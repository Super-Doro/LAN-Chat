param(
  [switch]$SkipCompression
)

$ErrorActionPreference = 'Stop'

$projectRoot = $PSScriptRoot
$requiredMajor = 26
$nodePath = $null
$toolsDir = Join-Path $projectRoot '.build-tools'
$outputName = if ($env:LAN_CHAT_EXE_NAME) { $env:LAN_CHAT_EXE_NAME } else { 'LAN CHAT.exe' }
if ($outputName -notmatch '^[A-Za-z0-9][A-Za-z0-9 ._-]*\.exe$') {
  throw 'LAN_CHAT_EXE_NAME must be a safe .exe file name.'
}
$buildDir = Join-Path $projectRoot 'build'
$distDir = Join-Path $projectRoot 'dist'
$outputBaseName = [System.IO.Path]::GetFileNameWithoutExtension($outputName)
$rawOutputPath = Join-Path $buildDir ($outputBaseName + '.raw.exe')
$outputPath = Join-Path $distDir $outputName

function Write-BuildProgress {
  param(
    [ValidateRange(0,100)][int]$Percent,
    [string]$Message
  )
  Write-Host ("[{0,3}%] {1}" -f $Percent, $Message)
}

Write-BuildProgress 0 'Build started.'

$nvmRoot = 'D:\NVM Desktop\files'
if (Test-Path -LiteralPath $nvmRoot) {
  $nodePath = Get-ChildItem -LiteralPath $nvmRoot -Directory |
    Where-Object { $_.Name -match '^\d+\.\d+\.\d+$' -and [int]($_.Name.Split('.')[0]) -ge $requiredMajor } |
    Sort-Object { [version]$_.Name } -Descending |
    ForEach-Object { Join-Path $_.FullName 'node.exe' } |
    Where-Object { Test-Path -LiteralPath $_ } |
    Select-Object -First 1
}

if (-not $nodePath) {
  $command = Get-Command node -ErrorAction SilentlyContinue
  if ($command) {
    $major = [int]((& $command.Source --version).TrimStart('v').Split('.')[0])
    if ($major -ge $requiredMajor) { $nodePath = $command.Source }
  }
}

if (-not $nodePath) {
  $nodeVersion = '26.0.0'
  $archive = Join-Path $toolsDir "node-v$nodeVersion-win-x64.zip"
  $portableDir = Join-Path $toolsDir "node-v$nodeVersion-win-x64"
  $nodePath = Join-Path $portableDir 'node.exe'

  New-Item -ItemType Directory -Path $toolsDir -Force | Out-Null
  if (-not (Test-Path -LiteralPath $archive)) {
    Write-Host "Downloading portable Node.js v$nodeVersion for the build..."
    Invoke-WebRequest -Uri "https://nodejs.org/dist/v$nodeVersion/node-v$nodeVersion-win-x64.zip" -OutFile $archive
  }
  if (-not (Test-Path -LiteralPath $nodePath)) {
    Expand-Archive -LiteralPath $archive -DestinationPath $toolsDir -Force
  }
}

Write-BuildProgress 10 "Using Node.js runtime: $nodePath"
Write-Host 'Preparing SEA build...'
& $nodePath (Join-Path $projectRoot 'tools\build-exe.js')
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
if (-not (Test-Path -LiteralPath $rawOutputPath)) {
  throw "Raw SEA output was not generated: $rawOutputPath"
}
Write-Host ("Raw SEA size: {0:N1} MB" -f ((Get-Item -LiteralPath $rawOutputPath).Length / 1MB))
Write-BuildProgress 35 'SEA executable generated.'

New-Item -ItemType Directory -Path $distDir -Force | Out-Null

if (-not $SkipCompression) {
  $upxVersion = '5.2.0'
  $upxArchive = Join-Path $toolsDir "upx-$upxVersion-win64.zip"
  $upxDirectory = Join-Path $toolsDir "upx-$upxVersion-win64"
  $upxPath = Join-Path $upxDirectory 'upx.exe'
  $upxUrl = "https://github.com/upx/upx/releases/download/v$upxVersion/upx-$upxVersion-win64.zip"
  $upxSha256 = 'B471EBF1B7F20F4A89150264ED9A008A2A5BFD247F3C6D1184A75BB59CA08F5D'

  Write-BuildProgress 45 "Checking UPX v$upxVersion"
  New-Item -ItemType Directory -Path $toolsDir -Force | Out-Null
  if (-not (Test-Path -LiteralPath $upxArchive)) {
    Write-Host "Downloading UPX v$upxVersion..."
    Invoke-WebRequest -Uri $upxUrl -OutFile $upxArchive
  }

  Write-Host 'Verifying UPX archive SHA-256...'
  $actualHash = (Get-FileHash -LiteralPath $upxArchive -Algorithm SHA256).Hash
  if ($actualHash -ne $upxSha256) {
    throw "UPX archive SHA-256 mismatch. Expected $upxSha256, received $actualHash."
  }

  if (-not (Test-Path -LiteralPath $upxPath)) {
    Expand-Archive -LiteralPath $upxArchive -DestinationPath $toolsDir -Force
  }
  if (-not (Test-Path -LiteralPath $upxPath)) {
    throw "UPX executable was not found after extraction: $upxPath"
  }

  Write-BuildProgress 55 'Compressing with UPX; waiting for UPX to finish...'
  $sizeBefore = (Get-Item -LiteralPath $rawOutputPath).Length
  $compressedPath = Join-Path $buildDir ($outputBaseName + '.compressed.exe')
  if (Test-Path -LiteralPath $compressedPath) {
    Remove-Item -LiteralPath $compressedPath -Force
  }
  Copy-Item -LiteralPath $rawOutputPath -Destination $compressedPath
  $compressionStarted = Get-Date
  try {
    & $upxPath --best --lzma $compressedPath
    if ($LASTEXITCODE -ne 0) { throw "UPX compression failed with exit code $LASTEXITCODE." }
    Write-BuildProgress 80 'UPX compression completed.'
    Write-BuildProgress 90 'Testing compressed executable integrity...'
    & $upxPath -t $compressedPath
    if ($LASTEXITCODE -ne 0) { throw "UPX integrity test failed with exit code $LASTEXITCODE." }
    Write-Host ("Compression elapsed: {0:N1} seconds" -f ((Get-Date) - $compressionStarted).TotalSeconds)
    Write-BuildProgress 95 'Copying final executable...'
    Copy-Item -LiteralPath $compressedPath -Destination $outputPath -Force
  } finally {
    if (Test-Path -LiteralPath $compressedPath) {
      Remove-Item -LiteralPath $compressedPath -Force
    }
  }

  $sizeAfter = (Get-Item -LiteralPath $outputPath).Length
  $savedPercent = [math]::Round((1 - ($sizeAfter / $sizeBefore)) * 100, 1)
  Write-Host ("Final size: {0:N1} MB (reduced by {1}%)" -f ($sizeAfter / 1MB), $savedPercent)
} else {
  Write-BuildProgress 90 'Copying uncompressed executable...'
  Copy-Item -LiteralPath $rawOutputPath -Destination $outputPath -Force
  $sizeAfter = (Get-Item -LiteralPath $outputPath).Length
  Write-Host ("Final size: {0:N1} MB (compression skipped)" -f ($sizeAfter / 1MB))
}

if (Test-Path -LiteralPath $rawOutputPath) {
  Write-BuildProgress 98 'Cleaning temporary build files...'
  Remove-Item -LiteralPath $rawOutputPath -Force
}

Write-BuildProgress 100 'Build completed.'
Write-Host ''
Write-Host 'Done. End users only need dist\LAN CHAT.exe and do not need Node.js.'
