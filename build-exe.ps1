param(
  [switch]$SkipCompression
)

$ErrorActionPreference = 'Stop'

$projectRoot = $PSScriptRoot
$requiredMajor = 26
$nodePath = $null
$toolsDir = Join-Path $projectRoot '.build-tools'
$outputName = if ($env:VOID_CHAT_EXE_NAME) { $env:VOID_CHAT_EXE_NAME } else { 'VOID-Chat.exe' }
if ($outputName -notmatch '^[A-Za-z0-9._-]+\.exe$') {
  throw 'VOID_CHAT_EXE_NAME must be a safe .exe file name.'
}

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

Write-Host "Build runtime: $nodePath"
& $nodePath (Join-Path $projectRoot 'tools\build-exe.js')
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

if (-not $SkipCompression) {
  $upxVersion = '5.2.0'
  $upxArchive = Join-Path $toolsDir "upx-$upxVersion-win64.zip"
  $upxDirectory = Join-Path $toolsDir "upx-$upxVersion-win64"
  $upxPath = Join-Path $upxDirectory 'upx.exe'
  $upxUrl = "https://github.com/upx/upx/releases/download/v$upxVersion/upx-$upxVersion-win64.zip"
  $upxSha256 = 'B471EBF1B7F20F4A89150264ED9A008A2A5BFD247F3C6D1184A75BB59CA08F5D'

  New-Item -ItemType Directory -Path $toolsDir -Force | Out-Null
  if (-not (Test-Path -LiteralPath $upxArchive)) {
    Write-Host "Downloading UPX v$upxVersion for executable compression..."
    Invoke-WebRequest -Uri $upxUrl -OutFile $upxArchive
  }

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

  $outputPath = Join-Path (Join-Path $projectRoot 'dist') $outputName
  $sizeBefore = (Get-Item -LiteralPath $outputPath).Length
  $compressedName = ([System.IO.Path]::GetFileNameWithoutExtension($outputName)) + '.compressed.exe'
  $compressedPath = Join-Path (Join-Path $projectRoot 'build') $compressedName
  Copy-Item -LiteralPath $outputPath -Destination $compressedPath -Force
  Write-Host "Compressing executable with UPX v$upxVersion..."
  try {
    & $upxPath --best --lzma --no-progress $compressedPath
    if ($LASTEXITCODE -ne 0) { throw "UPX compression failed with exit code $LASTEXITCODE." }
    & $upxPath -t $compressedPath
    if ($LASTEXITCODE -ne 0) { throw "UPX integrity test failed with exit code $LASTEXITCODE." }
    Copy-Item -LiteralPath $compressedPath -Destination $outputPath -Force
  } finally {
    if (Test-Path -LiteralPath $compressedPath) {
      Remove-Item -LiteralPath $compressedPath -Force
    }
  }

  $sizeAfter = (Get-Item -LiteralPath $outputPath).Length
  $savedPercent = [math]::Round((1 - ($sizeAfter / $sizeBefore)) * 100, 1)
  Write-Host ("Final size: {0:N1} MB (reduced by {1}%)" -f ($sizeAfter / 1MB), $savedPercent)
}

Write-Host ''
Write-Host 'Done. End users only need dist\VOID-Chat.exe and do not need Node.js.'
