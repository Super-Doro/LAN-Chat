$ErrorActionPreference = 'Stop'

$projectRoot = $PSScriptRoot
$requiredMajor = 26
$nodePath = $null

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
  $toolsDir = Join-Path $projectRoot '.build-tools'
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

Write-Host ''
Write-Host 'Done. End users only need dist\VOID-Chat.exe and do not need Node.js.'
