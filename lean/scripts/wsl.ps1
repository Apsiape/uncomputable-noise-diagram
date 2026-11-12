<#
Windows-side driver (PowerShell 5.1). Source of truth: this repository on Windows.

  powershell -File scripts/wsl.ps1 sync                 # mirror sources into the WSL build folder
  powershell -File scripts/wsl.ps1 build [MOD ...]      # sync, then serial capped build in WSL
  powershell -File scripts/wsl.ps1 check FILE           # sync, then elaborate one file (relative to project)
  powershell -File scripts/wsl.ps1 census               # sync, then the sorry census
  powershell -File scripts/wsl.ps1 audit                # sync, build, then print the axiom audit

The WSL build folder is /opt/uncomputable-noise-diagram-lean/project (distro `lean-comparator`;
/mnt/c is not mounted there, so files are copied through \\wsl.localhost). Every build also
checks the Windows host: it refuses below 8 GB free physical memory.
#>
param([Parameter(Position = 0)][string]$Cmd = 'build',
      [Parameter(Position = 1, ValueFromRemainingArguments = $true)][string[]]$Rest)
$ErrorActionPreference = 'Stop'
$Repo = Split-Path -Parent $PSScriptRoot
$Dest = '\\wsl.localhost\lean-comparator\opt\uncomputable-noise-diagram-lean\project'

function Sync {
  # Mirror the source tree; .git and build outputs are excluded (and never purged).
  robocopy $Repo $Dest /MIR /XD .git .lake /XF '*.olean' '*.ilean' /NFL /NDL /NJH /NJS /NP | Out-Null
  if ($LASTEXITCODE -ge 8) { throw "robocopy failed with exit code $LASTEXITCODE" }
}

function HostGuard {
  $free = (Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory * 1KB
  if ($free -lt 8GB) { throw ('REFUSE: Windows host has only {0:N1} GB free' -f ($free / 1GB)) }
}

function InWsl([string]$script) {
  # Pipe a script through stdin (UTF-8 without BOM; CRs stripped).
  $OutputEncoding = New-Object System.Text.UTF8Encoding $false
  $old = $ErrorActionPreference; $ErrorActionPreference = 'Continue'
  ("`n" + $script + "`n") | wsl.exe -d lean-comparator -- sh -c "tr -d '\r' | bash -s" 2>&1 |
    ForEach-Object { "$_" }
  $ErrorActionPreference = $old
}

Sync
$args2 = ($Rest | ForEach-Object { "'$_'" }) -join ' '
$cd = 'cd /opt/uncomputable-noise-diagram-lean/project'
switch ($Cmd) {
  'sync'   { 'synced' }
  'build'  { HostGuard; InWsl "$cd && python3 -I -B scripts/build.py $args2" }
  'check'  { HostGuard; InWsl "$cd && python3 -I -B scripts/build.py --check $args2" }
  'census' { InWsl "$cd && python3 -I -B scripts/sorry_census.py" }
  'audit'  { HostGuard; InWsl "$cd && bash scripts/audit.sh"
             Copy-Item (Join-Path $Dest 'AXIOMS.txt') (Join-Path $Repo 'AXIOMS.txt') -Force }
  'lint'   { InWsl "$cd && bash scripts/lint.sh" }
  default  { throw "unknown command $Cmd" }
}
