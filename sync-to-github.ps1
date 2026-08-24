$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$gitExe = "C:\Users\glide\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe"
$gitExecPath = "C:\Users\glide\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\mingw64\libexec\git-core"
$gitBinPath = "C:\Users\glide\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\mingw64\bin"
$logPath = Join-Path $repoRoot ".auto-sync.log"
$trackedFiles = @("index.html", "README.txt")
$mutex = New-Object System.Threading.Mutex($false, "Local\RookSolitaireGitSync")

if (-not $mutex.WaitOne(0)) {
  exit 0
}

$env:GIT_EXEC_PATH = $gitExecPath
$env:Path = "$gitBinPath;$env:Path"

function Write-SyncLog([string]$message) {
  $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
  Add-Content -LiteralPath $logPath -Value "[$timestamp] $message"
}

try {
  Write-SyncLog "Watcher started."
  $lastState = ""
  $stableSince = Get-Date

  while ($true) {
    $state = (& $gitExe -C $repoRoot status --porcelain -- @trackedFiles) -join "`n"

    if ($state -ne $lastState) {
      $lastState = $state
      $stableSince = Get-Date
    }

    if ($state -and ((Get-Date) - $stableSince).TotalSeconds -ge 5) {
      try {
        & $gitExe -C $repoRoot add -- @trackedFiles
        & $gitExe -C $repoRoot diff --cached --quiet
        if ($LASTEXITCODE -ne 0) {
          $message = "Auto-sync Rook Solitaire " + (Get-Date -Format "yyyy-MM-dd HH:mm:ss")
          & $gitExe -C $repoRoot commit -m $message
          & $gitExe -C $repoRoot push origin main
          if ($LASTEXITCODE -eq 0) {
            Write-SyncLog "Uploaded changes to GitHub."
          } else {
            Write-SyncLog "Push failed; the local commit was preserved for retry."
          }
        }
      } catch {
        Write-SyncLog ("Sync error: " + $_.Exception.Message)
      }

      $lastState = ""
      $stableSince = Get-Date
    }

    Start-Sleep -Seconds 3
  }
} finally {
  Write-SyncLog "Watcher stopped."
  $mutex.ReleaseMutex()
  $mutex.Dispose()
}

