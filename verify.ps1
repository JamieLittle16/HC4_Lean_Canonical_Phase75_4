$ErrorActionPreference = "Stop"

Write-Host "Updating the pinned dependency lock..."
lake update

Write-Host "Downloading the matching Mathlib cache..."
lake exe cache get

Write-Host "Building the complete HC4 library..."
lake build

Write-Host "Printing theorem axioms..."
lake env lean HC4/Audit.lean | Tee-Object -FilePath axioms.log

Write-Host "Checking the deliberately false negative control..."
lake env lean NegativeControl.lean *> negative-control.log
if ($LASTEXITCODE -eq 0) {
  throw "Lean accepted the deliberately false negative control."
}
Write-Host "Negative control rejected as expected."

Write-Host "Scanning project proofs for escape hatches..."
$bad = Get-ChildItem HC4 -Recurse -Filter *.lean | Select-String -Pattern '\b(sorry|admit|axiom|unsafe)\b'
if ($bad) {
  $bad | ForEach-Object { Write-Host $_ }
  throw "Forbidden proof escape found in HC4 sources."
}

Write-Host "Verification completed successfully."
