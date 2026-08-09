#!/usr/bin/env bash
set -euo pipefail

printf '%s\n' 'Updating the pinned dependency lock...'
lake update

printf '%s\n' 'Downloading the matching Mathlib cache...'
lake exe cache get

printf '%s\n' 'Building the complete HC4 library...'
lake build

printf '%s\n' 'Printing theorem axioms...'
lake env lean HC4/Audit.lean | tee axioms.log

printf '%s\n' 'Checking the deliberately false negative control...'
if lake env lean NegativeControl.lean > negative-control.log 2>&1; then
  echo "ERROR: Lean accepted the deliberately false negative control." >&2
  exit 1
fi
printf '%s\n' 'Negative control rejected as expected.'

printf '%s\n' 'Scanning project proofs for escape hatches...'
if grep -RInE --include='*.lean' '\b(sorry|admit|axiom|unsafe)\b' HC4; then
  echo "ERROR: forbidden proof escape found in HC4 sources." >&2
  exit 1
fi
printf '%s\n' 'No sorry/admit/axiom/unsafe tokens found in HC4 sources.'

printf '%s\n' 'Verification completed successfully.'
