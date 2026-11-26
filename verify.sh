#!/usr/bin/env bash
set -euo pipefail

printf '%s\n' 'Using the existing pinned dependency lock (no lake update).'

printf '%s\n' 'Downloading the matching Mathlib cache...'
lake exe cache get

printf '%s\n' 'Building the complete HC4 library...'
lake build

printf '%s\n' 'Printing theorem axioms...'
lake env lean HC4/Audit.lean | tee axioms.log

printf '%s\n' 'Checking the external mathematical statement and logical dependencies...'
lake env lean HC4/StatementAudit.lean | tee statement-audit.log

printf '%s\n' 'Checking the polynomial inverse and full equivalence...'
lake build HC4.FinalEquivalence
lake env lean HC4/PolynomialInverseAudit.lean | tee polynomial-inverse-audit.log
lake env lean HC4/RationalInverseAudit.lean | tee rational-inverse-audit.log
lake env lean HC4/FinalEquivalence.lean | tee final-equivalence.log

printf '%s\n' 'Checking the deliberately false negative control...'
if lake env lean NegativeControl.lean > negative-control.log 2>&1; then
  echo "ERROR: Lean accepted the deliberately false negative control." >&2
  exit 1
fi
printf '%s\n' 'Negative control rejected as expected.'

printf '%s\n' 'Scanning project sources for potentially suspicious tokens (including comments)...'
# This textual scan is advisory: it also matches documentation and is not a Lean parser.
# The enforced transitive axiom whitelists in the audit modules are the decisive checks.
if grep -RInE --include='*.lean' '\b(sorry|admit|axiom|unsafe)\b' HC4 > source-scan.log; then
  printf '%s\n' 'Review source-scan.log for matches; comments can produce false positives.'
else
  status=$?
  if [ "$status" -ne 1 ]; then exit "$status"; fi
  printf '%s\n' 'No matching tokens found.'
fi

printf '%s\n' 'Verification completed successfully.'
