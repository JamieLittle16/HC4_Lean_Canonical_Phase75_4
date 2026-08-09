\
#!/usr/bin/env bash
set -euo pipefail

# HC4 Lean Phase 88.2
# Minimal guarded repair for the invalid RatFunc.IntermediateField import.
#
# Run from the canonical HC4 Lean project root after overlaying this patch.

TARGET="HC4/RationalRigidity/ClearedInfinityEvaluation.lean"
BAD_IMPORT='import Mathlib.FieldTheory.RatFunc.IntermediateField'
GOOD_IMPORT='import Mathlib'

echo "HC4 Lean Phase 88.2 — guarded import repair"
echo "Target: $TARGET"
echo

if [[ ! -f "$TARGET" ]]; then
  echo "ERROR: $TARGET does not exist."
  echo "Run this script from the root of HC4_Lean_Canonical_Phase75_2."
  exit 2
fi

bad_count="$(grep -Fxc "$BAD_IMPORT" "$TARGET" || true)"
good_count="$(grep -Fxc "$GOOD_IMPORT" "$TARGET" || true)"

if [[ "$bad_count" == "1" ]]; then
  backup="${TARGET}.phase88_1.before_import_fix"
  cp -p "$TARGET" "$backup"

  python3 - "$TARGET" "$BAD_IMPORT" "$GOOD_IMPORT" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
bad = sys.argv[2]
good = sys.argv[3]

text = path.read_text()
count = text.count(bad)
if count != 1:
    raise SystemExit(
        f"ERROR: expected exactly one occurrence of the invalid import; found {count}"
    )

path.write_text(text.replace(bad, good, 1))
PY

  echo "Applied:"
  echo "  - $BAD_IMPORT"
  echo "  + $GOOD_IMPORT"
  echo "Backup:"
  echo "  $backup"

elif [[ "$bad_count" == "0" && "$good_count" -ge "1" ]]; then
  echo "Import repair is already present; no source change required."
else
  echo "ERROR: Refusing to modify an unexpected source state."
  echo
  echo "Expected exactly this invalid import:"
  echo "  $BAD_IMPORT"
  echo
  echo "Current import lines in $TARGET:"
  grep '^import ' "$TARGET" || true
  echo
  echo "No Lean source was modified."
  exit 3
fi

echo
echo "Checking that the invalid import is gone..."
if grep -Fq "$BAD_IMPORT" "$TARGET"; then
  echo "ERROR: invalid import still present after patch."
  exit 4
fi

echo
echo "Building the directly affected target..."
lake build HC4.RationalRigidity.ClearedInfinityEvaluation

echo
echo "Building downstream targets..."
lake build HC4.RationalRigidity.RankThreeInfinityAssembly
lake build HC4.RationalRigidity
lake build HC4

echo
echo "Phase 88.2 targeted dependency chain is green."
echo "Now run:"
echo "  ./verify.sh"
