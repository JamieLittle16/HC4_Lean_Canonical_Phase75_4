#!/usr/bin/env bash
set -euo pipefail

echo "== HC4 Phase 88.3 targeted verification =="

lake build HC4.RationalRigidity.ClearedInfinityEvaluation
lake build HC4.RationalRigidity.RankThreeInfinityAssembly
lake build HC4.RationalRigidity
lake build HC4

echo
echo "Phase 88.3 targeted dependency chain is green."
echo "Now run: ./verify.sh"
