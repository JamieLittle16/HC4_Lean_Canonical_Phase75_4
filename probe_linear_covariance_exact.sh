#!/usr/bin/env bash
set -euo pipefail

echo "=== exact Hessian/determinant declarations in LinearCovariance ==="
rg -n \
  '^(noncomputable )?(def|theorem|lemma|structure) .*([Hh]essian|determinant|Determinant|Covariance|covariance)' \
  HC4/Valuation/LinearCovariance.lean || true

echo
echo "=== lines 1-180 of LinearCovariance ==="
sed -n '1,180p' HC4/Valuation/LinearCovariance.lean
