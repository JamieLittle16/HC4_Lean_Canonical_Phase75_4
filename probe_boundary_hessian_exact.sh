#!/usr/bin/env bash
set -euo pipefail

echo "=== Existing shear Hessian/determinant declarations in HC4 ==="
rg -n -C 2 \
  '^(noncomputable )?(def|theorem|lemma).*elementaryShear.*(Hessian|hessian|det|Det|Matrix)|^(noncomputable )?(def|theorem|lemma).*(Hessian|hessian|det|Det).*elementaryShear' \
  HC4 --glob '*.lean' || true

echo
echo "=== Elementary shear matrix definitions/usages ==="
rg -n -C 3 \
  'elementaryShear(Matrix|TransposeMatrix)|transvection' \
  HC4/Valuation --glob '*.lean' | head -n 260 || true

echo
echo "=== Matrix determinant/transvection API in pinned mathlib ==="
rg -n -C 2 \
  'theorem .*transvection|lemma .*transvection|det_.*transvection|transvection_.*det|det.*updateRow|det.*updateColumn|det.*addRow|det.*addColumn|updateRow.*det|updateColumn.*det' \
  .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix \
  --glob '*.lean' | head -n 300 || true

echo
echo "=== Exact polynomial-family defect definition ==="
rg -n -C 8 \
  'def HasPolynomialFamilyHessianDefect|abbrev HasPolynomialFamilyHessianDefect|theorem quadraticFamilyHessianMatrix_det|def polynomialFamilyHessianDeterminant' \
  HC4 --glob '*.lean' | head -n 180 || true
