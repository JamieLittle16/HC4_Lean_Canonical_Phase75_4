#!/usr/bin/env bash
set -euo pipefail

echo "=== HC4/Valuation/LinearCovariance.lean: declarations and relevant lines ==="
if [[ -f HC4/Valuation/LinearCovariance.lean ]]; then
  rg -n -C 2 \
    '(^|[[:space:]])(theorem|lemma|def|noncomputable def|structure)[[:space:]]|hessian|Hessian|determinant|Determinant|gradient|Gradient|covarian|linear|Linear' \
    HC4/Valuation/LinearCovariance.lean || true
else
  echo "ERROR: HC4/Valuation/LinearCovariance.lean not found"
  exit 1
fi

echo
echo "=== Existing elementary-shear Hessian/determinant declarations anywhere in HC4 ==="
rg -n -C 2 \
  'elementaryShear.*(hessian|Hessian|det|Defect)|((hessian|Hessian|det|Defect).*)elementaryShear|linear.*(hessian|Hessian|determinant|Defect)|(hessian|Hessian|determinant|Defect).*linear' \
  HC4 --glob '*.lean' || true

echo
echo "=== Exact defect interface declarations ==="
rg -n -C 2 \
  'HasPolynomialFamilyHessianDefect|polynomialFamilyHessianDeterminant' \
  HC4/Valuation HC4/Polynomial --glob '*.lean' | head -n 240 || true
