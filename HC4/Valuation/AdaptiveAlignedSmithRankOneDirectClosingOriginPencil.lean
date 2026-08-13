import HC4.Valuation.AdaptiveAlignedSmithAxisPreservingQuadraticNormalization
import HC4.Valuation.AdaptiveRigidMatrixExposure
import Mathlib.Tactic

/-!
# The honest origin pencil at direct rank-one closing

This file isolates the finite-dimensional object carried by the remaining
`j = Delta` branch.

For the honest closing family `P(tau)`, put

* `H_n = Hess(P_n)(0)`, the source-origin Hessian of the `n`th parameter
  layer;
* `j = firstActualLayerOrder`.

At direct closing (`j = Delta`) we prove, without any JC2 input:

* `j > 0`;
* `H_n = 0` for every `0 < n < j`;
* `H_j != 0`;
* `det H_0 = 0`;
* the coefficient of `tau^j` in the honest determinant clock is exactly `1`.

Thus all of the remaining equality problem is concentrated in a literal
four-by-four matrix pencil with singular constant term and a nontrivial first
layer.  The next step is purely finite-dimensional: identify the first
nonzero determinant coefficient with the adjugate contraction and extract
the fresh kernel-square direction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Source-origin Hessian of the `n`th honest parameter layer. -/
noncomputable def sourceOriginHessianLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) : Matrix (Fin 4) (Fin 4) K :=
  quadraticFamilyHessianMatrix (familyParameterLayer P n)

/-- The origin Hessian layer is exactly the corresponding coefficient of the
polynomial-valued origin Hessian. -/
theorem sourceOriginHessianLayer_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i k : Fin 4) :
    sourceOriginHessianLayer P n i k =
      (quadraticFamilyHessianMatrix P i k).coeff n := by
  symm
  exact quadraticFamilyHessianMatrix_coeff_familyParameterLayer P n i k

/-- The exact zero parameter layer is the ordinary special fibre. -/
theorem familyParameterLayer_zero_eq_polynomialFamilySpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterLayer P 0 = polynomialFamilySpecialFiber P := by
  apply MvPolynomial.ext
  intro d
  rw [familyParameterLayer_coeff, coeff_polynomialFamilySpecialFiber]
  rfl

/-- The constant origin layer is literally the source-origin Hessian of the
special-fibre polynomial.  This formulation avoids asking Lean to elaborate a
large `mapMatrix`/`map_det` equality. -/
theorem sourceOriginHessianLayer_zero_eq_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    sourceOriginHessianLayer P 0 =
      quadraticFamilyHessianMatrix (polynomialFamilySpecialFiber P) := by
  unfold sourceOriginHessianLayer
  rw [familyParameterLayer_zero_eq_polynomialFamilySpecialFiber]

/-- Constant source-origin Hessian determinant is the source-constant
coefficient of the Hessian determinant of the special fibre. -/
theorem sourceOriginHessianLayer_zero_det
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (sourceOriginHessianLayer P 0).det =
      MvPolynomial.constantCoeff
        (HC4.Polynomial.hessianDeterminant (polynomialFamilySpecialFiber P)) := by
  rw [sourceOriginHessianLayer_zero_eq_specialFiber]
  exact quadraticFamilyHessianMatrix_det (polynomialFamilySpecialFiber P)

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The direct-closing order is positive. -/
theorem directClosing_firstActualLayerOrder_pos
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    0 < C.firstActualLayerOrder := by
  exact C.firstActualLayerOrder_pos

/-- Every positive source-origin Hessian layer below the honest first actual
layer vanishes. -/
theorem sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hnpos : 0 < n)
    (hnlt : n < C.firstActualLayerOrder) :
    sourceOriginHessianLayer C.family n = 0 := by
  apply Matrix.ext
  intro i k
  rw [sourceOriginHessianLayer_apply]
  rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
  have hzero := familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    C.family C.hasPositiveActualParameterLayer hnpos
      (by simpa [firstActualLayerOrder] using hnlt)
  rw [hzero]
  simp [quadraticFamilyHessianMatrix]

/-- At direct closing, the first origin Hessian layer is genuinely nonzero. -/
theorem directClosing_sourceOriginHessianLayer_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    sourceOriginHessianLayer C.family C.firstActualLayerOrder ≠ 0 := by
  simpa [sourceOriginHessianLayer] using
    C.firstActualLayer_originHessian_ne_zero_of_eq_defect heq

/-- The honest polynomial-valued source-origin Hessian has determinant exactly
`X^Delta`. -/
theorem family_originHessian_det_eq_X_pow
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (quadraticFamilyHessianMatrix C.family).det =
      (Polynomial.X : Polynomial K) ^ B.aligned.endpoint.defect := by
  rw [quadraticFamilyHessianMatrix_det]
  rw [C.family_hessianDefect]
  simp

/-- Its determinant coefficient at the closing order is exactly one. -/
theorem family_originHessian_det_coeff_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    ((quadraticFamilyHessianMatrix C.family).det).coeff
        B.aligned.endpoint.defect = 1 := by
  rw [C.family_originHessian_det_eq_X_pow]
  rw [Polynomial.coeff_X_pow]
  simp

/-- Equivalently, in the direct-closing timing branch the determinant
coefficient at the first actual source order is exactly one. -/
theorem directClosing_family_originHessian_det_coeff_firstActual
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    ((quadraticFamilyHessianMatrix C.family).det).coeff
        C.firstActualLayerOrder = 1 := by
  simpa [heq] using C.family_originHessian_det_coeff_defect

/-- The constant source-origin Hessian is singular.  This is forced directly
by the positive pure determinant clock. -/
theorem sourceOriginSpecialHessian_det_eq_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (sourceOriginHessianLayer C.family 0).det = 0 := by
  rw [sourceOriginHessianLayer_zero_det]
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  rw [C.family_hessianDefect]
  have hDelta : 0 < B.aligned.endpoint.defect := C.defect_pos
  simp [hDelta.ne']

/-- A compact certificate for the exact finite-dimensional origin pencil
carried by the direct-closing equality branch. -/
structure DirectClosingOriginPencilCertificate
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop where
  order_pos : 0 < C.firstActualLayerOrder
  intermediate_zero :
    ∀ n : ℕ,
      0 < n →
      n < C.firstActualLayerOrder →
      sourceOriginHessianLayer C.family n = 0
  firstLayer_ne_zero :
    sourceOriginHessianLayer C.family C.firstActualLayerOrder ≠ 0
  special_det_zero :
    (sourceOriginHessianLayer C.family 0).det = 0
  determinant_firstCoeff_one :
    ((quadraticFamilyHessianMatrix C.family).det).coeff
      C.firstActualLayerOrder = 1

/-- Direct closing canonically supplies the origin-pencil certificate. -/
theorem directClosing_originPencilCertificate
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    DirectClosingOriginPencilCertificate C := by
  refine
    { order_pos := C.directClosing_firstActualLayerOrder_pos
      intermediate_zero := ?_
      firstLayer_ne_zero := C.directClosing_sourceOriginHessianLayer_ne_zero heq
      special_det_zero := C.sourceOriginSpecialHessian_det_eq_zero
      determinant_firstCoeff_one :=
        C.directClosing_family_originHessian_det_coeff_firstActual heq }
  intro n hnpos hnlt
  exact C.sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual hnpos hnlt

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
