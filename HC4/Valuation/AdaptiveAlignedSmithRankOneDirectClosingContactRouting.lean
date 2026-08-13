import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingQuadraticSupport
import HC4.Valuation.AdaptiveAlignedSmithClosingFirstContactLattice
import Mathlib.Tactic

/-!
# Routing the direct rank-one closing equality case

The green first-actual-layer analysis has now reached the honest dichotomy

    j < Delta

or

    j = Delta.

At equality the first actual source layer contains genuine quadratic
curvature.  The support analysis also showed that a whole-family diagonal
first-contact exposure can see an actual layer only when its selected
coefficient has exact X-adic order equal to that layer.

This file makes the resulting routing precise.

* Any layer-sensitive whole-family first-contact certificate canonically
  upgrades to the older exact-order first-contact lattice.  Thus once a
  supporting lattice has genuinely selected a fresh first layer, all of the
  already-green polynomial first-contact / marked-collision machinery becomes
  available immediately.
* In the overlap branch, where the entire first actual layer is already
  supported on the old special fibre, no whole-family first-contact lattice
  can select that layer.  The correct object is necessarily the relative
  deformation `P = P_0 + X^j Q`.
* At direct closing `j = Delta`, that overlap relative deformation has a
  nonzero source-origin Hessian.  Hence it is not an affine/invisible tail:
  it is a genuine quadratic deformation supported entirely on the old source
  support.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Layer-sensitive contact upgrades to exact-order first contact -/

namespace AdaptiveAlignedSmithLayerSensitiveFirstContactData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- A corrected layer-sensitive contact is automatically an honest
exact-order first-contact lattice: the previous support theorem proved that
its selected actual layer equals the exact X-adic order of the selected
source coefficient. -/
noncomputable def toExactFirstContactLattice
    (L : AdaptiveAlignedSmithLayerSensitiveFirstContactData B source) :
    AdaptiveAlignedSmithClosingFirstContactLatticeData B source where
  weight := L.weight
  commonLevel := L.commonLevel
  R := L.R
  R_pos := L.R_pos
  familyIntegrality := L.familyIntegrality
  rightSectionIntegrality := L.rightSectionIntegrality
  determinantExponentNonnegative := L.determinantExponentNonnegative
  contactExponent := L.contactExponent
  contactSupport := L.contactSupport
  contactOrderPositive := by
    simpa [L.contactOrder_eq_parameterOrder] using L.contactOrderPositive
  contactLevel := by
    simpa [L.contactOrder_eq_parameterOrder] using L.contactLevel

/-- Consequently the selected positive layer is genuinely visible on the
special fibre of the exposed first-contact family. -/
theorem contactCoefficient_specialFiber_ne_zero
    (L : AdaptiveAlignedSmithLayerSensitiveFirstContactData B source) :
    MvPolynomial.coeff L.contactExponent
        (polynomialFamilySpecialFiber L.toExactFirstContactLattice.family) ≠ 0 := by
  exact L.toExactFirstContactLattice.contactCoefficient_specialFiber_ne_zero

end AdaptiveAlignedSmithLayerSensitiveFirstContactData

/-! ## The overlap branch cannot be a whole-family first contact -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- If every monomial in the first actual layer was already present in the
old special fibre, no whole-family diagonal first-contact certificate can
select that actual layer.  Such a certificate would force fresh support by
the already-green exact-order theorem. -/
theorem no_firstActualLayer_wholeFamilyContact_of_overlap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hoverlap : C.FirstActualLayerSupportContainedInSpecialFiber) :
    ¬ ∃ L : AdaptiveAlignedSmithRankOneClosingLayerSensitiveFirstContactData C,
        L.contactOrder = C.firstActualLayerOrder := by
  rintro ⟨L, hcontact⟩
  have hfresh := C.firstActualLayerContact_hasFreshSupport L hcontact
  rcases hfresh with ⟨d, hdLayer, hdFresh⟩
  exact hdFresh (hoverlap hdLayer)

/-- At direct closing, if the complete first actual layer overlaps the old
special fibre, then the honest relative deformation has a nonzero
source-origin Hessian.  Thus the overlap branch is a genuinely quadratic
relative deformation, not an affine or Hessian-invisible perturbation. -/
theorem overlapRelativeFirstDeformation_originHessian_ne_zero_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (_hoverlap : C.FirstActualLayerSupportContainedInSpecialFiber) :
    quadraticFamilyHessianMatrix
        (polynomialFamilySpecialFiber
          C.relativeFirstActualDeformationFamily) ≠ 0 := by
  have hH := C.firstActualLayer_originHessian_ne_zero_of_eq_defect heq
  rw [← C.relativeFirstActualDeformation_specialFiber] at hH
  exact hH

/-- **Direct-closing extraction frontier.**

If `j = Delta`, then either the first actual layer contains genuinely fresh
support (the only case eligible for an honest whole-family first-contact
exposure at order `j`), or the entire layer overlaps the old special fibre.
In the latter case its relative quotient simultaneously

* stays supported on the old special fibre,
* has nonzero quadratic Hessian at the source origin, and
* cannot be selected at order `j` by any whole-family first-contact lattice.

This isolates the next no-JC2 problem exactly: kernel-align the quadratic
relative overlap deformation, or prove it gives strict restart progress. -/
theorem directClosing_fresh_or_quadraticRelativeOverlap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.FirstActualLayerHasFreshSupport ∨
      (C.FirstActualLayerSupportContainedInSpecialFiber ∧
        (polynomialFamilySpecialFiber
            C.relativeFirstActualDeformationFamily).support ⊆
          (polynomialFamilySpecialFiber C.family).support ∧
        quadraticFamilyHessianMatrix
            (polynomialFamilySpecialFiber
              C.relativeFirstActualDeformationFamily) ≠ 0 ∧
        ¬ ∃ L : AdaptiveAlignedSmithRankOneClosingLayerSensitiveFirstContactData C,
            L.contactOrder = C.firstActualLayerOrder) := by
  rcases C.firstActualLayer_fresh_or_overlap with hfresh | hoverlap
  · exact Or.inl hfresh
  · right
    refine ⟨hoverlap,
      C.relativeFirstActualDeformation_specialFiber_support_subset_of_overlap hoverlap,
      C.overlapRelativeFirstDeformation_originHessian_ne_zero_of_eq_defect heq hoverlap,
      C.no_firstActualLayer_wholeFamilyContact_of_overlap hoverlap⟩

/-- Complete timing/routing frontier after the direct-closing support audit. -/
theorem firstActualLayer_preclosing_or_freshDirect_or_quadraticRelativeOverlap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      C.FirstActualLayerHasFreshSupport) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      C.FirstActualLayerSupportContainedInSpecialFiber ∧
      quadraticFamilyHessianMatrix
          (polynomialFamilySpecialFiber
            C.relativeFirstActualDeformationFamily) ≠ 0) := by
  rcases C.firstActualLayer_preclosing_or_directQuadratic with hpre | hdirect
  · exact Or.inl hpre
  · rcases C.directClosing_fresh_or_quadraticRelativeOverlap hdirect.1 with
      hfresh | hoverlap
    · exact Or.inr (Or.inl ⟨hdirect.1, hfresh⟩)
    · exact Or.inr (Or.inr ⟨hdirect.1, hoverlap.1, hoverlap.2.2.1⟩)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
