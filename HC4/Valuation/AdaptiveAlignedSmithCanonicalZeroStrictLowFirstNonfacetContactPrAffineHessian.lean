import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineCarrier
import Mathlib.Tactic

/-!
# The actual PR contact Hessian has a zero leading block

The first-exposure support bound gives three vanishing second derivatives on
the entire contact carrier.  Its determinant is therefore the square of the
mixed `(0,1)` versus `(2,3)` determinant.  Singularity kills this mixed
determinant on that same carrier.

The nonzero principal `(2,3)` pivot is a different minor.  These facts do not
contradict one another and do not assert terminal impossibility.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The complete `(0,1)` Hessian block vanishes on the contact carrier. -/
theorem pr_contact_pair_hessian_eq_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i j : Fin 4) (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    HC4.Polynomial.hessian C.face i j = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [hessian_apply, coeff_pderiv_backport, coeff_pderiv_backport,
    MvPolynomial.coeff_zero]
  have hc : MvPolynomial.coeff
      (d + Finsupp.single j 1 + Finsupp.single i 1) C.face = 0 := by
    by_contra hne
    have hs := C.pr_contact_support_pair_le_one hthree houtThree
      (MvPolynomial.mem_support_iff.mpr hne)
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp at hs <;> omega
  rw [hc, zero_mul, zero_mul]

/-- The mixed determinant is zero on the actual contact face.  No minor is
transported to another carrier in this statement. -/
theorem pr_contact_mixedDet_eq_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessian C.face 0 2 * HC4.Polynomial.hessian C.face 1 3 -
      HC4.Polynomial.hessian C.face 0 3 * HC4.Polynomial.hessian C.face 1 2 = 0 := by
  let H := HC4.Polynomial.hessian C.face
  have h00 : H 0 0 = 0 := C.pr_contact_pair_hessian_eq_zero hthree houtThree 0 0
    (Or.inl rfl) (Or.inl rfl)
  have h01 : H 0 1 = 0 := C.pr_contact_pair_hessian_eq_zero hthree houtThree 0 1
    (Or.inl rfl) (Or.inr rfl)
  have h10 : H 1 0 = 0 := C.pr_contact_pair_hessian_eq_zero hthree houtThree 1 0
    (Or.inr rfl) (Or.inl rfl)
  have h11 : H 1 1 = 0 := C.pr_contact_pair_hessian_eq_zero hthree houtThree 1 1
    (Or.inr rfl) (Or.inr rfl)
  have h20 : H 2 0 = H 0 2 := pderiv_comm_backport 0 2 C.face
  have h21 : H 2 1 = H 1 2 := pderiv_comm_backport 1 2 C.face
  have h30 : H 3 0 = H 0 3 := pderiv_comm_backport 0 3 C.face
  have h31 : H 3 1 = H 1 3 := pderiv_comm_backport 1 3 C.face
  have hdet : H.det = (H 0 2 * H 1 3 - H 0 3 * H 1 2)^2 := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four]
    simp [Matrix.det_fin_three, Fin.succAbove, h00, h01, h10, h11,
      h20, h21, h30, h31]
    ring
  have hz : H.det = 0 := C.hessian_zero
  rw [hdet] at hz
  exact (pow_eq_zero hz)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
