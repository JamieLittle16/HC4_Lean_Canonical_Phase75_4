import HC4.Newton.FirstSchurLayerLinearization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianRecognition
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyActiveConstant
import Mathlib.Tactic

/-!
# A19.R18: integral active-pivot cancellation for the profile Hessian

The final Schur adapter produces the binary profile-Hessian determinant only
through multiplication by the surviving active transverse pivot.  Division by
that pivot is unnecessary.  Its constant **family-parameter** coefficient is
nonzero, so ordinary parameter-polynomial convolution is triangular: once all
lower coefficients of the right factor have been killed, the next product
coefficient is exactly the constant pivot coefficient times the next right
coefficient.

This file isolates that cancellation once and attaches it to the three honest
cyclic contact pivots.  It reuses the generic convolution lemma from
`FirstSchurLayerLinearization`; no localization, inverse, or second cancellation
infrastructure is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u

/-- **R18 triangular constant-pivot cancellation.**  If the right factor has
vanished below `n`, a zero `n`th product coefficient and a nonzero constant
coefficient of the left factor force the `n`th right coefficient to vanish. -/
theorem polynomial_coeff_eq_zero_of_constant_pivot
    {R : Type u} [CommRing R] [IsDomain R]
    (A B : Polynomial R)
    {n : ℕ}
    (hA0 : A.coeff 0 ≠ 0)
    (hprod : (A * B).coeff n = 0)
    (hlower : ∀ k : ℕ, k < n → B.coeff k = 0) :
    B.coeff n = 0 := by
  have hlinear :=
    HC4.Newton.coeff_mul_eq_constant_mul_of_right_vanishes_below
      A B hlower
  have hmul : A.coeff 0 * B.coeff n = 0 := by
    rw [← hlinear]
    exact hprod
  exact (mul_eq_zero.mp hmul).resolve_left hA0

/-- **R18 whole-polynomial constant-pivot cancellation.**  Coefficientwise
vanishing of `A * B`, together with a nonzero constant coefficient of `A`,
forces `B = 0`.  The proof is deliberately triangular rather than divisive. -/
theorem polynomial_eq_zero_of_constant_pivot
    {R : Type u} [CommRing R] [IsDomain R]
    (A B : Polynomial R)
    (hA0 : A.coeff 0 ≠ 0)
    (hprod : ∀ n : ℕ, (A * B).coeff n = 0) :
    B = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      exact polynomial_coeff_eq_zero_of_constant_pivot
        A B hA0 (hprod n) (fun k hk => ih k hk)

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- `.pr`: cancel the actual contact-family active pivot from any
parameter-first polynomial identity. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_cancel_contactFamily_activeDet
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (hprod : ∀ n : ℕ,
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.contactFamily).activeDet B
  · exact P.pr_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hprod

/-- `.sp`: cancel the actual contact-family active pivot from any
parameter-first polynomial identity. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_cancel_contactFamily_activeDet
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (hprod : ∀ n : ℕ,
      (((permutedFamilyHessianFourBlock
          qsSpSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot
    (permutedFamilyHessianFourBlock
      qsSpSuperfaceSchurPermutation P.contactFamily).activeDet B
  · exact P.sp_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hprod

/-- `.rq`: cancel the actual contact-family active pivot from any
parameter-first polynomial identity. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_cancel_contactFamily_activeDet
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (hprod : ∀ n : ℕ,
      (((permutedFamilyHessianFourBlock
          qsRqSuperfaceSchurPermutation P.contactFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  apply polynomial_eq_zero_of_constant_pivot
    (permutedFamilyHessianFourBlock
      qsRqSuperfaceSchurPermutation P.contactFamily).activeDet B
  · exact P.rq_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  · exact hprod

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
