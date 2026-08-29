import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfacePivot
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import Mathlib.Tactic

/-!
# A19.127: cyclic cleared Schur blocks on the honest first superface

The first strict superface is now an honest singular source polynomial and
A19.126 gives the correct nonzero ordinary Hessian principal pivot in each of
the three other-facet cases.  We simultaneously permute coordinates so that
that pivot is the active `2 x 2` block of `GeneralFourBlock`.

The result is exactly the division-free Schur datum wanted by the closing
profile argument:

    activeDet != 0,
    schurDetCore = 0.

No matrix inverse, localization, or 24-term determinant expansion appears.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Put the `.pr` active pair `(2,3)` into four-block coordinates `(0,1)`. -/
def qsPrSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 2)

/-- Put the `.sp` active pair `(1,3)` into four-block coordinates `(0,1)`. -/
def qsSpSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)

/-- Put the `.rq` active pair `(1,2)` into four-block coordinates `(0,1)`. -/
def qsRqSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- `.pr`: honest first-superface four-block with nonzero active determinant
and zero cleared binary Schur determinant. -/
theorem QsOtherFacetRayFirstSuperfacePackage.pr_clearedSchur
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := permutedPolynomialHessianFourBlock
      qsPrSuperfaceSchurPermutation S.polynomial
    H.activeDet ≠ 0 ∧ H.schurDetCore = 0 := by
  dsimp only
  constructor
  · rw [permutedPolynomialHessianFourBlock_activeDet]
    simpa [qsPrSuperfaceSchurPermutation] using
      S.pr_hessianPrincipalMinor_ne_zero hthree houtThree
  · exact permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
      qsPrSuperfaceSchurPermutation S.polynomial
      S.hessianDeterminant_polynomial_eq_zero

/-- `.sp`: honest first-superface four-block with nonzero active determinant
and zero cleared binary Schur determinant. -/
theorem QsOtherFacetRayFirstSuperfacePackage.sp_clearedSchur
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    let H := permutedPolynomialHessianFourBlock
      qsSpSuperfaceSchurPermutation S.polynomial
    H.activeDet ≠ 0 ∧ H.schurDetCore = 0 := by
  dsimp only
  constructor
  · rw [permutedPolynomialHessianFourBlock_activeDet]
    simpa [qsSpSuperfaceSchurPermutation] using
      S.sp_hessianPrincipalMinor_ne_zero hthree houtThree
  · exact permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
      qsSpSuperfaceSchurPermutation S.polynomial
      S.hessianDeterminant_polynomial_eq_zero

/-- `.rq`: honest first-superface four-block with nonzero active determinant
and zero cleared binary Schur determinant. -/
theorem QsOtherFacetRayFirstSuperfacePackage.rq_clearedSchur
    (S : QsOtherFacetRayFirstSuperfacePackage C R)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    let H := permutedPolynomialHessianFourBlock
      qsRqSuperfaceSchurPermutation S.polynomial
    H.activeDet ≠ 0 ∧ H.schurDetCore = 0 := by
  dsimp only
  constructor
  · rw [permutedPolynomialHessianFourBlock_activeDet]
    simpa [qsRqSuperfaceSchurPermutation] using
      S.rq_hessianPrincipalMinor_ne_zero hthree houtThree
  · exact permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
      qsRqSuperfaceSchurPermutation S.polynomial
      S.hessianDeterminant_polynomial_eq_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
