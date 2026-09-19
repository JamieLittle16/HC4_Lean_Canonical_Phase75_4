import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberThreeLayerPencil
import HC4.Valuation.RankThreeLineSpecialisationHessianDeterminantSwap
import HC4.Polynomial.MatrixPolynomialReflect
import Mathlib.Tactic

/-!
# A19 reflected unit one-fibre three-layer moment pencil

Reflecting the exact unit pair-Rees pencil at terminal order `N=n-1` reverses
its outer grading and gives the locked-based pencil

    H_locked + tau^(k-1) H_int + tau^(n-1) H_high.

The determinant reflection theorem then transports singularity exactly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

noncomputable def unitLeftOneFiberReflectedThreeLayerMomentPencil
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  fun i j =>
    Polynomial.C
      (lockedBinomialMomentHessian 1 F.locked.ell
        (MvPolynomial.coeff C.ray.facetExponent P.carrier)
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j) +
    Polynomial.monomial (Alo.k - 1)
      (parallelStaircaseMomentHessian 1 Alo.k Alo.j
        Alo.coefficientProfile i j) +
    Polynomial.monomial (F.highest.n - 1)
      (highestBinomialMomentHessian 1 F.highest.n
        (MvPolynomial.coeff F.highest.e0 S.slice)
        (MvPolynomial.coeff F.highest.e1 S.slice) i j)

/-- Every entry of the original unit one-fibre pencil has outer degree at most
`n-1`. -/
theorem unitLeftOneFiberThreeLayerMomentPencil_natDegree_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (i j : Fin 4) :
    (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).natDegree ≤
      F.highest.n - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hqle : F.highest.n - Alo.k ≤ F.highest.n - 1 := by omega
  have hm0 : m ≠ 0 := by omega
  have hmq : m ≠ F.highest.n - Alo.k := by omega
  have hmN : m ≠ F.highest.n - 1 := by omega
  simp [unitLeftOneFiberThreeLayerMomentPencil, Polynomial.coeff_monomial,
    hm0, hmq, hmN]

/-- Entrywise reflection at `n-1` is exactly the unit locked-based pencil. -/
theorem reflect_unitLeftOneFiberThreeLayerMomentPencil
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo) :
    HC4.Polynomial.reflectMatrix (F.highest.n - 1)
        (unitLeftOneFiberThreeLayerMomentPencil F Alo) =
      unitLeftOneFiberReflectedThreeLayerMomentPencil F Alo := by
  let N := F.highest.n - 1
  let q := F.highest.n - Alo.k
  have hqle : q ≤ N := by dsimp [q, N]; omega
  have hgap : N - q = Alo.k - 1 := by dsimp [q, N]; omega
  have hreflectC (r : Polynomial K) :
      Polynomial.reflect N (Polynomial.C r) =
        Polynomial.monomial N r := by
    rw [Polynomial.reflect_C]
    rw [Polynomial.X_pow_eq_monomial]
    simp
  have hreflectMono (m : ℕ) (r : Polynomial K) (hm : m ≤ N) :
      Polynomial.reflect N (Polynomial.monomial m r) =
        Polynomial.monomial (N - m) r := by
    have hrepr :
        Polynomial.monomial m r = Polynomial.C r * Polynomial.X ^ m := by
      rw [Polynomial.X_pow_eq_monomial]
      simp
    rw [hrepr, Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le hm]
    rw [Polynomial.X_pow_eq_monomial]
    simp
  apply Matrix.ext
  intro i j
  simp only [HC4.Polynomial.reflectMatrix,
    unitLeftOneFiberThreeLayerMomentPencil,
    unitLeftOneFiberReflectedThreeLayerMomentPencil]
  rw [Polynomial.reflect_add, Polynomial.reflect_add]
  rw [hreflectC]
  rw [hreflectMono q _ hqle]
  rw [hreflectMono N _ (le_refl N)]
  rw [hgap]
  simp [N, q, add_assoc, add_comm, add_left_comm]

/-- The reflected locked-based unit pencil has identically zero determinant. -/
theorem det_unitLeftOneFiberReflectedThreeLayerMomentPencil_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    (unitLeftOneFiberReflectedThreeLayerMomentPencil F Alo).det = 0 := by
  have hmatrix := D.swappedEuler_eq_unitLeftOneFiberThreeLayerMomentPencil
    F Alo Ahi hthree houtThree hnot hext
  have hdetSwapped : (swappedRankThreeEulerHessian D.family).det = 0 :=
    det_swappedRankThreeEulerHessian_eq_zero_of_hessianDeterminant_eq_zero
      D.family D.hessian_zero
  have hdet : (unitLeftOneFiberThreeLayerMomentPencil F Alo).det = 0 := by
    rw [← hmatrix]
    exact hdetSwapped
  have hdeg : ∀ i j,
      (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).natDegree ≤
        F.highest.n - 1 := by
    intro i j
    exact D.unitLeftOneFiberThreeLayerMomentPencil_natDegree_le F Alo i j
  rw [← D.reflect_unitLeftOneFiberThreeLayerMomentPencil F Alo]
  rw [HC4.Polynomial.det_reflectMatrix
    (unitLeftOneFiberThreeLayerMomentPencil F Alo) (F.highest.n - 1) hdeg]
  rw [hdet]
  simp

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
