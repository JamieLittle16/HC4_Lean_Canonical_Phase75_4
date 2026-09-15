import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberThreeLayerPencil
import HC4.Valuation.RankThreeLineSpecialisationHessianDeterminantSwap
import HC4.Polynomial.MatrixPolynomialReflect
import Mathlib.Tactic

/-!
# A19 reflected one-fibre three-layer moment pencil

The exact pair-degree Rees pencil is oriented from the primitive-highest
endpoint:

    H_high + tau^(n-k) H_int + tau^(n-1) H_locked.

Reflecting the outer parameter polynomial at `N=n-1` reverses this finite
grading without constructing a second source family.  The reflected pencil is
literally

    H_locked + tau^(k-1) H_int + tau^(n-1) H_high.

Because every entry has outer degree at most `N`, determinant reflection is
exact.  Hence the reflected locked-based pencil also has identically zero
determinant.
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

/-- The same exact three layers, now written from the locked endpoint after
reflection of the pair-Rees parameter grading. -/
noncomputable def oneFiberReflectedThreeLayerMomentPencil
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  fun i j =>
    Polynomial.C
      (lockedBinomialMomentHessian F.V F.locked.ell
        (MvPolynomial.coeff C.ray.facetExponent P.carrier)
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j) +
    Polynomial.monomial (Alo.k - 1)
      (parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile i j) +
    Polynomial.monomial (F.highest.n - 1)
      (highestBinomialMomentHessian F.V F.highest.n
        (MvPolynomial.coeff F.highest.e0 S.slice)
        (MvPolynomial.coeff F.highest.e1 S.slice) i j)

/-- Every entry of the original one-fibre pencil has outer degree at most the
terminal pair-Rees order `n-1`. -/
theorem oneFiberThreeLayerMomentPencil_natDegree_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (i j : Fin 4) :
    (oneFiberThreeLayerMomentPencil F Alo i j).natDegree ≤
      F.highest.n - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hqle : F.highest.n - Alo.k ≤ F.highest.n - 1 := by omega
  have hm0 : m ≠ 0 := by omega
  have hmq : m ≠ F.highest.n - Alo.k := by omega
  have hmN : m ≠ F.highest.n - 1 := by omega
  simp [oneFiberThreeLayerMomentPencil, Polynomial.coeff_monomial,
    hm0, hmq, hmN]

/-- Entrywise reflection at `n-1` is exactly the locked-based three-layer
pencil. -/
theorem reflect_oneFiberThreeLayerMomentPencil
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo) :
    HC4.Polynomial.reflectMatrix (F.highest.n - 1)
        (oneFiberThreeLayerMomentPencil F Alo) =
      oneFiberReflectedThreeLayerMomentPencil F Alo := by
  let N := F.highest.n - 1
  let q := F.highest.n - Alo.k
  have hqle : q ≤ N := by
    dsimp [q, N]
    omega
  have hgap : N - q = Alo.k - 1 := by
    dsimp [q, N]
    omega
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
    oneFiberThreeLayerMomentPencil,
    oneFiberReflectedThreeLayerMomentPencil]
  rw [Polynomial.reflect_add, Polynomial.reflect_add]
  rw [hreflectC]
  rw [hreflectMono q _ hqle]
  rw [hreflectMono N _ (le_refl N)]
  rw [hgap]
  simp [N, q, add_assoc, add_comm, add_left_comm]

/-- **Reflected determinant zero.**  The exact locked-based three-layer pencil
inherits determinant singularity from the honest pair-Rees family. -/
theorem det_oneFiberReflectedThreeLayerMomentPencil_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k) :
    (oneFiberReflectedThreeLayerMomentPencil F Alo).det = 0 := by
  have hmatrix := D.swappedEuler_eq_oneFiberThreeLayerMomentPencil
    F Alo Ahi hthree houtThree hnot hext
  have hdetSwapped : (swappedRankThreeEulerHessian D.family).det = 0 :=
    det_swappedRankThreeEulerHessian_eq_zero_of_hessianDeterminant_eq_zero
      D.family D.hessian_zero
  have hdet : (oneFiberThreeLayerMomentPencil F Alo).det = 0 := by
    rw [← hmatrix]
    exact hdetSwapped
  have hdeg : ∀ i j,
      (oneFiberThreeLayerMomentPencil F Alo i j).natDegree ≤
        F.highest.n - 1 := by
    intro i j
    exact D.oneFiberThreeLayerMomentPencil_natDegree_le F Alo i j
  rw [← D.reflect_oneFiberThreeLayerMomentPencil F Alo]
  rw [HC4.Polynomial.det_reflectMatrix
    (oneFiberThreeLayerMomentPencil F Alo) (F.highest.n - 1) hdeg]
  rw [hdet]
  simp

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
