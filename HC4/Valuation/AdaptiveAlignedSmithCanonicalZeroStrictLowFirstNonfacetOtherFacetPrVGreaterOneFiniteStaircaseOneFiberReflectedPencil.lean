import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberThreeLayerPencil
import HC4.Valuation.RankThreeLineSpecialisationHessianDeterminantSwap
import HC4.Polynomial.MatrixPolynomialReflect
import Mathlib.Tactic

/-!
# A19 reflected one-fibre pair-Rees pencil

The exact one-fibre pair-Rees has outer parameter orders

    0, q = n-k, N = n-1.

Reflecting every matrix entry at degree `N` reverses these to

    0, N-q = k-1, N.

Thus the same honest source-derived singular family can be read from the
locked end without constructing a second Rees family.  This is the endpoint
dual needed for the lower pure-mode determinant obstruction.
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

/-- Every entry of the one-fibre three-layer pencil has outer parameter degree
at most the terminal order `n-1`. -/
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
  have hq : F.highest.n - Alo.k ≤ F.highest.n - 1 := by
    omega
  dsimp [oneFiberThreeLayerMomentPencil]
  compute_degree

/-- Reflected swapped Euler-Hessian matrix, read from the locked terminal
layer. -/
noncomputable def oneFiberReflectedEulerHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  HC4.Polynomial.reflectMatrix (F.highest.n - 1)
    (swappedRankThreeEulerHessian D.family)

/-- The reflected matrix remains determinant-singular. -/
theorem det_oneFiberReflectedEulerHessian_eq_zero
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
    (oneFiberReflectedEulerHessian D F).det = 0 := by
  have hmatrix := D.swappedEuler_eq_oneFiberThreeLayerMomentPencil
    F Alo Ahi hthree houtThree hnot hext
  have hdeg : ∀ i j,
      (swappedRankThreeEulerHessian D.family i j).natDegree ≤
        F.highest.n - 1 := by
    intro i j
    rw [hmatrix]
    exact D.oneFiberThreeLayerMomentPencil_natDegree_le F Alo i j
  have hreflect := HC4.Polynomial.det_reflectMatrix
    (M := swappedRankThreeEulerHessian D.family)
    (N := F.highest.n - 1) hdeg
  have hdet : (swappedRankThreeEulerHessian D.family).det = 0 :=
    det_swappedRankThreeEulerHessian_eq_zero_of_hessianDeterminant_eq_zero
      D.family D.hessian_zero
  rw [hdet] at hreflect
  simpa [oneFiberReflectedEulerHessian] using hreflect

/-- Locked endpoint becomes the zero layer of the reflected pencil. -/
theorem oneFiberReflectedEuler_coeff_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (i j : Fin 4) :
    (oneFiberReflectedEulerHessian D F i j).coeff 0 =
      lockedBinomialMomentHessian F.V F.locked.ell
        (MvPolynomial.coeff C.ray.facetExponent P.carrier)
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j := by
  rw [oneFiberReflectedEulerHessian, HC4.Polynomial.reflectMatrix,
    Polynomial.coeff_reflect, Polynomial.revAt_zero]
  exact D.oneFiber_swappedEuler_coeff_locked F i j

/-- The unique interior layer moves to exact reflected order `k-1`. -/
theorem oneFiberReflectedEuler_coeff_interior
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
    (hext : Alo.k = Ahi.k)
    (i j : Fin 4) :
    (oneFiberReflectedEulerHessian D F i j).coeff (Alo.k - 1) =
      parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile i j := by
  have hkN : Alo.k - 1 ≤ F.highest.n - 1 := by omega
  have hrev :
      Polynomial.revAt (F.highest.n - 1) (Alo.k - 1) =
        F.highest.n - Alo.k := by
    rw [Polynomial.revAt_le hkN]
    omega
  rw [oneFiberReflectedEulerHessian, HC4.Polynomial.reflectMatrix,
    Polynomial.coeff_reflect, hrev]
  exact D.oneFiber_swappedEuler_coeff_interior F Alo Ahi hext i j

/-- Primitive-highest endpoint becomes the terminal reflected layer. -/
theorem oneFiberReflectedEuler_coeff_highest
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (i j : Fin 4) :
    (oneFiberReflectedEulerHessian D F i j).coeff (F.highest.n - 1) =
      highestBinomialMomentHessian F.V F.highest.n
        (MvPolynomial.coeff F.highest.e0 S.slice)
        (MvPolynomial.coeff F.highest.e1 S.slice) i j := by
  have hN : F.highest.n - 1 ≤ F.highest.n - 1 := le_rfl
  have hrev :
      Polynomial.revAt (F.highest.n - 1) (F.highest.n - 1) = 0 := by
    rw [Polynomial.revAt_le hN]
    omega
  rw [oneFiberReflectedEulerHessian, HC4.Polynomial.reflectMatrix,
    Polynomial.coeff_reflect, hrev]
  exact D.oneFiber_swappedEuler_coeff_zero F i j

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
