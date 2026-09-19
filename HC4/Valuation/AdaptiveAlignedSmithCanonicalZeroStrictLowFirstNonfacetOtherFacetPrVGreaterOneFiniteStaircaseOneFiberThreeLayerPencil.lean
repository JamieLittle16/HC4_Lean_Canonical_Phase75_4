import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberPairOrders
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesLockedMomentRealisation
import HC4.Valuation.RankThreeLineSpecialisationHessianParameterSwap
import Mathlib.Tactic

/-!
# A19 one-fibre pair-Rees as an exact three-layer moment pencil

Under coincident low/high interior extrema, the pair-degree reverse Rees has
only three actual parameter orders:

* `0`       : the primitive-highest binomial;
* `n-k`     : the unique strict-interior fibre;
* `n-1`     : the locked binomial.

The parameter/longitudinal swap bridge identifies the corresponding
Euler-Hessian matrix coefficients with the already-verified moment matrices.
This file packages the result as a literal matrix polynomial equality.
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

/-- Zero outer parameter coefficient of the swapped Euler Hessian is exactly
the primitive-highest moment Hessian. -/
theorem oneFiber_swappedEuler_coeff_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (i j : Fin 4) :
    (swappedRankThreeEulerHessian D.family i j).coeff 0 =
      highestBinomialMomentHessian F.V F.highest.n
        (MvPolynomial.coeff F.highest.e0 S.slice)
        (MvPolynomial.coeff F.highest.e1 S.slice) i j := by
  rw [coeff_swappedRankThreeEulerHessian]
  have h := D.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left F
  exact congrFun (congrFun h i) j

/-- The unique positive interior coefficient occurs at exact order `n-k` and
is the selected parallel staircase moment Hessian. -/
theorem oneFiber_swappedEuler_coeff_interior
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
    (swappedRankThreeEulerHessian D.family i j).coeff
        (F.highest.n - Alo.k) =
      parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile i j := by
  have horder :
      firstPositiveActualParameterOrder D.family D.positiveLayer =
        F.highest.n - Alo.k := by
    calc
      firstPositiveActualParameterOrder D.family D.positiveLayer =
          F.highest.n - Ahi.k := Ahi.firstPositiveOrder_eq_pairGap
      _ = F.highest.n - Alo.k := by rw [← hext]
  rw [coeff_swappedRankThreeEulerHessian]
  rw [← horder]
  have h := Ahi.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hij := congrFun (congrFun h i) j
  simpa [hext] using hij

/-- Terminal outer parameter coefficient `n-1` is exactly the locked moment
Hessian. -/
theorem oneFiber_swappedEuler_coeff_locked
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (i j : Fin 4) :
    (swappedRankThreeEulerHessian D.family i j).coeff
        (F.highest.n - 1) =
      lockedBinomialMomentHessian F.V F.locked.ell
        (MvPolynomial.coeff C.ray.facetExponent P.carrier)
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j := by
  rw [coeff_swappedRankThreeEulerHessian]
  have h := D.lockedLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian F
  exact congrFun (congrFun h i) j

/-- Every other outer parameter coefficient matrix vanishes. -/
theorem oneFiber_swappedEuler_coeff_eq_zero_of_other
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
    (hext : Alo.k = Ahi.k)
    {q : ℕ}
    (hq0 : q ≠ 0)
    (hqInt : q ≠ F.highest.n - Alo.k)
    (hqLock : q ≠ F.highest.n - 1)
    (i j : Fin 4) :
    (swappedRankThreeEulerHessian D.family i j).coeff q = 0 := by
  have hLayer : familyParameterLayer D.family q = 0 := by
    by_contra hne
    rcases D.parameterLayer_order_trichotomy_of_oneFiber
        F Alo Ahi hthree houtThree hnot hext q hne with h | h | h
    · exact hq0 h
    · exact hqInt h
    · exact hqLock h
  rw [coeff_swappedRankThreeEulerHessian, hLayer]
  simp [eulerScaledHessian, mvEuler]

/-- Literal three-layer matrix pencil attached to the one-fibre pair-Rees. -/
noncomputable def oneFiberThreeLayerMomentPencil
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
      (highestBinomialMomentHessian F.V F.highest.n
        (MvPolynomial.coeff F.highest.e0 S.slice)
        (MvPolynomial.coeff F.highest.e1 S.slice) i j) +
    Polynomial.monomial (F.highest.n - Alo.k)
      (parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile i j) +
    Polynomial.monomial (F.highest.n - 1)
      (lockedBinomialMomentHessian F.V F.locked.ell
        (MvPolynomial.coeff C.ray.facetExponent P.carrier)
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier) i j)

/-- **Exact three-layer reconstruction.**  In the one-fibre branch the swapped
specialised Euler Hessian is literally the three-layer moment pencil above. -/
theorem swappedEuler_eq_oneFiberThreeLayerMomentPencil
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
    swappedRankThreeEulerHessian D.family =
      oneFiberThreeLayerMomentPencil F Alo := by
  have hqpos : 0 < F.highest.n - Alo.k := by
    omega
  have hNpos : 0 < F.highest.n - 1 := by
    omega
  have hqN : F.highest.n - Alo.k ≠ F.highest.n - 1 := by
    omega
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro q
  by_cases h0 : q = 0
  · subst q
    rw [D.oneFiber_swappedEuler_coeff_zero F]
    simp [oneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos,
      Nat.ne_of_gt hNpos]
  by_cases hInt : q = F.highest.n - Alo.k
  · subst q
    rw [D.oneFiber_swappedEuler_coeff_interior F Alo Ahi hext]
    simp [oneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos, hqN]
  by_cases hLock : q = F.highest.n - 1
  · subst q
    rw [D.oneFiber_swappedEuler_coeff_locked F]
    simp [oneFiberThreeLayerMomentPencil, Nat.ne_of_gt hNpos, Ne.symm hqN]
  · rw [D.oneFiber_swappedEuler_coeff_eq_zero_of_other
      F Alo Ahi hthree houtThree hnot hext h0 hInt hLock]
    simp [oneFiberThreeLayerMomentPencil, h0, hInt, hLock]

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
