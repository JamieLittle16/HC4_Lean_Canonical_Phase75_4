import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberThreeLayerPencil
import HC4.Valuation.ParameterGapSecondJet
import HC4.Polynomial.FiniteStaircaseSecondVariationTopCoefficient
import Mathlib.Tactic

/-!
# A19 exact second jet of the one-fibre pair-Rees pencil

For the exact three-layer pencil

    H_high + tau^q H_int + tau^N H_locked,
    q = n-k,  N = n-1,

we have `0 < q < N`.  Hence every entry has no positive parameter coefficient
below `q`, and the generic second parameter-gap jet applies.  Its matrix is
literally

    ((H_high,H_int),(H_int,2 H_{2q})).

The possible `H_{2q}` is left abstract here; exact three-layer support later
shows it is either zero or the degree-one locked endpoint.  This module is only
representation plumbing.
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

/-- The interior pair-Rees order is positive and strictly below the terminal
locked order. -/
theorem oneFiber_pairGap_pos_lt_terminal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo) :
    0 < F.highest.n - Alo.k ∧
      F.highest.n - Alo.k < F.highest.n - 1 := by
  omega

/-- Every entry of the exact one-fibre three-layer pencil has a genuine
positive gap below the unique interior order. -/
theorem oneFiberThreeLayerMomentPencil_hasGap
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (i j : Fin 4) :
    HasNoPositiveParameterCoeffBelow (F.highest.n - Alo.k)
      (oneFiberThreeLayerMomentPencil F Alo i j) := by
  intro r hrpos hrlt
  have hqpos : 0 < F.highest.n - Alo.k := by omega
  have hqN : F.highest.n - Alo.k < F.highest.n - 1 := by omega
  have hr0 : r ≠ 0 := Nat.ne_of_gt hrpos
  have hrq : r ≠ F.highest.n - Alo.k := by omega
  have hrN : r ≠ F.highest.n - 1 := by omega
  simp [oneFiberThreeLayerMomentPencil, Polynomial.coeff_monomial,
    hr0, hrq, hrN]

/-- The possibly resonant second-order matrix coefficient of the exact
three-layer pencil. -/
noncomputable def oneFiberSecondOrderMomentMatrix
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  fun i j =>
    (oneFiberThreeLayerMomentPencil F Alo i j).coeff
      (2 * (F.highest.n - Alo.k))

/-- **Exact second-jet representation.** -/
theorem matrixParameterGapSecondJet_oneFiberThreeLayer
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo) :
    let q := F.highest.n - Alo.k
    let A := highestBinomialMomentHessian F.V F.highest.n
      (MvPolynomial.coeff F.highest.e0 S.slice)
      (MvPolynomial.coeff F.highest.e1 S.slice)
    let B := parallelStaircaseMomentHessian F.V Alo.k Alo.j
      Alo.coefficientProfile
    let C2 := oneFiberSecondOrderMomentMatrix F Alo
    matrixParameterGapSecondJet (R := Polynomial K) (by omega : 0 < q)
        (oneFiberThreeLayerMomentPencil F Alo)
        (D.oneFiberThreeLayerMomentPencil_hasGap F Alo) =
      secondVariationJetMatrix A B C2 := by
  let q := F.highest.n - Alo.k
  let A := highestBinomialMomentHessian F.V F.highest.n
    (MvPolynomial.coeff F.highest.e0 S.slice)
    (MvPolynomial.coeff F.highest.e1 S.slice)
  let B := parallelStaircaseMomentHessian F.V Alo.k Alo.j
    Alo.coefficientProfile
  let C2 := oneFiberSecondOrderMomentMatrix F Alo
  have hqpos : 0 < q := by dsimp [q]; omega
  have hqN : q ≠ F.highest.n - 1 := by dsimp [q]; omega
  apply Matrix.ext
  intro i j
  rw [matrixParameterGapSecondJet_apply]
  simp only [secondVariationJetMatrix, secondVariationJetEntry]
  have h0 :
      (oneFiberThreeLayerMomentPencil F Alo i j).coeff 0 = A i j := by
    dsimp [A]
    simp [oneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos]
  have hq :
      (oneFiberThreeLayerMomentPencil F Alo i j).coeff q = B i j := by
    dsimp [B, q]
    simp [oneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos, hqN]
  have h2 :
      (oneFiberThreeLayerMomentPencil F Alo i j).coeff (2 * q) = C2 i j := by
    rfl
  rw [h0, hq, h2]

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
