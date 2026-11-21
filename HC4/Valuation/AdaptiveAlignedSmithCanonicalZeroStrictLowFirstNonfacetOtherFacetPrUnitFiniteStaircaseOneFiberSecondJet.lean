import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberThreeLayerPencil
import HC4.Valuation.ParameterGapSecondJet
import HC4.Polynomial.FiniteStaircaseSecondVariationTopCoefficient
import Mathlib.Tactic

/-!
# A19 exact second jet of the unit one-fibre pair-Rees pencil

For the exact unit three-layer pencil

    H_high + tau^(n-k) H_int + tau^(n-1) H_locked,

the interior order is positive and strictly below the locked terminal order.
The generic parameter-gap second jet therefore applies verbatim.
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

/-- The unit interior pair-Rees order is positive and below the locked order. -/
theorem unitLeft_oneFiber_pairGap_pos_lt_terminal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo) :
    0 < F.highest.n - Alo.k ∧
      F.highest.n - Alo.k < F.highest.n - 1 := by
  omega

/-- Every entry of the exact unit three-layer pencil has no positive
parameter coefficient below its interior order. -/
theorem unitLeftOneFiberThreeLayerMomentPencil_hasGap
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (i j : Fin 4) :
    HasNoPositiveParameterCoeffBelow (F.highest.n - Alo.k)
      (unitLeftOneFiberThreeLayerMomentPencil F Alo i j) := by
  intro r hrpos hrlt
  have hqpos : 0 < F.highest.n - Alo.k := by omega
  have hr0 : r ≠ 0 := Nat.ne_of_gt hrpos
  have hrq : r ≠ F.highest.n - Alo.k := by omega
  have hrN : r ≠ F.highest.n - 1 := by omega
  simp [unitLeftOneFiberThreeLayerMomentPencil, Polynomial.coeff_monomial,
    hr0, hrq, hrN]

/-- The possibly resonant second-order coefficient matrix of the unit pencil. -/
noncomputable def unitLeftOneFiberSecondOrderMomentMatrix
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  fun i j =>
    (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).coeff
      (2 * (F.highest.n - Alo.k))

/-- Exact second-jet representation for the unit one-fibre pencil. -/
theorem matrixParameterGapSecondJet_unitLeftOneFiberThreeLayer
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo) :
    let q := F.highest.n - Alo.k
    let A := highestBinomialMomentHessian 1 F.highest.n
      (MvPolynomial.coeff F.highest.e0 S.slice)
      (MvPolynomial.coeff F.highest.e1 S.slice)
    let B := parallelStaircaseMomentHessian 1 Alo.k Alo.j
      Alo.coefficientProfile
    let C2 := unitLeftOneFiberSecondOrderMomentMatrix F Alo
    matrixParameterGapSecondJet (R := Polynomial K) (by omega : 0 < q)
        (unitLeftOneFiberThreeLayerMomentPencil F Alo)
        (unitLeftOneFiberThreeLayerMomentPencil_hasGap F Alo) =
      secondVariationJetMatrix A B C2 := by
  let q := F.highest.n - Alo.k
  let A := highestBinomialMomentHessian 1 F.highest.n
    (MvPolynomial.coeff F.highest.e0 S.slice)
    (MvPolynomial.coeff F.highest.e1 S.slice)
  let B := parallelStaircaseMomentHessian 1 Alo.k Alo.j
    Alo.coefficientProfile
  let C2 := unitLeftOneFiberSecondOrderMomentMatrix F Alo
  have hqpos : 0 < q := by dsimp [q]; omega
  have hqN : q ≠ F.highest.n - 1 := by dsimp [q]; omega
  apply Matrix.ext
  intro i j
  rw [matrixParameterGapSecondJet_apply]
  simp only [secondVariationJetMatrix, secondVariationJetEntry]
  have h0 :
      (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).coeff 0 = A i j := by
    dsimp [A]
    simp [unitLeftOneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos]
  have hq :
      (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).coeff q = B i j := by
    dsimp [B, q]
    simp [unitLeftOneFiberThreeLayerMomentPencil, Nat.ne_of_gt hqpos, hqN]
  have h2 :
      (unitLeftOneFiberThreeLayerMomentPencil F Alo i j).coeff (2 * q) = C2 i j := by
    rfl
  rw [h0, hq, h2]

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
