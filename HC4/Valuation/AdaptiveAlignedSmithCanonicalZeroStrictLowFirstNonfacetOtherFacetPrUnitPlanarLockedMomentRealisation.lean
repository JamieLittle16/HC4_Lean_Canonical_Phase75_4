import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarSpecialFiber
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 moment realisation of the locked unit contact special fibre

The zero parameter layer is the literal locked source pair.  Package that pair
as a degree-one affine rank-three line and identify its specialised
Euler-scaled Hessian with the `V = 1` locked-binomial moment Hessian.
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

namespace QsOtherFacetPrUnitLeftPlanarContactReesData

/-- Exact locked zero-layer moment identification in the unit left orientation. -/
theorem zeroLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let a := MvPolynomial.coeff C.ray.facetExponent P.carrier
    let b := MvPolynomial.coeff C.ray.outsideExponent P.carrier
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family 0) r s)) =
      HC4.Polynomial.lockedBinomialMomentHessian 1 F.locked.ell a b := by
  classical
  let a : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let phi : Polynomial K := Polynomial.C a + Polynomial.C b * Polynomial.X
  have ha : a ≠ 0 := by
    dsimp [a]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hphiSupport : phi.support = {0, 1} := by
    ext n
    simp only [Polynomial.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hn
      by_cases hn0 : n = 0
      · exact Or.inl hn0
      by_cases hn1 : n = 1
      · exact Or.inr hn1
      exfalso
      apply hn
      have hC : (Polynomial.C a : Polynomial K).coeff n = 0 := by
        rw [Polynomial.coeff_C]
        simp [hn0]
      have hX : (Polynomial.X : Polynomial K).coeff n = 0 := by
        rw [← pow_one (Polynomial.X : Polynomial K)]
        rw [Polynomial.coeff_X_pow]
        simp [hn1]
      simp [phi, hC, hX]
    · intro hn
      rcases hn with rfl | rfl
      · simp [phi, ha]
      · simp [phi, hb]
  let exponent : ℕ → (Fin 4 →₀ ℕ) := fun n =>
    if n = 0 then C.ray.facetExponent else C.ray.outsideExponent
  let L : HC4.Polynomial.RankThreeAffineLineData
      1 (F.locked.ell + 1) (F.locked.ell + 1) 1
      (-1 : K) (-1 : K) (-1 : K) phi := {
    exponent := exponent
    affine := by
      intro n hn
      rw [hphiSupport] at hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · funext i
        fin_cases i <;>
          simp [exponent, HC4.Polynomial.rankThreeLogBaseExponent,
            HC4.Polynomial.rankThreeLogDirection,
            F.locked.facet_zero, F.locked.facet_one,
            F.locked.facet_two, F.locked.facet_three]
      · funext i
        fin_cases i <;>
          simp [exponent, HC4.Polynomial.rankThreeLogBaseExponent,
            HC4.Polynomial.rankThreeLogDirection,
            F.locked.outside_zero, F.locked.outside_one,
            F.locked.outside_two, F.locked.outside_three] <;> ring
  }
  have hpoly :
      L.polynomial =
        MvPolynomial.monomial C.ray.facetExponent a +
          MvPolynomial.monomial C.ray.outsideExponent b := by
    simp only [HC4.Polynomial.RankThreeAffineLineData.polynomial,
      Polynomial.sum_def]
    rw [hphiSupport]
    rw [Finset.sum_insert]
    · simp only [Finset.sum_singleton]
      rw [L.term_eq_monomial, L.term_eq_monomial]
      simp [L, exponent, phi]
    · simp
  have hsf := D.specialFiber_eq_locked_pair hthree houtThree
  have hLsf : L.polynomial = polynomialFamilySpecialFiber D.family := by
    exact hpoly.trans (by simpa [a, b] using hsf.symm)
  have hzero := polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    (K := K) (qsIntegralContactWeight 2) T.topFace.degree P.carrier D.bound
  change polynomialFamilySpecialFiber D.family = familyParameterLayer D.family 0 at hzero
  have hm := L.specialisation_eulerScaledHessian
  rw [hLsf, hzero] at hm
  dsimp only
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun hm r) s
  simpa [HC4.Polynomial.lockedBinomialMomentHessian, phi] using hrs

end QsOtherFacetPrUnitLeftPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
