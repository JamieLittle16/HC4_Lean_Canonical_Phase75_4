import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneEndpointFibers
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairRees
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 locked endpoint as the terminal pair-Rees layer

The pair-degree reverse Rees is oriented from the primitive-highest fibre.
The locked pair has pair degree one, hence occurs at parameter order `n-1`.
This file proves that this entire parameter layer is literally the two locked
source monomials and identifies its specialised Euler Hessian with the existing
`lockedBinomialMomentHessian`.
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

/-- Exact support of the terminal locked pair-Rees layer. -/
theorem lockedLayer_support_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    (familyParameterLayer D.family (F.highest.n - 1)).support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
  classical
  have hn2 := F.highest.n_two_le
  rw [D.parameterLayer_support]
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hgap⟩
    have hpairNat : e 0 + e 1 = 1 := by
      have hle : e 0 + e 1 ≤ F.highest.n := by
        rcases F.support_staircase_classification
            (by exact F.hthree) (by exact F.houtThree) he with
          ⟨_j, _hj, hk, _hjle, _h0, _h1⟩
        simpa [rankThreeQuotientCoordinate] using hk
      omega
    have hpair : (rankThreeQuotientCoordinate 1 F.V e).pair = 1 := by
      simpa [rankThreeQuotientCoordinate] using hpairNat
    exact F.eq_locked_of_support_pair_eq_one he hpair
  · intro heq
    rcases heq with rfl | rfl
    · refine ⟨F.locked.facet_provenance.carrier_mem, ?_⟩
      rw [F.locked.facet_zero, F.locked.facet_one]
      omega
    · refine ⟨F.locked.outside_provenance.carrier_mem, ?_⟩
      rw [F.locked.outside_zero, F.locked.outside_one]
      omega

/-- The terminal pair-Rees layer is the literal locked source binomial with
unchanged carrier coefficients. -/
theorem lockedLayer_eq_locked_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    familyParameterLayer D.family (F.highest.n - 1) =
      MvPolynomial.monomial C.ray.facetExponent
          (MvPolynomial.coeff C.ray.facetExponent P.carrier) +
        MvPolynomial.monomial C.ray.outsideExponent
          (MvPolynomial.coeff C.ray.outsideExponent P.carrier) := by
  classical
  let L := familyParameterLayer D.family (F.highest.n - 1)
  have hsupp : L.support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
    dsimp [L]
    exact D.lockedLayer_support_eq F
  have hne : C.ray.facetExponent ≠ C.ray.outsideExponent := by
    intro h
    have h0 := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.facet_zero, F.locked.outside_zero] at h0
    omega
  have hfacetCoeff :
      MvPolynomial.coeff C.ray.facetExponent L =
        MvPolynomial.coeff C.ray.facetExponent P.carrier := by
    dsimp [L]
    rw [D.parameterLayer_coeff]
    simp [F.locked.facet_provenance.carrier_mem,
      F.locked.facet_zero, F.locked.facet_one]
  have houtCoeff :
      MvPolynomial.coeff C.ray.outsideExponent L =
        MvPolynomial.coeff C.ray.outsideExponent P.carrier := by
    dsimp [L]
    rw [D.parameterLayer_coeff]
    simp [F.locked.outside_provenance.carrier_mem,
      F.locked.outside_zero, F.locked.outside_one]
  have hsum := MvPolynomial.as_sum L
  rw [hsupp] at hsum
  rw [Finset.sum_insert] at hsum
  · simp only [Finset.sum_singleton] at hsum
    rw [hfacetCoeff, houtCoeff] at hsum
    exact hsum
  · simpa using hne

/-- **Exact locked terminal-layer moment identification for the pair-Rees.** -/
theorem lockedLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    let a := MvPolynomial.coeff C.ray.facetExponent P.carrier
    let b := MvPolynomial.coeff C.ray.outsideExponent P.carrier
    (fun r s =>
      rankThreeLineSpecialisation
        (eulerScaledHessian
          (familyParameterLayer D.family (F.highest.n - 1)) r s)) =
      lockedBinomialMomentHessian F.V F.locked.ell a b := by
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
      simp [phi, hn0, hn1]
    · intro hn
      rcases hn with rfl | rfl
      · simp [phi, ha]
      · simp [phi, hb]
  let exponent : ℕ → (Fin 4 →₀ ℕ) := fun n =>
    if n = 0 then C.ray.facetExponent else C.ray.outsideExponent
  let L : RankThreeAffineLineData
      1 (F.locked.ell + 1) (F.V * (F.locked.ell + 1)) 1
      (-1 : K) (-1 : K) (-(F.V : K)) phi := {
    exponent := exponent
    affine := by
      intro n hn
      rw [hphiSupport] at hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · funext i
        fin_cases i <;>
          simp [exponent, rankThreeLogBaseExponent, rankThreeLogDirection,
            F.locked.facet_zero, F.locked.facet_one,
            F.locked.facet_two, F.locked.facet_three]
      · funext i
        fin_cases i <;>
          simp [exponent, rankThreeLogBaseExponent, rankThreeLogDirection,
            F.locked.outside_zero, F.locked.outside_one,
            F.locked.outside_two, F.locked.outside_three] <;> ring
  }
  have hpoly :
      L.polynomial = familyParameterLayer D.family (F.highest.n - 1) := by
    have hL :
        L.polynomial =
          MvPolynomial.monomial C.ray.facetExponent a +
            MvPolynomial.monomial C.ray.outsideExponent b := by
      simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
      rw [hphiSupport]
      rw [Finset.sum_insert]
      · simp only [Finset.sum_singleton]
        rw [L.term_eq_monomial, L.term_eq_monomial]
        simp [L, exponent, phi]
      · simp
    rw [hL]
    symm
    simpa [a, b] using D.lockedLayer_eq_locked_pair F
  have hm := L.specialisation_eulerScaledHessian
  rw [hpoly] at hm
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun hm r) s
  simpa [lockedBinomialMomentHessian, phi] using hrs

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
