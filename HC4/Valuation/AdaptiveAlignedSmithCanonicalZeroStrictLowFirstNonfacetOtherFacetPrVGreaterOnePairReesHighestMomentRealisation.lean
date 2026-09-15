import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairRees
import HC4.Valuation.PlanarHighestFirstVariationBridge
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 highest pair-Rees special fibre as the primitive highest moment Hessian

The pair-degree reverse Rees is oriented from the primitive highest slice.
Its zero layer is therefore the literal source-honest highest binomial already
stored by the live `(1,V)` frontier.  This file identifies the specialised
Euler-scaled Hessian of that exact zero layer with
`highestBinomialMomentHessian`.

No copied support, normalisation, or new singularity hypothesis is introduced.
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

/-- **Exact highest zero-layer moment identification.**  The coefficients are
literally the coefficients of the retained highest slice. -/
theorem zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    let c := MvPolynomial.coeff F.highest.e0 S.slice
    let d := MvPolynomial.coeff F.highest.e1 S.slice
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family 0) r s)) =
      HC4.Polynomial.highestBinomialMomentHessian
        F.V F.highest.n c d := by
  classical
  let e0 := F.highest.e0
  let e1 := F.highest.e1
  let c : K := MvPolynomial.coeff e0 S.slice
  let d : K := MvPolynomial.coeff e1 S.slice
  let phi : Polynomial K := Polynomial.C c + Polynomial.C d * Polynomial.X

  have he0S : e0 ∈ S.slice.support := by
    dsimp [e0]
    rw [F.highest.slice_support_eq]
    simp
  have he1S : e1 ∈ S.slice.support := by
    dsimp [e1]
    rw [F.highest.slice_support_eq]
    simp
  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp he0S
  have hd : d ≠ 0 := by
    dsimp [d]
    exact MvPolynomial.mem_support_iff.mp he1S
  have he01 : e0 ≠ e1 := by
    intro h
    have h0 := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    dsimp [e0, e1] at h0
    rw [F.highest.e0_zero, F.highest.e1_zero] at h0
    omega

  have hphiSupport : phi.support = {0, 1} := by
    ext m
    simp only [Polynomial.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hm
      by_cases hm0 : m = 0
      · exact Or.inl hm0
      by_cases hm1 : m = 1
      · exact Or.inr hm1
      exfalso
      apply hm
      simp [phi, hm0, hm1]
    · intro hm
      rcases hm with rfl | rfl
      · simp [phi, hc]
      · simp [phi, hd]

  let exponent : ℕ → (Fin 4 →₀ ℕ) := fun m =>
    if m = 0 then e0 else e1
  let L : HC4.Polynomial.RankThreeAffineLineData
      F.highest.n 1 (F.V * F.highest.n) 1
      (-1 : K) (-1 : K) (-(F.V : K)) phi := {
    exponent := exponent
    affine := by
      intro m hm
      rw [hphiSupport] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · funext i
        fin_cases i <;>
          simp [exponent, e0,
            HC4.Polynomial.rankThreeLogBaseExponent,
            HC4.Polynomial.rankThreeLogDirection,
            F.highest.e0_zero, F.highest.e0_one,
            F.highest.e0_two, F.highest.e0_three,
            F.highest_V_eq]
      · funext i
        fin_cases i <;>
          simp [exponent, e1,
            HC4.Polynomial.rankThreeLogBaseExponent,
            HC4.Polynomial.rankThreeLogDirection,
            F.highest.e1_zero, F.highest.e1_one,
            F.highest.e1_two, F.highest.e1_three,
            F.highest_V_eq] <;> ring
  }

  have hLpoly :
      L.polynomial =
        MvPolynomial.monomial e0 c + MvPolynomial.monomial e1 d := by
    simp only [HC4.Polynomial.RankThreeAffineLineData.polynomial,
      Polynomial.sum_def]
    rw [hphiSupport]
    rw [Finset.sum_insert]
    · simp only [Finset.sum_singleton]
      rw [L.term_eq_monomial, L.term_eq_monomial]
      simp [L, exponent, phi]
    · simp

  have hslice :
      S.slice =
        MvPolynomial.monomial e0 c + MvPolynomial.monomial e1 d := by
    have hsum := MvPolynomial.as_sum S.slice
    rw [F.highest.slice_support_eq] at hsum
    dsimp [e0, e1, c, d]
    simpa [Finset.sum_insert, he01] using hsum

  have hpoly : L.polynomial = S.slice :=
    hLpoly.trans hslice.symm

  have hzero : familyParameterLayer D.family 0 = S.slice := by
    calc
      familyParameterLayer D.family 0 =
          polynomialFamilySpecialFiber D.family := by
        apply MvPolynomial.ext
        intro e
        rw [familyParameterLayer_coeff, coeff_polynomialFamilySpecialFiber]
        rfl
      _ = S.slice := D.specialFiber_eq_slice

  have hm := L.specialisation_eulerScaledHessian
  rw [hpoly, ← hzero] at hm
  dsimp only
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun hm r) s
  simpa [HC4.Polynomial.highestBinomialMomentHessian, phi, c, d, e0, e1]
    using hrs

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
