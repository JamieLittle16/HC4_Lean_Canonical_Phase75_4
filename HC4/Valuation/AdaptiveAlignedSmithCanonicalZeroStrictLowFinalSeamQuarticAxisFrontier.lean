import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamCubicExclusion
import Mathlib.Tactic

/-!
# G18: quartic final-seam axis frontier

G17 excludes maximal ordinary source degree at most three.  If the remaining
source has degree four, every represented gradient component restricted to the
marked collision axis has degree at most three and vanishes at both endpoints
0 and 1.

Hence each such univariate gradient component is either zero or has the exact
form

    X * (X - 1) * B

with B nonzero of degree at most one.

This is an unconditional finite normal form for the complete marked-axis
gradient data in the first degree not removed by the midpoint argument.  No
terminal weight, repair transition, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A degree-at-most-three univariate polynomial with roots 0 and 1 is either
zero or is the endpoint quadratic times a nonzero linear residual. -/
inductive TwoEndpointLinearResidualData
    (P : Polynomial K) : Type u
  | zero
      (hzero : P = 0)
  | factored
      (B : Polynomial K)
      (B_ne_zero : B ≠ 0)
      (factorization :
        P =
          (Polynomial.X *
            (Polynomial.X - Polynomial.C (1 : K))) * B)
      (B_natDegree_le_one : B.natDegree ≤ 1)

/-- Construct the finite two-endpoint linear residual normal form. -/
theorem twoEndpointLinearResidualData_of_natDegree_le_three
    (P : Polynomial K)
    (hdeg : P.natDegree ≤ 3)
    (hzero : Polynomial.eval 0 P = 0)
    (hone : Polynomial.eval 1 P = 0) :
    Nonempty (TwoEndpointLinearResidualData P) := by
  by_cases hP : P = 0
  · exact ⟨.zero hP⟩
  have hX : (Polynomial.X : Polynomial K) ∣ P := by
    rw [Polynomial.X_dvd_iff]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hzero
  have hXone : Polynomial.X - Polynomial.C (1 : K) ∣ P := by
    have hdvd :=
      Polynomial.X_sub_C_dvd_sub_C_eval (p := P) (a := (1 : K))
    simpa [hone] using hdvd
  have hcoprime :
      IsCoprime (Polynomial.X : Polynomial K)
        (Polynomial.X - Polynomial.C (1 : K)) := by
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : K)) (b := (1 : K)) (by simp))
  have hprod :
      Polynomial.X * (Polynomial.X - Polynomial.C (1 : K)) ∣ P :=
    hcoprime.mul_dvd hX hXone
  rcases exists_twoEndpointResidual_natDegree_lt P hP hprod with
    ⟨B, hB, hfactor, hdegree⟩
  exact ⟨.factored B hB hfactor (by omega)⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Under maximal ordinary source degree at most four, every represented
axis-gradient component has degree at most three. -/
theorem representedAxisGradientComponent_natDegree_le_three
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4)
    (i : Fin 4) :
    (T.representedAxisGradientComponent i).natDegree ≤ 3 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [representedAxisGradientComponent,
      longitudinalAxisRestriction_pderiv_zero,
      Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Polynomial.coeff_derivative,
      longitudinalAxisRestriction_eq_coefficient_zero,
      coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
    let d : Fin 4 →₀ ℕ := (0 : Fin 3 →₀ ℕ).cons (n + 1)
    by_cases hc : MvPolynomial.coeff d T.representedSpecialFiber = 0
    · simpa [d, hc]
    · have hdmem : d ∈ T.representedSpecialFiber.support :=
        MvPolynomial.mem_support_iff.mpr hc
      have hmax := T.topFace.maximal d hdmem
      have hddeg : HC4.Polynomial.ordinaryDegree4 d = n + 1 := by
        dsimp [d]
        simp [HC4.Polynomial.ordinaryDegree4]
      rw [hddeg] at hmax
      omega
  · rw [representedAxisGradientComponent,
      ← longitudinalCoefficient_single_eq_axisRestriction_pderiv,
      Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
    let d : Fin 4 →₀ ℕ := (Finsupp.single j 1).cons n
    by_cases hc : MvPolynomial.coeff d T.representedSpecialFiber = 0
    · simpa [d, hc]
    · have hdmem : d ∈ T.representedSpecialFiber.support :=
        MvPolynomial.mem_support_iff.mpr hc
      have hmax := T.topFace.maximal d hdmem
      have hddeg : HC4.Polynomial.ordinaryDegree4 d = n + 1 := by
        dsimp [d]
        fin_cases j <;>
          simp [HC4.Polynomial.ordinaryDegree4]
      rw [hddeg] at hmax
      omega

/-- Quartic marked-axis normal form for one gradient component. -/
abbrev FinalSeamQuarticAxisGradientData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) : Type u :=
  TwoEndpointLinearResidualData (T.representedAxisGradientComponent i)

/-- Every represented axis-gradient component has the finite quartic normal
form whenever the maximal ordinary source degree is at most four. -/
theorem finalSeamQuarticAxisGradientData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4)
    (i : Fin 4) :
    Nonempty (T.FinalSeamQuarticAxisGradientData i) := by
  have hdeg :=
    T.representedAxisGradientComponent_natDegree_le_three hD i
  have hzero :=
    T.representedAxisGradientComponent_eval_zero i
  have heq :=
    T.representedAxisGradientComponent_eval_zero_eq_eval_one i
  have hone :
      Polynomial.eval 1 (T.representedAxisGradientComponent i) = 0 := by
    rw [← heq, hzero]
  exact twoEndpointLinearResidualData_of_natDegree_le_three
    (T.representedAxisGradientComponent i) hdeg hzero hone

/-- Since G17 gives degree at least four, an upper bound by four is actually
the exact quartic case. -/
theorem finalSeam_degree_eq_four_of_le_four
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4) :
    T.topFace.degree = 4 := by
  have h4 := T.finalSeam_topFace_degree_ge_four
  omega

/-- The complete four-component quartic axis packet. -/
structure FinalSeamQuarticAxisPacket
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type u where
  degree_eq_four : T.topFace.degree = 4
  component :
    ∀ i : Fin 4, T.FinalSeamQuarticAxisGradientData i

/-- Assemble the finite quartic packet from a degree upper bound. -/
theorem finalSeamQuarticAxisPacket_of_degree_le_four
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 4) :
    Nonempty T.FinalSeamQuarticAxisPacket := by
  refine ⟨{
    degree_eq_four := T.finalSeam_degree_eq_four_of_le_four hD
    component := fun i =>
      Classical.choice (T.finalSeamQuarticAxisGradientData hD i)
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
