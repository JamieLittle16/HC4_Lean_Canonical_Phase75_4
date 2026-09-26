import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamLongitudinalCoupling
import Mathlib.Tactic

/-!
# G17: cubic ordinary source degree is impossible at the final seam

The final seam carries an exact gradient collision on the marked source axis,

    0 ~ e_0,

and its represented Hessian determinant is identically one.

If the represented source has ordinary degree at most three, then every
gradient component restricted to that axis is a univariate polynomial of
degree at most two.  A quadratic polynomial taking the same value at 0 and 1
has derivative zero at the midpoint 1/2.  Consequently every entry in the
marked Hessian row vanishes at (1/2)e_0, contradicting determinant one.

This is the line-restriction form of the elementary quadratic Keller argument.
It uses no terminal weight, repair transition, or JC2 input.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A univariate polynomial of degree at most two which vanishes at both
endpoints 0 and 1 has zero derivative at the midpoint. -/
theorem polynomial_derivative_eval_half_eq_zero_of_natDegree_le_two
    (P : Polynomial K)
    (hdeg : P.natDegree ≤ 2)
    (hzero : Polynomial.eval 0 P = 0)
    (hone : Polynomial.eval 1 P = 0) :
    Polynomial.eval ((2 : K)⁻¹) P.derivative = 0 := by
  by_cases hP : P = 0
  · simp [hP]
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
  have hBdeg : B.natDegree = 0 := by
    omega
  have hBC : B = Polynomial.C (B.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hBdeg
  rw [hfactor, hBC]
  simp [Polynomial.derivative_mul]
  have htwo : (2 : K) ≠ 0 := by norm_num
  field_simp
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Axis restriction of one represented-source gradient component. -/
noncomputable def representedAxisGradientComponent
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) : Polynomial K :=
  longitudinalAxisRestriction
    (MvPolynomial.pderiv i T.representedSpecialFiber)

/-- If the maximal ordinary source degree is at most three, every represented
axis-gradient component has univariate degree at most two. -/
theorem representedAxisGradientComponent_natDegree_le_two
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 3)
    (i : Fin 4) :
    (T.representedAxisGradientComponent i).natDegree ≤ 2 := by
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

/-- Exact collision gives equal endpoint values for every represented
axis-gradient component. -/
theorem representedAxisGradientComponent_eval_zero_eq_eval_one
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    Polynomial.eval 0 (T.representedAxisGradientComponent i) =
      Polynomial.eval 1 (T.representedAxisGradientComponent i) := by
  have hcoll := T.finalSeamData.exactCollision i
  rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
    eval_finCons_zero_eq_longitudinalAxisRestriction] at hcoll
  simpa [representedAxisGradientComponent] using hcoll

/-- The represented gradient is normalized to zero at the left collision
endpoint. -/
theorem representedAxisGradientComponent_eval_zero
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    Polynomial.eval 0 (T.representedAxisGradientComponent i) = 0 := by
  have h := T.represented_gradientAtZero_eq_zero i
  rw [eval_finCons_zero_eq_longitudinalAxisRestriction] at h
  simpa [representedAxisGradientComponent] using h

/-- In degree at most three every marked-row Hessian entry vanishes at the
axis midpoint. -/
theorem represented_midpoint_hessianRow_zero_of_degree_le_three
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hD : T.topFace.degree ≤ 3)
    (i : Fin 4) :
    MvPolynomial.eval
        (Fin.cons ((2 : K)⁻¹) (fun _ : Fin 3 => 0))
        (HC4.Polynomial.hessian T.representedSpecialFiber
          (0 : Fin 4) i) = 0 := by
  let G := T.representedAxisGradientComponent i
  have hGdeg : G.natDegree ≤ 2 := by
    simpa [G] using T.representedAxisGradientComponent_natDegree_le_two hD i
  have hG0 : Polynomial.eval 0 G = 0 := by
    simpa [G] using T.representedAxisGradientComponent_eval_zero i
  have hG1 : Polynomial.eval 1 G = 0 := by
    have heq := T.representedAxisGradientComponent_eval_zero_eq_eval_one i
    have h0 := T.representedAxisGradientComponent_eval_zero i
    simpa [G, h0] using heq.symm
  have hmid :=
    polynomial_derivative_eval_half_eq_zero_of_natDegree_le_two
      G hGdeg hG0 hG1
  rw [show G.derivative =
      longitudinalAxisRestriction
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv i T.representedSpecialFiber)) by
        rw [G, representedAxisGradientComponent,
          longitudinalAxisRestriction_pderiv_zero]] at hmid
  rw [← eval_finCons_zero_eq_longitudinalAxisRestriction] at hmid
  have hcomm :=
    pderiv_comm_commRing (0 : Fin 4) i T.representedSpecialFiber
  simpa [HC4.Polynomial.hessian_apply, hcomm] using hmid

/-- **Cubic exclusion at the final seam.**

The maximal ordinary source degree is strictly larger than three. -/
theorem finalSeam_topFace_degree_ge_four
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    4 ≤ T.topFace.degree := by
  by_contra hnot
  have hD : T.topFace.degree ≤ 3 := by omega
  let point : Fin 4 → K :=
    Fin.cons ((2 : K)⁻¹) (fun _ : Fin 3 => 0)
  let H : Matrix (Fin 4) (Fin 4) K :=
    (MvPolynomial.eval point).mapMatrix
      (HC4.Polynomial.hessian T.representedSpecialFiber)
  have hrow : ∀ i : Fin 4, H 0 i = 0 := by
    intro i
    dsimp [H, point]
    exact T.represented_midpoint_hessianRow_zero_of_degree_le_three hD i
  have hdetzero : H.det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 4)
    exact hrow
  have hdetone : H.det = 1 := by
    calc
      H.det =
          MvPolynomial.eval point
            (HC4.Polynomial.hessianDeterminant
              T.representedSpecialFiber) := by
        dsimp [H]
        exact
          ((MvPolynomial.eval point).map_det
            (HC4.Polynomial.hessian T.representedSpecialFiber)).symm
      _ = 1 := by
        rw [T.finalSeamData.representedHessianDetOne]
        simp
  rw [hdetzero] at hdetone
  exact zero_ne_one hdetone

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
