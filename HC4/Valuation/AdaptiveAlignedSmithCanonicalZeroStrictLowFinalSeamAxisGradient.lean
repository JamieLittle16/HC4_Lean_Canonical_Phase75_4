import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamAxisHessian
import HC4.Newton.TerminalPositiveWeightLinearBlocks
import Mathlib.Tactic

/-!
# G5: every final-seam axis gradient has the two collision roots

The G1 right-recentered seam has zero source-linear jet at the new origin and
an exact gradient collision between the origin and the negative marked axis
point.  Consequently each component of the gradient, restricted to the
longitudinal axis, vanishes at both `x = 0` and `x = -1`.

This file packages that elementary fact in the useful divisibility form

    X (X + 1) ∣ gradient_i|axis.

It is independent of which of the three strict-low Smith patterns is present.
The result is intended to be combined with G3's exact Hessian-entry orders,
since those Hessian entries are derivatives of these two-endpoint axis
gradient polynomials.

No progress theorem, repair transition, cocharacter, homogeneity assumption,
or JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The `i`th gradient component of the honest right-recentered seam,
restricted to the distinguished longitudinal axis. -/
noncomputable def finalSeamAxisGradientComponent
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) : Polynomial K :=
  longitudinalAxisRestriction
    (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber)

/-- Zero source-linear jet says every restricted gradient component vanishes
at the recentered origin. -/
theorem finalSeamAxisGradientComponent_eval_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    Polynomial.eval 0 (T.finalSeamAxisGradientComponent i) = 0 := by
  let R := T.finalSeamRightRecenteredData
  have hgrad :
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
          (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber) = 0 := by
    rw [eval_zero_pderiv_eq_linearCoeff]
    exact R.linearCoeff_zero i
  have haxis :=
    eval_finCons_zero_eq_longitudinalAxisRestriction
      (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber) (0 : K)
  rw [show (Fin.cons (0 : K) (fun _ : Fin 3 => (0 : K))) =
      (fun _ : Fin 4 => (0 : K)) by
        funext j
        fin_cases j <;> rfl] at haxis
  simpa [finalSeamAxisGradientComponent] using haxis.symm.trans hgrad

/-- The exact recentered collision gives the second root `x = -1`. -/
theorem finalSeamAxisGradientComponent_eval_neg_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    Polynomial.eval (-1 : K) (T.finalSeamAxisGradientComponent i) = 0 := by
  let R := T.finalSeamRightRecenteredData
  have hleft :
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
          (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber) = 0 := by
    rw [eval_zero_pderiv_eq_linearCoeff]
    exact R.linearCoeff_zero i
  have hcoll := R.exactCollision i
  have hright :
      MvPolynomial.eval
          (fun j => - coordinateAxisPoint (K := K) (0 : Fin 4) j)
          (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber) = 0 := by
    rw [← hcoll]
    exact hleft
  have hpoint :
      (fun j => - coordinateAxisPoint (K := K) (0 : Fin 4) j) =
        Fin.cons (-1 : K) (fun _ : Fin 3 => (0 : K)) := by
    funext j
    fin_cases j <;> simp [coordinateAxisPoint]
  rw [hpoint] at hright
  have haxis :=
    eval_finCons_zero_eq_longitudinalAxisRestriction
      (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber) (-1 : K)
  simpa [finalSeamAxisGradientComponent] using haxis.symm.trans hright

/-- Every axis-gradient component contains both collision endpoint factors. -/
theorem finalSeamAxisGradientComponent_twoEndpoint_dvd
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    Polynomial.X * (Polynomial.X + Polynomial.C (1 : K)) ∣
      T.finalSeamAxisGradientComponent i := by
  let Q := T.finalSeamAxisGradientComponent i
  have h0 : Polynomial.eval 0 Q = 0 := by
    simpa [Q] using T.finalSeamAxisGradientComponent_eval_zero i
  have hm1 : Polynomial.eval (-1 : K) Q = 0 := by
    simpa [Q] using T.finalSeamAxisGradientComponent_eval_neg_one i

  have hX : (Polynomial.X : Polynomial K) ∣ Q := by
    have h :=
      Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := (0 : K))
    simpa [h0] using h

  have hXm1 :
      Polynomial.X - Polynomial.C (-1 : K) ∣ Q := by
    have h :=
      Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := (-1 : K))
    simpa [hm1] using h

  have hcoprime :
      IsCoprime (Polynomial.X : Polynomial K)
        (Polynomial.X - Polynomial.C (-1 : K)) := by
    simpa using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : K)) (b := (-1 : K)) (by simp))

  have hprod :
      Polynomial.X * (Polynomial.X - Polynomial.C (-1 : K)) ∣ Q :=
    hcoprime.mul_dvd hX hXm1
  simpa [Q] using hprod

/-- Factorisation-facing form of the same two-endpoint constraint. -/
theorem finalSeamAxisGradientComponent_twoEndpoint_factor
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    ∃ B : Polynomial K,
      T.finalSeamAxisGradientComponent i =
        (Polynomial.X * (Polynomial.X + Polynomial.C (1 : K))) * B := by
  rcases T.finalSeamAxisGradientComponent_twoEndpoint_dvd i with ⟨B, hB⟩
  exact ⟨B, hB.symm⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
