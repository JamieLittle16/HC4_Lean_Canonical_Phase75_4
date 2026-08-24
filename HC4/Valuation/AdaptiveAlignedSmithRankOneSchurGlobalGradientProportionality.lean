import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurAffineLineLogGradient
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# Stage 4B22: globalise the affine-line gradient ratios

Stage 4B21 proves that, for the logarithmic-gradient residual, every gradient
component is a scalar multiple of the chosen nonzero pivot component after
restriction to any affine line on which the pivot restriction is nonzero.

This file proves that the scalar is independent of the line.  Choose one
basepoint `a` where the pivot polynomial `P` is nonzero.  For an arbitrary
point `b`, use the line

    a + T (b - a).

Its restriction of `P` is nonzero because its value at `T = 0` is `P(a)`.
B21 therefore gives `Q|_line = c_b P|_line`.  Evaluation at `T = 0` forces

    c_b = Q(a) / P(a),

which is independent of `b`; evaluation at `T = 1` then gives the same
proportionality at `b`.  Function extensionality for multivariate polynomials
over the infinite characteristic-zero field upgrades pointwise equality to a
polynomial identity.

Thus the rank-one residual now carries constants `c_i` with

    ∂_i H = c_i ∂_r H

globally.  This is the exact input for the final linear-form-power
classification.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluate the affine-line specialisation at a scalar parameter. -/
@[simp] theorem eval_transverseAffineLineSpecialisation
    (a v : Fin 3 → K)
    (F : MvPolynomial (Fin 3) K)
    (t : K) :
    Polynomial.eval t (transverseAffineLineSpecialisation a v F) =
      MvPolynomial.eval (fun i => a i + v i * t) F := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [transverseAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    have hvar :
        Polynomial.eval t
            (transverseAffineLineSpecialisation a v (MvPolynomial.X i)) =
          MvPolynomial.eval (fun j => a j + v j * t) (MvPolynomial.X i) := by
      simp [transverseAffineLineSpecialisation]
    have hmul := congrArg₂ (fun x y : K => x * y) hp hvar
    simpa only [map_mul, Polynomial.eval_mul] using hmul

/-- The affine line through `a` in direction `b-a` starts at `a`. -/
@[simp] theorem eval_zero_transverseAffineLineSpecialisation_sub
    (a b : Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) :
    Polynomial.eval 0
        (transverseAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval a F := by
  rw [eval_transverseAffineLineSpecialisation]
  apply congrArg (fun x : Fin 3 → K => MvPolynomial.eval x F)
  funext i
  ring

/-- The affine line through `a` in direction `b-a` reaches `b` at `T=1`. -/
@[simp] theorem eval_one_transverseAffineLineSpecialisation_sub
    (a b : Fin 3 → K)
    (F : MvPolynomial (Fin 3) K) :
    Polynomial.eval 1
        (transverseAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval b F := by
  rw [eval_transverseAffineLineSpecialisation]
  apply congrArg (fun x : Fin 3 → K => MvPolynomial.eval x F)
  funext i
  ring

/-- A nonzero multivariate polynomial over the characteristic-zero field is
nonzero at some point.  This is the contrapositive of `MvPolynomial.funext`. -/
theorem exists_eval_ne_zero_of_ne_zero
    (P : MvPolynomial (Fin 3) K)
    (hP : P ≠ 0) :
    ∃ a : Fin 3 → K, MvPolynomial.eval a P ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hP
  apply MvPolynomial.funext
  intro a
  simp [hnone a]

/-- **Affine-line globalisation lemma.**

If every affine-line restriction of `Q` is a scalar multiple of the
corresponding restriction of a nonzero polynomial `P` whenever that pivot
restriction is nonzero, then `Q` is one fixed scalar multiple of `P`
globally. -/
theorem mvPolynomial_eq_C_mul_of_affineLine_proportional
    (P Q : MvPolynomial (Fin 3) K)
    (hP : P ≠ 0)
    (hline :
      ∀ (a v : Fin 3 → K),
        transverseAffineLineSpecialisation a v P ≠ 0 →
          ∃ c : K,
            transverseAffineLineSpecialisation a v Q =
              Polynomial.C c * transverseAffineLineSpecialisation a v P) :
    ∃ c : K, Q = MvPolynomial.C c * P := by
  classical
  rcases exists_eval_ne_zero_of_ne_zero P hP with ⟨a, ha⟩
  let c : K := MvPolynomial.eval a Q / MvPolynomial.eval a P
  refine ⟨c, ?_⟩
  apply MvPolynomial.funext
  intro b
  let v : Fin 3 → K := fun i => b i - a i
  have hPline : transverseAffineLineSpecialisation a v P ≠ 0 := by
    intro hzero
    have hzero0 := congrArg (Polynomial.eval (0 : K)) hzero
    have : MvPolynomial.eval a P = 0 := by
      simpa [v] using hzero0
    exact ha this
  rcases hline a v hPline with ⟨d, hd⟩
  have h0 : MvPolynomial.eval a Q = d * MvPolynomial.eval a P := by
    have h := congrArg (Polynomial.eval (0 : K)) hd
    simpa [v] using h
  have hd_eq : d = c := by
    dsimp [c]
    apply (eq_div_iff ha).2
    simpa using h0.symm
  have h1 : MvPolynomial.eval b Q = d * MvPolynomial.eval b P := by
    have h := congrArg (Polynomial.eval (1 : K)) hd
    simpa [v] using h
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simpa [hd_eq] using h1

namespace RankOneHomogeneousLogGradientData

/-- B21 globalised: every gradient component is one fixed scalar multiple of
the chosen pivot derivative as a multivariate polynomial. -/
theorem gradientComponent_global_proportional
    {H : MvPolynomial (Fin 3) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m)
    (i : Fin 3) :
    ∃ c : K,
      MvPolynomial.pderiv i H =
        MvPolynomial.C c * MvPolynomial.pderiv G.pivot H := by
  apply mvPolynomial_eq_C_mul_of_affineLine_proportional
      (MvPolynomial.pderiv G.pivot H)
      (MvPolynomial.pderiv i H)
      G.pivot_ne_zero
  intro a v hpivotLine
  exact G.affineLine_gradientComponent_proportional i a v hpivotLine

/-- Package all three global gradient ratios at once. -/
theorem gradient_global_proportional_family
    {H : MvPolynomial (Fin 3) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m) :
    ∃ c : Fin 3 → K,
      ∀ i : Fin 3,
        MvPolynomial.pderiv i H =
          MvPolynomial.C (c i) * MvPolynomial.pderiv G.pivot H := by
  classical
  choose c hc using fun i : Fin 3 => G.gradientComponent_global_proportional i
  exact ⟨c, hc⟩

end RankOneHomogeneousLogGradientData

/-- The exact global-gradient normal form left by the rank-one homogeneous
Hessian residual. -/
structure RankOneHomogeneousGlobalGradientData
    (H : MvPolynomial (Fin 3) K)
    (m : ℕ) where
  logGradient : RankOneHomogeneousLogGradientData H m
  ratio : Fin 3 → K
  proportional :
    ∀ i : Fin 3,
      MvPolynomial.pderiv i H =
        MvPolynomial.C (ratio i) *
          MvPolynomial.pderiv logGradient.pivot H

/-- Upgrade B19/B21's logarithmic-gradient data to global constant gradient
ratios. -/
theorem RankOneHomogeneousLogGradientData.toGlobalGradientData
    {H : MvPolynomial (Fin 3) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m) :
    Nonempty (RankOneHomogeneousGlobalGradientData H m) := by
  rcases G.gradient_global_proportional_family with ⟨c, hc⟩
  exact ⟨{
    logGradient := G
    ratio := c
    proportional := hc
  }⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-level B22 residual: retain the B19 rank-one packet and strengthen
its logarithmic-gradient data to exact global constant ratios. -/
structure FirstKeyRankOneGlobalGradientResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  residual : C.FirstKeyRankOneLogGradientResidualData D F
  globalGradient :
    RankOneHomogeneousGlobalGradientData
      D.transverseSourceProfile D.transverseDegree

/-- Upgrade the B19 residual using the B22 globalisation theorem. -/
theorem FirstKeyRankOneLogGradientResidualData.toGlobalGradientResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyRankOneLogGradientResidualData D F) :
    Nonempty (C.FirstKeyRankOneGlobalGradientResidualData D F) := by
  rcases R.logGradient.toGlobalGradientData with ⟨G⟩
  exact ⟨{
    residual := R
    globalGradient := G
  }⟩

/-- **Stage 4B22 global-gradient frontier.**

The early-Schur first key now has only three possibilities:

* transverse degree one;
* existing certified rank-two repair;
* degree at least two with every gradient component a global constant
  multiple of one nonzero pivot derivative.

The third branch is the direct input to the final `H = c L^m`
classification. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_rankTwoRepair_or_globalGradientResidual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyRankOneGlobalGradientResidualData D F) := by
  rcases D.degreeOne_or_rankTwoRepair_or_logGradientResidual F complexity with
    hdegree | hrepair | hres
  · exact Or.inl hdegree
  · exact Or.inr (Or.inl hrepair)
  · rcases hres with ⟨R⟩
    exact Or.inr (Or.inr R.toGlobalGradientResidualData)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
