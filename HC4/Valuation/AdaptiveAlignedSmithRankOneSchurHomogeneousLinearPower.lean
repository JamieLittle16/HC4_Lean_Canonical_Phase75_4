import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurGlobalGradientProportionality
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Stage 4B23: homogeneous global-gradient rigidity gives a linear-form power

Stage 4B22 leaves the rank-one transverse first-key residual in the exact
constant-gradient-ratio form

    ∂_i H = c_i ∂_r H

for one nonzero pivot derivative `∂_r H` and every transverse coordinate.

This file closes that algebraic residual without introducing a coordinate
change.  Put

    L = sum_i c_i X_i,
    P = ∂_r H.

Euler's identity for a homogeneous degree-`m` form gives

    L P = m H.

Mixed partial commutation shows that `P` has the same constant gradient
ratios.  Thus one can induct on the homogeneous degree.  In degree one the
pivot derivative is homogeneous of degree zero and hence constant.  In the
inductive step, `P` is a scalar multiple of `L^(m-1)` and Euler reconstructs
`H` as a scalar multiple of `L^m`.

This is the missing homogeneous rank-one classification:

    H = a * L^m.

The carrier theorem below consumes the B22 global-gradient residual and
packages precisely this normal form.  The degree-one branch remains separate
only because it enters the frontier before the rank-one residual is built;
it will be folded into the same `L^1` form in the next assembly adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- The linear form canonically determined by global gradient ratios. -/
noncomputable def gradientRatioLinearForm
    {n : ℕ}
    (c : Fin n → K) : MvPolynomial (Fin n) K :=
  ∑ i : Fin n, MvPolynomial.C (c i) * MvPolynomial.X i

/-- A homogeneous degree-zero multivariate polynomial is constant.

This is the `Fin n` version of the already-used HC4 support argument from the
terminal scalar-gradient machinery. -/
theorem homogeneous_zero_eq_C_constantCoeff_fin
    {n : ℕ}
    {P : MvPolynomial (Fin n) K}
    (hzero : P.IsHomogeneous 0) :
    P = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · subst d
    have hconst :
        MvPolynomial.constantCoeff P = MvPolynomial.coeff 0 P := by
      exact
        congrArg
          (fun f : MvPolynomial (Fin n) K → K => f P)
          MvPolynomial.constantCoeff_eq
    simp [hconst]
  · have hdeg : Finsupp.degree d ≠ 0 := by
      intro hdegree
      exact hd ((Finsupp.degree_eq_zero_iff d).mp hdegree)
    have hcoeff : MvPolynomial.coeff d P = 0 :=
      hzero.coeff_eq_zero hdeg
    simp [hcoeff, hd, Ne.symm hd]

/-- Euler's identity after substituting the global gradient ratios.

If `P = ∂_r H` and every `∂_i H = c_i P`, then

    (sum_i c_i X_i) P = m H.
-/
theorem gradientRatioLinearForm_mul_pivot_eq_degree_mul
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (r : Fin n)
    (c : Fin n → K)
    (hprop :
      ∀ i : Fin n,
        MvPolynomial.pderiv i H =
          MvPolynomial.C (c i) * MvPolynomial.pderiv r H) :
    gradientRatioLinearForm c * MvPolynomial.pderiv r H =
      MvPolynomial.C (m : K) * H := by
  classical
  have heuler := hhom.sum_X_mul_pderiv
  calc
    gradientRatioLinearForm c * MvPolynomial.pderiv r H =
        ∑ i : Fin n,
          (MvPolynomial.C (c i) * MvPolynomial.X i) *
            MvPolynomial.pderiv r H := by
              rw [gradientRatioLinearForm, Finset.sum_mul]
    _ = ∑ i : Fin n,
          MvPolynomial.X i * MvPolynomial.pderiv i H := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hprop i]
            ring
    _ = MvPolynomial.C (m : K) * H := by
          simpa using heuler

/-- The pivot derivative inherits the same global gradient ratios.

This is just differentiation of `∂_i H = c_i ∂_r H` in the pivot direction,
followed by commutation of mixed formal partial derivatives. -/
theorem pivotDerivative_gradientRatio
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (r : Fin n)
    (c : Fin n → K)
    (hprop :
      ∀ i : Fin n,
        MvPolynomial.pderiv i H =
          MvPolynomial.C (c i) * MvPolynomial.pderiv r H) :
    ∀ i : Fin n,
      MvPolynomial.pderiv i (MvPolynomial.pderiv r H) =
        MvPolynomial.C (c i) *
          MvPolynomial.pderiv r (MvPolynomial.pderiv r H) := by
  intro i
  have hd := congrArg (MvPolynomial.pderiv r) (hprop i)
  calc
    MvPolynomial.pderiv i (MvPolynomial.pderiv r H) =
        MvPolynomial.pderiv r (MvPolynomial.pderiv i H) :=
      pderiv_comm_backport i r H
    _ = MvPolynomial.C (c i) *
          MvPolynomial.pderiv r (MvPolynomial.pderiv r H) := by
      simpa [MvPolynomial.pderiv_C_mul] using hd

/-- If a positive-degree homogeneous polynomial has all of its partials
proportional to one chosen partial, then that chosen partial cannot vanish.

This is the small induction-safety lemma needed after differentiating the
pivot once more. -/
theorem pivot_pderiv_ne_zero_of_globalGradientRatio
    {n : ℕ}
    (P : MvPolynomial (Fin n) K)
    (d : ℕ)
    (hhom : P.IsHomogeneous d)
    (hP : P ≠ 0)
    (hd : 0 < d)
    (r : Fin n)
    (c : Fin n → K)
    (hprop :
      ∀ i : Fin n,
        MvPolynomial.pderiv i P =
          MvPolynomial.C (c i) * MvPolynomial.pderiv r P) :
    MvPolynomial.pderiv r P ≠ 0 := by
  intro hr
  rcases homogeneous_exists_pderiv_ne_zero P d hhom hP hd with ⟨i, hi⟩
  have hizero : MvPolynomial.pderiv i P = 0 := by
    rw [hprop i, hr]
    simp
  exact hi hizero

/-- **Homogeneous constant-gradient-ratio classification.**

A nonzero pivot derivative together with homogeneous degree `m > 0` and
constant global gradient ratios forces the polynomial to be a scalar
multiple of the `m`-th power of the corresponding linear form. -/
theorem homogeneous_eq_C_mul_gradientRatioLinearForm_pow
    {n : ℕ}
    (m : ℕ) :
    ∀ (H : MvPolynomial (Fin n) K),
      H.IsHomogeneous m →
      0 < m →
      ∀ (r : Fin n),
        MvPolynomial.pderiv r H ≠ 0 →
        ∀ (c : Fin n → K),
          (∀ i : Fin n,
            MvPolynomial.pderiv i H =
              MvPolynomial.C (c i) * MvPolynomial.pderiv r H) →
          ∃ a : K,
            H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro H hhom hmpos r hpivot c hprop
      by_cases hm1 : m = 1
      · subst m
        let P : MvPolynomial (Fin n) K := MvPolynomial.pderiv r H
        have hPhom : P.IsHomogeneous 0 := by
          dsimp [P]
          simpa using hhom.pderiv
        have hPconst : P = MvPolynomial.C (MvPolynomial.constantCoeff P) :=
          homogeneous_zero_eq_C_constantCoeff_fin hPhom
        have heuler :=
          gradientRatioLinearForm_mul_pivot_eq_degree_mul
            H 1 hhom r c hprop
        refine ⟨MvPolynomial.constantCoeff P, ?_⟩
        rw [show MvPolynomial.pderiv r H = P by rfl, hPconst] at heuler
        simp only [Nat.cast_one, MvPolynomial.C_1, one_mul] at heuler
        calc
          H = gradientRatioLinearForm c *
                MvPolynomial.C (MvPolynomial.constantCoeff P) := heuler.symm
          _ = MvPolynomial.C (MvPolynomial.constantCoeff P) *
                (gradientRatioLinearForm c) ^ 1 := by
              simp [pow_one, mul_comm]
      · have hm2 : 2 ≤ m := by omega
        have hpredpos : 0 < m - 1 := by omega
        let P : MvPolynomial (Fin n) K := MvPolynomial.pderiv r H
        have hPhom : P.IsHomogeneous (m - 1) := by
          dsimp [P]
          simpa using hhom.pderiv
        have hPne : P ≠ 0 := by
          simpa [P] using hpivot
        have hPprop :
            ∀ i : Fin n,
              MvPolynomial.pderiv i P =
                MvPolynomial.C (c i) * MvPolynomial.pderiv r P := by
          intro i
          dsimp [P]
          exact pivotDerivative_gradientRatio H r c hprop i
        have hPrne : MvPolynomial.pderiv r P ≠ 0 :=
          pivot_pderiv_ne_zero_of_globalGradientRatio
            P (m - 1) hPhom hPne hpredpos r c hPprop
        have hlt : m - 1 < m := by omega
        rcases ih (m - 1) hlt P hPhom hpredpos r hPrne c hPprop with ⟨a, ha⟩
        have heuler :=
          gradientRatioLinearForm_mul_pivot_eq_degree_mul
            H m hhom r c hprop
        have hpow :
            (gradientRatioLinearForm c) ^ (m - 1) * gradientRatioLinearForm c =
              (gradientRatioLinearForm c) ^ m := by
          rw [← pow_succ]
          congr 1
          omega
        have hdegree :
            MvPolynomial.C (m : K) * H =
              MvPolynomial.C a * (gradientRatioLinearForm c) ^ m := by
          calc
            MvPolynomial.C (m : K) * H =
                gradientRatioLinearForm c * P := heuler.symm
            _ = gradientRatioLinearForm c *
                  (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (m - 1)) := by
                rw [ha]
            _ = MvPolynomial.C a *
                  ((gradientRatioLinearForm c) ^ (m - 1) * gradientRatioLinearForm c) := by
                ring
            _ = MvPolynomial.C a * (gradientRatioLinearForm c) ^ m := by
                rw [hpow]
        have hmK : (m : K) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hmpos)
        refine ⟨a / (m : K), ?_⟩
        have hunit :
            MvPolynomial.C ((m : K)⁻¹) * MvPolynomial.C (m : K) =
              (1 : MvPolynomial (Fin n) K) := by
          rw [← MvPolynomial.C_mul]
          simp [hmK]
        calc
          H = 1 * H := by simp
          _ = (MvPolynomial.C ((m : K)⁻¹) * MvPolynomial.C (m : K)) * H := by
              rw [hunit]
          _ = MvPolynomial.C ((m : K)⁻¹) *
                (MvPolynomial.C (m : K) * H) := by
              rw [mul_assoc]
          _ = MvPolynomial.C ((m : K)⁻¹) *
                (MvPolynomial.C a * (gradientRatioLinearForm c) ^ m) := by
              rw [hdegree]
          _ = MvPolynomial.C ((m : K)⁻¹ * a) *
                (gradientRatioLinearForm c) ^ m := by
              rw [← mul_assoc, ← MvPolynomial.C_mul]
          _ = MvPolynomial.C (a / (m : K)) *
                (gradientRatioLinearForm c) ^ m := by
              rw [show (m : K)⁻¹ * a = a / (m : K) by
                simp [div_eq_mul_inv, mul_comm]]

/-- The exact normal form of the B22 rank-one global-gradient residual. -/
structure RankOneHomogeneousLinearPowerData
    (H : MvPolynomial (Fin 3) K)
    (m : ℕ) where
  ratio : Fin 3 → K
  coefficient : K
  eq_power :
    H = MvPolynomial.C coefficient * (gradientRatioLinearForm ratio) ^ m

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-level B23 residual: the rank-at-most-one homogeneous transverse
profile is now an actual scalar times a power of one linear form. -/
structure FirstKeyRankOneLinearPowerResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  globalResidual : C.FirstKeyRankOneGlobalGradientResidualData D F
  linearPower :
    RankOneHomogeneousLinearPowerData
      D.transverseSourceProfile D.transverseDegree

/-- Upgrade the B22 residual to the exact `H = a L^m` normal form. -/
theorem FirstKeyRankOneGlobalGradientResidualData.toLinearPowerResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyRankOneGlobalGradientResidualData D F) :
    Nonempty (C.FirstKeyRankOneLinearPowerResidualData D F) := by
  let G := R.globalGradient
  rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
      D.transverseDegree
      D.transverseSourceProfile
      D.transverseSourceProfile_homogeneous
      D.transverseDegree_pos
      G.logGradient.pivot
      G.logGradient.pivot_ne_zero
      G.ratio
      G.proportional with ⟨a, ha⟩
  exact ⟨{
    globalResidual := R
    linearPower := {
      ratio := G.ratio
      coefficient := a
      eq_power := ha
    }
  }⟩

/-- **Stage 4B23 linear-power frontier.**

After the existing rank-two repair branch, the degree-at-least-two rank-one
residual is no longer merely singular: its homogeneous transverse source
profile is exactly a scalar multiple of a power of one linear form.
-/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_rankTwoRepair_or_linearPowerResidual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyRankOneLinearPowerResidualData D F) := by
  rcases D.degreeOne_or_rankTwoRepair_or_globalGradientResidual F complexity with
    hdegree | hrepair | hres
  · exact Or.inl hdegree
  · exact Or.inr (Or.inl hrepair)
  · rcases hres with ⟨R⟩
    exact Or.inr (Or.inr R.toLinearPowerResidualData)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
