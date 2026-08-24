import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLinearCornerElimination
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurConstantProjectiveKernel
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurUnivariateLogDerivativeRigidity
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Stage 4B27: vanishing projective wedges give a constant source direction

The remaining RS2/provenance theorem naturally produces infinitesimal
projective-motion expressions for the Stage-3 polynomial kernel vector

    W = D.fullVector : Fin 4 -> MvPolynomial (Fin 4) K.

The correct denominator-free expressions are the projective wedges

    W_i * d_k W_j - W_j * d_k W_i.

This file removes the global projectivisation problem once and for all.  If
all such wedges vanish and `W` is nonzero, choose one nonzero component `P`.
For every other component `Q` we have

    P * d_k Q = Q * d_k P

in all four source variables.  Restriction to an arbitrary affine line gives

    p q' = q p',

so the already-green Stage 4B20 univariate rigidity theorem makes `q` a
constant multiple of `p` on that line.  The Stage 4B22 basepoint argument,
repeated here in four variables, globalises the scalar.  Thus

    W_i = C(c_i) * P

for constants `c_i`.  Commutativity rewrites this in exactly the factor form
required by Stage 4A's `HasConstantProjectiveDirection` certificate.

Consequently the final source-to-Schur theorem no longer has to construct a
projective factorisation.  It only has to prove that every projective wedge
vanishes (or expose certified repair); this file turns wedge vanishing into
the honest constant source kernel already consumed by Stage 4A.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Four-variable affine-line specialisation -/

/-- Substitute the affine source line `X_i = a_i + v_i T`. -/
def sourceAffineLineSpecialisation
    (a v : Fin 4 → K) :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

@[simp] theorem sourceAffineLineSpecialisation_C
    (a v : Fin 4 → K) (c : K) :
    sourceAffineLineSpecialisation a v (MvPolynomial.C c) =
      Polynomial.C c := by
  simp [sourceAffineLineSpecialisation]

@[simp] theorem sourceAffineLineSpecialisation_X
    (a v : Fin 4 → K) (i : Fin 4) :
    sourceAffineLineSpecialisation a v (MvPolynomial.X i) =
      Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X := by
  simp [sourceAffineLineSpecialisation]

/-- Exact chain rule for four-variable affine-line substitution. -/
theorem derivative_sourceAffineLineSpecialisation
    (a v : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    (sourceAffineLineSpecialisation a v F).derivative =
      ∑ i : Fin 4,
        Polynomial.C (v i) *
          sourceAffineLineSpecialisation a v
            (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [sourceAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq, mul_add, Finset.sum_add_distrib]
  · intro p i hp
    simp only [map_mul, sourceAffineLineSpecialisation_X,
      Polynomial.derivative_mul, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases i <;> simp [Fin.sum_univ_succ] <;> ring

/-- A complete four-variable logarithmic-derivative cross system restricts
to the one-variable cross identity on every affine source line. -/
theorem sourceAffineLine_logDerivative_cross
    (P Q : MvPolynomial (Fin 4) K)
    (hcross :
      ∀ j : Fin 4,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 4 → K) :
    sourceAffineLineSpecialisation a v P *
        (sourceAffineLineSpecialisation a v Q).derivative =
      sourceAffineLineSpecialisation a v Q *
        (sourceAffineLineSpecialisation a v P).derivative := by
  rw [derivative_sourceAffineLineSpecialisation,
    derivative_sourceAffineLineSpecialisation]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmap := congrArg (sourceAffineLineSpecialisation a v) (hcross j)
  simp only [map_mul] at hmap
  calc
    sourceAffineLineSpecialisation a v P *
          (Polynomial.C (v j) *
            sourceAffineLineSpecialisation a v
              (MvPolynomial.pderiv j Q)) =
        Polynomial.C (v j) *
          (sourceAffineLineSpecialisation a v P *
            sourceAffineLineSpecialisation a v
              (MvPolynomial.pderiv j Q)) := by ring
    _ = Polynomial.C (v j) *
          (sourceAffineLineSpecialisation a v Q *
            sourceAffineLineSpecialisation a v
              (MvPolynomial.pderiv j P)) := by rw [hmap]
    _ = sourceAffineLineSpecialisation a v Q *
          (Polynomial.C (v j) *
            sourceAffineLineSpecialisation a v
              (MvPolynomial.pderiv j P)) := by ring

/-- B20 after four-variable affine-line restriction. -/
theorem sourceAffineLine_eq_C_mul_of_logDerivative_cross
    (P Q : MvPolynomial (Fin 4) K)
    (hcross :
      ∀ j : Fin 4,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 4 → K)
    (hPline : sourceAffineLineSpecialisation a v P ≠ 0) :
    ∃ c : K,
      sourceAffineLineSpecialisation a v Q =
        Polynomial.C c * sourceAffineLineSpecialisation a v P := by
  exact polynomial_eq_C_mul_of_logDerivative_cross
    (sourceAffineLineSpecialisation a v P)
    (sourceAffineLineSpecialisation a v Q)
    hPline
    (sourceAffineLine_logDerivative_cross P Q hcross a v)

/-! ## Globalise linewise proportionality in four variables -/

@[simp] theorem eval_sourceAffineLineSpecialisation
    (a v : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K)
    (t : K) :
    Polynomial.eval t (sourceAffineLineSpecialisation a v F) =
      MvPolynomial.eval (fun i => a i + v i * t) F := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [sourceAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    have hvar :
        Polynomial.eval t
            (sourceAffineLineSpecialisation a v (MvPolynomial.X i)) =
          MvPolynomial.eval (fun j => a j + v j * t)
            (MvPolynomial.X i) := by
      simp [sourceAffineLineSpecialisation]
    have hmul := congrArg₂ (fun x y : K => x * y) hp hvar
    simpa only [map_mul, Polynomial.eval_mul] using hmul

@[simp] theorem eval_zero_sourceAffineLineSpecialisation_sub
    (a b : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    Polynomial.eval 0
        (sourceAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval a F := by
  rw [eval_sourceAffineLineSpecialisation]
  apply congrArg (fun x : Fin 4 → K => MvPolynomial.eval x F)
  funext i
  ring

@[simp] theorem eval_one_sourceAffineLineSpecialisation_sub
    (a b : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    Polynomial.eval 1
        (sourceAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval b F := by
  rw [eval_sourceAffineLineSpecialisation]
  apply congrArg (fun x : Fin 4 → K => MvPolynomial.eval x F)
  funext i
  ring

/-- A nonzero four-variable polynomial is nonzero at some point. -/
theorem exists_source_eval_ne_zero_of_ne_zero
    (P : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0) :
    ∃ a : Fin 4 → K, MvPolynomial.eval a P ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hP
  apply MvPolynomial.funext
  intro a
  simp [hnone a]

/-- Four-variable version of the B22 globalisation lemma. -/
theorem mvPolynomial_fin4_eq_C_mul_of_affineLine_proportional
    (P Q : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0)
    (hline :
      ∀ (a v : Fin 4 → K),
        sourceAffineLineSpecialisation a v P ≠ 0 →
          ∃ c : K,
            sourceAffineLineSpecialisation a v Q =
              Polynomial.C c * sourceAffineLineSpecialisation a v P) :
    ∃ c : K, Q = MvPolynomial.C c * P := by
  classical
  rcases exists_source_eval_ne_zero_of_ne_zero P hP with ⟨a, ha⟩
  let c : K := MvPolynomial.eval a Q / MvPolynomial.eval a P
  refine ⟨c, ?_⟩
  apply MvPolynomial.funext
  intro b
  let v : Fin 4 → K := fun i => b i - a i
  have hPline : sourceAffineLineSpecialisation a v P ≠ 0 := by
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

/-- If `P ≠ 0` and every source partial logarithmic derivative of `Q/P`
vanishes, then `Q/P` is one constant globally. -/
theorem mvPolynomial_fin4_eq_C_mul_of_logDerivative_cross
    (P Q : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0)
    (hcross :
      ∀ j : Fin 4,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P) :
    ∃ c : K, Q = MvPolynomial.C c * P := by
  apply mvPolynomial_fin4_eq_C_mul_of_affineLine_proportional P Q hP
  intro a v hPline
  exact sourceAffineLine_eq_C_mul_of_logDerivative_cross
    P Q hcross a v hPline

/-! ## Projective constancy of the Stage-3 polynomial kernel -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- Denominator-free infinitesimal projective constancy: every pair of
components of the polynomial full kernel has zero source projective wedge in
every source direction. -/
def HasVanishingProjectiveWedges
    (D : DenominatorClearedSpecialSchurKernelData C) : Prop :=
  ∀ i j k : Fin 4,
    D.fullVector i * MvPolynomial.pderiv k (D.fullVector j) =
      D.fullVector j * MvPolynomial.pderiv k (D.fullVector i)

/-- A nonzero polynomial vector has a nonzero coordinate. -/
theorem exists_fullVector_coordinate_ne_zero
    (D : DenominatorClearedSpecialSchurKernelData C) :
    ∃ r : Fin 4, D.fullVector r ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply D.fullVector_ne_zero
  funext i
  exact hnone i

/-- **Stage 4B27 projective constancy theorem.**

Vanishing of all denominator-free projective wedges of the Stage-3 polynomial
kernel produces exactly the constant-projective-direction certificate consumed
by Stage 4A. -/
theorem hasConstantProjectiveDirection_of_vanishingProjectiveWedges
    (D : DenominatorClearedSpecialSchurKernelData C)
    (hwedges : D.HasVanishingProjectiveWedges) :
    Nonempty D.HasConstantProjectiveDirection := by
  classical
  rcases D.exists_fullVector_coordinate_ne_zero with ⟨r, hr⟩
  have hcomponent :
      ∀ i : Fin 4,
        ∃ c : K,
          D.fullVector i = MvPolynomial.C c * D.fullVector r := by
    intro i
    exact mvPolynomial_fin4_eq_C_mul_of_logDerivative_cross
      (D.fullVector r) (D.fullVector i) hr
      (fun k => hwedges r i k)
  choose c hc using hcomponent
  refine ⟨{
    scalar := D.fullVector r
    scalar_ne_zero := hr
    direction := c
    direction_ne_zero := ?_
    factor := ?_
  }⟩
  · intro hzero
    have hcr : c r = 0 := by
      exact congrFun hzero r
    have hrr := hc r
    rw [hcr] at hrr
    simp at hrr
    exact hr hrr
  · intro i
    simpa [mul_comm] using hc i

/-- Compose B27 with the already-green Stage 4A denominator cancellation. -/
theorem constantSpecialSourceKernel_of_vanishingProjectiveWedges
    (D : DenominatorClearedSpecialSchurKernelData C)
    (hwedges : D.HasVanishingProjectiveWedges) :
    Nonempty (ConstantSpecialSourceKernelData C) := by
  rcases D.hasConstantProjectiveDirection_of_vanishingProjectiveWedges
      hwedges with ⟨P⟩
  exact ⟨P.toConstantSpecialSourceKernelData⟩

end DenominatorClearedSpecialSchurKernelData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
