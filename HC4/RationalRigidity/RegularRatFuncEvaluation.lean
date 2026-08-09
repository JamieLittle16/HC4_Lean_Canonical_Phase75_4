import HC4.RationalRigidity.LogarithmicSourceRegularity
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

/-!
# Regular evaluation of polynomial expressions in a rational function

`RatFunc.eval` is intentionally not a ring homomorphism at points where a
reduced denominator vanishes.  For the autonomous ODE pole-removal argument we
only evaluate on the finite source chart, where the reduced source denominator
is nonzero.  On that chart polynomial expressions in the source rational
function are regular and evaluation behaves exactly as ordinary polynomial
evaluation.

This file packages that fact without introducing projective geometry.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- A rational function is regular at `x` when its canonical denominator does
not vanish there. -/
def RatFuncRegularAt (x : K) (r : RatFunc K) : Prop :=
  r.denom.eval x ≠ 0

/-- If `A` divides `B` and `B(x)` is nonzero, then `A(x)` is nonzero. -/
theorem eval_ne_zero_of_dvd
    {A B : Polynomial K} {x : K}
    (hAB : A ∣ B) (hB : B.eval x ≠ 0) :
    A.eval x ≠ 0 := by
  rcases hAB with ⟨C, rfl⟩
  intro hA
  apply hB
  simp [hA]

/-- Polynomial rational functions are regular everywhere. -/
theorem ratFuncRegularAt_algebraMap
    (x : K) (P : Polynomial K) :
    RatFuncRegularAt x ((algebraMap (Polynomial K) (RatFunc K)) P) := by
  unfold RatFuncRegularAt
  simp

/-- Regularity is preserved by addition. -/
theorem ratFuncRegularAt_add
    {x : K} {r s : RatFunc K}
    (hr : RatFuncRegularAt x r)
    (hs : RatFuncRegularAt x s) :
    RatFuncRegularAt x (r + s) := by
  unfold RatFuncRegularAt at hr hs ⊢
  apply eval_ne_zero_of_dvd (RatFunc.denom_add_dvd r s)
  simp [hr, hs]

/-- Regularity is preserved by multiplication. -/
theorem ratFuncRegularAt_mul
    {x : K} {r s : RatFunc K}
    (hr : RatFuncRegularAt x r)
    (hs : RatFuncRegularAt x s) :
    RatFuncRegularAt x (r * s) := by
  unfold RatFuncRegularAt at hr hs ⊢
  apply eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd r s)
  simp [hr, hs]

/-- Regularity is preserved by natural powers. -/
theorem ratFuncRegularAt_pow
    {x : K} {r : RatFunc K}
    (hr : RatFuncRegularAt x r) :
    ∀ n : ℕ, RatFuncRegularAt x (r ^ n) := by
  intro n
  induction n with
  | zero =>
      simpa using ratFuncRegularAt_algebraMap x (1 : Polynomial K)
  | succ n ih =>
      rw [pow_succ]
      exact ratFuncRegularAt_mul ih hr

/-- On a regular chart, every polynomial expression in `r` remains regular and
`RatFunc.eval` agrees with ordinary polynomial evaluation at the scalar value
of `r`.

Both conclusions are proved simultaneously so the induction hypotheses supply
exactly the denominator certificates needed by `RatFunc.eval_add` and
`RatFunc.eval_mul`. -/
theorem ratFuncRegularAt_aeval_and_eval
    {x : K} {r : RatFunc K}
    (hr : RatFuncRegularAt x r) (P : Polynomial K) :
    RatFuncRegularAt x (Polynomial.aeval r P) ∧
      RatFunc.eval (RingHom.id K) x (Polynomial.aeval r P) =
        P.eval (RatFunc.eval (RingHom.id K) x r) := by
  refine Polynomial.induction_on P ?_ ?_ ?_
  · intro a
    constructor
    · simpa using ratFuncRegularAt_algebraMap x (Polynomial.C a)
    · simp
  · intro p q hp hq
    constructor
    · simpa only [map_add] using ratFuncRegularAt_add hp.1 hq.1
    · rw [map_add]
      rw [RatFunc.eval_add (RingHom.id K) x
        (by simpa using hp.1) (by simpa using hq.1)]
      rw [hp.2, hq.2]
      simp
  · intro n a hn
    have hpoly :
        Polynomial.C a * Polynomial.X ^ (n + 1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ]
      ring
    constructor
    · rw [hpoly, map_mul]
      simpa using ratFuncRegularAt_mul hn.1 hr
    · rw [hpoly, map_mul]
      rw [RatFunc.eval_mul (RingHom.id K) x
        (by simpa using hn.1) (by simpa using hr)]
      rw [hn.2]
      simp

/-- Polynomial substitution preserves regularity on a regular chart. -/
theorem ratFuncRegularAt_aeval
    {x : K} {r : RatFunc K}
    (hr : RatFuncRegularAt x r) (P : Polynomial K) :
    RatFuncRegularAt x (Polynomial.aeval r P) :=
  (ratFuncRegularAt_aeval_and_eval hr P).1

/-- Evaluation commutes with polynomial substitution on a regular chart. -/
theorem ratFunc_eval_aeval
    {x : K} {r : RatFunc K}
    (hr : RatFuncRegularAt x r) (P : Polynomial K) :
    RatFunc.eval (RingHom.id K) x (Polynomial.aeval r P) =
      P.eval (RatFunc.eval (RingHom.id K) x r) :=
  (ratFuncRegularAt_aeval_and_eval hr P).2

/-- The canonical scalar value of a regular rational function is its reduced
numerator divided by its reduced denominator. -/
theorem ratFunc_eval_eq_num_div_denom
    {x : K} {r : RatFunc K} :
    RatFunc.eval (RingHom.id K) x r =
      r.num.eval x / r.denom.eval x := by
  simp [RatFunc.eval]

end

end HC4.RationalRigidity
