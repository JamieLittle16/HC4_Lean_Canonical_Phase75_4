import HC4.Valuation.QuadraticTransverseCapRankThreeNilpotent
import HC4.Valuation.QuadraticTransverseCapSchurDriftEndpoints
import Mathlib.Tactic

/-!
# Generic-rank-three nilpotent interval drift on the marked axis

Once the rank-three transverse reciprocal is affine, write
M(x)=A(1+xN), with N³=0. The transverse-linear coefficient ODE
then has polynomial solution

  b'(x) = (I - 2xN + 3x²N²) v,

where v is the initial derivative vector.

Exact integration over the MARKED interval 0→1 gives

  b(1)-b(0) = (I-N+N²)v.

This module proves that the original marked transverse-gradient
collision makes v=0. The result consumes explicit polynomial
coefficient equations, not an abstract closing-state assumption.
The source ODE and reciprocal-affine adapter remain separate tasks.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The exact ordinary-polynomial integral over 0→1 of
a quadratic derivative in the nilpotent inverse normal form:
  b' = u - 2 v X + 3 w X².
Then b(1)-b(0)=u-v+w. -/
theorem quadraticTransverse_cubicDerivative_markedInterval
    (b : Polynomial K)
    (u v w : K)
    (hder :
      Polynomial.derivative b =
        Polynomial.C u -
          Polynomial.C (2 * v) * Polynomial.X +
          Polynomial.C (3 * w) * Polynomial.X ^ 2) :
    Polynomial.eval (1 : K) b -
      Polynomial.eval (0 : K) b = u - v + w := by
  let model : Polynomial K :=
    Polynomial.C u * Polynomial.X -
      Polynomial.C v * Polynomial.X ^ 2 +
      Polynomial.C w * Polynomial.X ^ 3
  have hmodel :
      Polynomial.derivative model =
        Polynomial.C u -
          Polynomial.C (2 * v) * Polynomial.X +
          Polynomial.C (3 * w) * Polynomial.X ^ 2 := by
    dsimp [model]
    simp [Polynomial.derivative_mul, Polynomial.derivative_X_pow_succ]
    simp only [map_ofNat]
    ring_nf
  have hzero :
      Polynomial.derivative (b - model) = 0 := by
    rw [map_sub, hder, hmodel]
    exact sub_self _
  have hconst :=
    Polynomial.eq_C_of_derivative_eq_zero hzero
  have heval :
      Polynomial.eval (1 : K) (b - model) =
        Polynomial.eval (0 : K) (b - model) := by
    rw [hconst]
    simp
  have hmodel1 : Polynomial.eval (1 : K) model = u - v + w := by
    simp [model]
  have hmodel0 : Polynomial.eval (0 : K) model = 0 := by
    simp [model]
  have heval' :
      Polynomial.eval (1 : K) b - (u - v + w) =
        Polynomial.eval (0 : K) b := by
    simpa [Polynomial.eval_sub, hmodel1, hmodel0] using heval
  linear_combination heval'

/-- **Rank-three transverse marked drift endpoint.**

When a 3x3 matrix N is cubic nilpotent and the actual
three transverse-linear source coefficient derivatives have
the affine-inverse solution form, collision at 0 and 1 forces
the entire constant initial transverse vector to vanish.

No invertibility assumption on I-N+N² is needed: the existing
two-sided inverse 1+N proves it automatically. -/
theorem quadraticTransverse_rankThree_nilpotentDrift_collision
    (N : Matrix (Fin 3) (Fin 3) K)
    (hN : N ^ 3 = 0)
    (b : Fin 3 → Polynomial K)
    (v : Fin 3 → K)
    (hder : ∀ i : Fin 3,
      Polynomial.derivative (b i) =
        Polynomial.C (v i) -
          Polynomial.C (2 * (N.mulVec v) i) * Polynomial.X +
          Polynomial.C (3 * ((N ^ 2).mulVec v) i) * Polynomial.X ^ 2)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    v = 0 := by
  have hdrift (i : Fin 3) :
      v i - (N.mulVec v) i +
        ((N ^ 2).mulVec v) i = 0 := by
    have h := quadraticTransverse_cubicDerivative_markedInterval
      (b i) (v i) ((N.mulVec v) i)
        (((N ^ 2).mulVec v) i) (hder i)
    rw [hcoll i] at h
    linear_combination -h
  have hmatrix : (1 - N + N ^ 2).mulVec v = 0 := by
    funext i
    simpa only [Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.zero_apply] using hdrift i
  have hinv := (cubicNilpotent_drift_twoSidedInverse N hN).2
  have h := congrArg (fun z : Fin 3 → K => (1 + N).mulVec z) hmatrix
  change (1 + N).mulVec ((1 - N + N ^ 2).mulVec v) =
    (1 + N).mulVec 0 at h
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact h

end

end HC4.Valuation
