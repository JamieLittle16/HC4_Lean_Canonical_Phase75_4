import HC4.Polynomial.RankThreeCubicAdditiveDichotomy
import Mathlib.Tactic

/-!
# Globalising the full-kernel-or-zero-block dichotomy for a Hessian pencil

Let B(u,v)=u*A+v*C be an arbitrary 3x3 linear matrix pencil.
Suppose that at every point either its lower-right 2x2 block
is zero, or its normal row kills the same fixed tangent vector
(0,r,t). Those two conditions define kernels of *additive* maps
K² -> K³ and K² -> K. The additive zero-set dichotomy proves
that one alternative holds on the entire plane.

This is pure pencil linear algebra and does not assume that
the matrix pencil comes from a Hessian. Source-specific tensor
integrability is needed only to produce this linear pencil and
its pointwise dichotomy.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- For a two-parameter linear 3x3 pencil, a pointwise
zero-tangent-block or full-tangent-kernel alternative is
automatically a *uniform* alternative on the whole plane. -/
theorem linearMatrixPencil_zeroTangentBlock_or_normalKernel_global
    {K : Type*} [Field K]
    (A C : Matrix (Fin 3) (Fin 3) K)
    (r t : K)
    (hpoint : ∀ u v : K,
      let B := u • A + v • C
      (B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0) ∨
        (B 0 1 * r + B 0 2 * t = 0)) :
    (∀ u v : K,
      let B := u • A + v • C
      B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0) ∨
    (∀ u v : K,
      let B := u • A + v • C
      B 0 1 * r + B 0 2 * t = 0) := by
  classical
  let P : (K × K) → Matrix (Fin 3) (Fin 3) K :=
    fun x => x.1 • A + x.2 • C
  let f : (K × K) → (Fin 3 → K) :=
    fun x => ![P x 1 1, P x 1 2, P x 2 2]
  let g : (K × K) → K :=
    fun x => P x 0 1 * r + P x 0 2 * t
  have hPadd (x y : K × K) :
      P (x + y) = P x + P y := by
    ext i j
    simp [P, Matrix.smul_apply, Matrix.add_apply, add_mul]
    ring
  have hfadd (x y : K × K) :
      f (x + y) = f x + f y := by
    have hp := hPadd x y
    funext i
    fin_cases i <;>
      simp [f, hp, Matrix.add_apply]
  have hgadd (x y : K × K) :
      g (x + y) = g x + g y := by
    change P (x + y) 0 1 * r + P (x + y) 0 2 * t =
      (P x 0 1 * r + P x 0 2 * t) +
        (P y 0 1 * r + P y 0 2 * t)
    rw [hPadd x y]
    simp only [Matrix.add_apply]
    ring
  have hpoint' (x : K × K) : f x = 0 ∨ g x = 0 := by
    rcases hpoint x.1 x.2 with hQ | hw
    · left
      funext i
      fin_cases i
      · simpa [f, P] using hQ.1
      · simpa [f, P] using hQ.2.1
      · simpa [f, P] using hQ.2.2
    · exact Or.inr hw
  rcases additiveMaps_pointwiseEitherZero_implies_globalEitherZero
      f g hfadd hgadd hpoint' with hfzero | hgzero
  · left
    intro u v
    have h := hfzero (u, v)
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    exact ⟨by simpa [f, P] using h0,
      by simpa [f, P] using h1,
      by simpa [f, P] using h2⟩
  · right
    intro u v
    exact hgzero (u, v)

end
end HC4.Polynomial.RankThreeCubic
