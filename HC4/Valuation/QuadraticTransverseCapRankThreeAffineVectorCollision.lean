import HC4.Valuation.QuadraticTransverseCapRankThreePolynomialAffineClosure
import Mathlib.Tactic

/-!
# Affine inverse and marked-vector collision

For a polynomially invertible matrix M(x), if M''=0 and
(M(x)b(x))''=0, equality b(0)=b(1) forces b to be constant.

This uses only affine polynomial interpolation at two points;
there is no nilpotence, explicit integration, or ODE uniqueness step.
The actual source Riccati identities supply the two second-derivative
conditions in the subsequent source adapter.
-/

namespace HC4.Valuation
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- An affine polynomial is determined by its values at 0 and 1. -/
theorem quadraticTransverse_affinePolynomial_eq_of_twoValues
    (p q : Polynomial K)
    (hp : Polynomial.derivative (Polynomial.derivative p) = 0)
    (hq : Polynomial.derivative (Polynomial.derivative q) = 0)
    (h0 : Polynomial.eval (0 : K) p = Polynomial.eval 0 q)
    (h1 : Polynomial.eval (1 : K) p = Polynomial.eval 1 q) :
    p = q := by
  have hsecond :
      Polynomial.derivative (Polynomial.derivative (p - q)) = 0 := by
    rw [map_sub, map_sub, hp, hq, sub_self]
  obtain ⟨a, b, hform⟩ :=
    quadraticTransverse_polynomial_secondDerivative_zero_affine
      (p - q) hsecond
  have hzero : Polynomial.eval (0 : K) (p - q) = 0 := by
    rw [Polynomial.eval_sub, sub_eq_zero]
    exact h0
  have hone : Polynomial.eval (1 : K) (p - q) = 0 := by
    rw [Polynomial.eval_sub, sub_eq_zero]
    exact h1
  have ha : a = 0 := by
    simpa [hform] using hzero
  have hb : b = 0 := by
    simpa [hform, ha] using hone
  have hdiff : p - q = 0 := by
    simp [hform, ha, hb]
  exact sub_eq_zero.mp hdiff

/-- Matrix-vector polynomial differentiation. -/
def quadraticTransverse_polynomialVectorDerivative
    (v : Fin 3 → Polynomial K) : Fin 3 → Polynomial K :=
  fun i => Polynomial.derivative (v i)

/-- The vector derivative commutes with addition. -/
theorem quadraticTransverse_polynomialVectorDerivative_add
    (v w : Fin 3 → Polynomial K) :
    quadraticTransverse_polynomialVectorDerivative (v + w) =
      quadraticTransverse_polynomialVectorDerivative v +
        quadraticTransverse_polynomialVectorDerivative w := by
  funext i
  simp [quadraticTransverse_polynomialVectorDerivative]

/-- Product rule for a polynomial matrix acting on a polynomial vector. -/
theorem quadraticTransverse_polynomialVectorDerivative_mulVec
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (v : Fin 3 → Polynomial K) :
    quadraticTransverse_polynomialVectorDerivative (M.mulVec v) =
      (quadraticTransverse_polynomialMatrixDerivative M).mulVec v +
        M.mulVec (quadraticTransverse_polynomialVectorDerivative v) := by
  funext i
  change
    Polynomial.derivative (∑ j : Fin 3, M i j * v j) =
      (∑ j : Fin 3, Polynomial.derivative (M i j) * v j) +
        (∑ j : Fin 3, M i j * Polynomial.derivative (v j))
  rw [map_sum]
  simp_rw [Polynomial.derivative_mul]
  exact Finset.sum_add_distrib

/-- **Rank-three affine-matrix collision rigidity.**

For M a polynomial matrix with a polynomial left inverse C, if
every entry of M and M*b has zero second derivative, the two equal
marked values of b force b'=0. -/
theorem quadraticTransverse_affineMatrixVector_markedCollision_zero
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (b : Fin 3 → Polynomial K)
    (hMaffine : ∀ i j : Fin 3,
      Polynomial.derivative (Polynomial.derivative (M i j)) = 0)
    (hMbaffine : ∀ i : Fin 3,
      Polynomial.derivative (Polynomial.derivative (M.mulVec b i)) = 0)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    ∀ i : Fin 3, Polynomial.derivative (b i) = 0 := by
  classical
  let v₀ : Fin 3 → K := fun i => Polynomial.eval 0 (b i)
  let vconst : Fin 3 → Polynomial K := fun i => Polynomial.C (v₀ i)
  have hconstSecond (i : Fin 3) :
      Polynomial.derivative (Polynomial.derivative
        (M.mulVec vconst i)) = 0 := by
    change Polynomial.derivative (Polynomial.derivative
      (∑ j : Fin 3, M i j * Polynomial.C (v₀ j))) = 0
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
      mul_zero, add_zero, hMaffine i j, zero_mul]
  have heval (t : K) (w : Fin 3 → Polynomial K) (i : Fin 3) :
      Polynomial.eval t (M.mulVec w i) =
        ∑ j : Fin 3,
          Polynomial.eval t (M i j) * Polynomial.eval t (w j) := by
    change (Polynomial.evalRingHom t)
        (∑ j : Fin 3, M i j * w j) =
      ∑ j : Fin 3,
        (Polynomial.evalRingHom t) (M i j) *
          (Polynomial.evalRingHom t) (w j)
    simp only [map_sum, map_mul]
  have hevalEq (t : K)
      (ht : ∀ j : Fin 3, Polynomial.eval t (b j) = v₀ j)
      (i : Fin 3) :
      Polynomial.eval t (M.mulVec b i) =
        Polynomial.eval t (M.mulVec vconst i) := by
    rw [heval t b i, heval t vconst i]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht j]
    simp [vconst]
  have hzero (i : Fin 3) :
      Polynomial.eval (0 : K) (M.mulVec b i) =
        Polynomial.eval 0 (M.mulVec vconst i) :=
    hevalEq 0 (fun j => rfl) i
  have hone (i : Fin 3) :
      Polynomial.eval (1 : K) (M.mulVec b i) =
        Polynomial.eval 1 (M.mulVec vconst i) :=
    hevalEq 1 hcoll i
  have hMb : M.mulVec b = M.mulVec vconst := by
    funext i
    exact quadraticTransverse_affinePolynomial_eq_of_twoValues
      (M.mulVec b i) (M.mulVec vconst i)
      (hMbaffine i) (hconstSecond i) (hzero i) (hone i)
  have hb : b = vconst := by
    have h := congrArg (fun w : Fin 3 → Polynomial K => C.mulVec w) hMb
    change C.mulVec (M.mulVec b) = C.mulVec (M.mulVec vconst) at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    rw [hCM] at h
    simpa only [Matrix.one_mulVec] using h
  intro i
  rw [congrFun hb i]
  simp [vconst]

end
end HC4.Valuation
