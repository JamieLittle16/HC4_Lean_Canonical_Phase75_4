import HC4.Valuation.QuadraticTransverseCapRankThreePolynomialAffineClosure
import Mathlib.Tactic

/-!
# Affine transverse vector collision: a shortcut through second derivatives

The rank-three mixed-vector equation can be multiplied by the affine
reciprocal to show that (T b)''=0, where T=1+X N is a polynomial
matrix with a polynomial left inverse.

Two affine polynomial vectors with identical values at X=0 and X=1
are identical. Therefore the actual marked collision b(0)=b(1)
forces b to be constant, with no nilpotent slope, explicit integration,
or first-order ODE uniqueness theorem required.
-/

namespace HC4.Valuation
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Over a characteristic-zero field an affine polynomial is
determined by its values at zero and one. -/
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

/-- **Affine-vector collision rigidity.**

Here T=I+XN, U*T=I, and every entry of T*b has zero
second derivative.  If b(0)=b(1), then b is constant.

In particular, this statement does NOT need N³=0. -/
theorem quadraticTransverse_affineVector_twoValues_constant
    (N : Matrix (Fin 3) (Fin 3) K)
    (U : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (hUT :
      U * (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C) = 1)
    (hsecond : ∀ i : Fin 3,
      Polynomial.derivative (Polynomial.derivative
        ((1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C).mulVec b i)) = 0)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    ∀ i : Fin 3, Polynomial.derivative (b i) = 0 := by
  classical
  let T : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C
  let v₀ : Fin 3 → K := fun i => Polynomial.eval 0 (b i)
  let vconst : Fin 3 → Polynomial K := fun i => Polynomial.C (v₀ i)
  have hconstSecond (i : Fin 3) :
      Polynomial.derivative (Polynomial.derivative
        (T.mulVec vconst i)) = 0 := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp [T, vconst, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, smul_eq_mul,
      Polynomial.derivative_mul]
  have heval (t : K) (w : Fin 3 → Polynomial K) (i : Fin 3) :
      Polynomial.eval t (T.mulVec w i) =
        ∑ j : Fin 3,
          Polynomial.eval t (T i j) * Polynomial.eval t (w j) := by
    change (Polynomial.evalRingHom t)
        (∑ j : Fin 3, T i j * w j) =
      ∑ j : Fin 3,
        (Polynomial.evalRingHom t) (T i j) *
          (Polynomial.evalRingHom t) (w j)
    simp only [map_sum, map_mul]
  have hevalEq (t : K)
      (ht : ∀ j : Fin 3, Polynomial.eval t (b j) = v₀ j)
      (i : Fin 3) :
      Polynomial.eval t (T.mulVec b i) =
        Polynomial.eval t (T.mulVec vconst i) := by
    rw [heval t b i, heval t vconst i]
    apply Finset.sum_congr rfl
    intro j _
    rw [ht j]
    simp [vconst]
  have hzero (i : Fin 3) :
      Polynomial.eval (0 : K) (T.mulVec b i) =
        Polynomial.eval 0 (T.mulVec vconst i) :=
    hevalEq 0 (fun j => rfl) i
  have hone (i : Fin 3) :
      Polynomial.eval (1 : K) (T.mulVec b i) =
        Polynomial.eval 1 (T.mulVec vconst i) :=
    hevalEq 1 hcoll i
  have hTb : T.mulVec b = T.mulVec vconst := by
    funext i
    exact quadraticTransverse_affinePolynomial_eq_of_twoValues
      (T.mulVec b i) (T.mulVec vconst i)
      (hsecond i) (hconstSecond i) (hzero i) (hone i)
  have hb : b = vconst := by
    have h := congrArg (fun w : Fin 3 → Polynomial K => U.mulVec w) hTb
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    change (U * T).mulVec b = (U * T).mulVec vconst at h
    rw [hUT, Matrix.one_mulVec] at h
    exact h
  intro i
  rw [congrFun hb i]
  simp [vconst]


/-- Entrywise polynomial-vector differentiation. -/
private def dvec (w : Fin 3 → Polynomial K) : Fin 3 → Polynomial K :=
  fun i => Polynomial.derivative (w i)

private theorem dvec_add (v w : Fin 3 → Polynomial K) :
    dvec (v + w) = dvec v + dvec w := by
  funext i
  simp [dvec]

/-- Product rule for a polynomial matrix acting on a polynomial vector. -/
private theorem dvec_mulVec
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (w : Fin 3 → Polynomial K) :
    dvec (M.mulVec w) =
      (quadraticTransverse_polynomialMatrixDerivative M).mulVec w +
        M.mulVec (dvec w) := by
  funext i
  change
    Polynomial.derivative (∑ j : Fin 3, M i j * w j) =
      (∑ j : Fin 3, Polynomial.derivative (M i j) * w j) +
        (∑ j : Fin 3, M i j * Polynomial.derivative (w j))
  rw [map_sum]
  simp_rw [Polynomial.derivative_mul]
  exact Finset.sum_add_distrib

/-- The derivative of I + X N is the constant matrix N. -/
private theorem dmat_affineN
    (N : Matrix (Fin 3) (Fin 3) K) :
    quadraticTransverse_polynomialMatrixDerivative
      (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C) =
        N.map Polynomial.C := by
  ext i j
  simp [quadraticTransverse_polynomialMatrixDerivative,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply, Polynomial.derivative_mul]

/-- **Affine-vector ODE closure.** The first-order coefficient equation
T*b'' = -2N*b' is sufficient to make (T*b)'' vanish.  Consequently
a polynomially invertible T and the marked collision make b constant.

No nilpotence or explicit ODE solution is required. -/
theorem quadraticTransverse_affineVector_odeCollision_constant
    (N : Matrix (Fin 3) (Fin 3) K)
    (U : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (hUT :
      U * (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C) = 1)
    (hode :
      (1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C).mulVec
          (dvec (dvec b)) =
        -((N.map Polynomial.C).mulVec (dvec b) +
          (N.map Polynomial.C).mulVec (dvec b)))
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    ∀ i : Fin 3, Polynomial.derivative (b i) = 0 := by
  let T : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • N.map Polynomial.C
  let Np := N.map Polynomial.C
  have hTderiv :
      quadraticTransverse_polynomialMatrixDerivative T = Np :=
    dmat_affineN N
  have hNderiv :
      quadraticTransverse_polynomialMatrixDerivative Np = 0 :=
    quadraticTransverse_polynomialMatrixDerivative_mapC N
  have hfirst :
      dvec (T.mulVec b) =
        Np.mulVec b + T.mulVec (dvec b) := by
    rw [dvec_mulVec, hTderiv]
  have hsecond :
      dvec (dvec (T.mulVec b)) =
        Np.mulVec (dvec b) +
          (Np.mulVec (dvec b) + T.mulVec (dvec (dvec b))) := by
    rw [hfirst, dvec_add, dvec_mulVec, dvec_mulVec,
      hNderiv, hTderiv]
    simp
  have hzero :
      dvec (dvec (T.mulVec b)) = 0 := by
    rw [hsecond, hode]
    abel
  apply quadraticTransverse_affineVector_twoValues_constant N U b hUT
  · intro i
    have hi := congrFun hzero i
    simpa [dvec] using hi
  · exact hcoll

end
end HC4.Valuation
