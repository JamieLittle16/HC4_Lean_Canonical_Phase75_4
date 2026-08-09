import HC4.Newton.MixedDepartureAdapter
import Mathlib.Tactic

/-!
# Weight-theoretic core of the terminal conformal face

The remaining exceptional restart case is a first departure occurring
exactly at determinant closure.  The v5 audit observes that the terminal
associated-graded fibre is weighted homogeneous and that its ordinary
quadratic part is automatically conformal for the terminal weight.

This file formalises the weight-theoretic half of that statement without
depending on a particular Hessian-matrix representation.

For an integral weight `lambda : σ -> ℤ`, define the weighted degree of a
multi-index `m` by

    sum_i m_i * lambda_i.

A polynomial is weighted homogeneous of degree `d` when every nonzero
coefficient has this weight.

The main consequences are:

1. every nonzero quadratic coefficient `X_i X_j` satisfies
       lambda_i + lambda_j = d;

2. if all weights are equal to one nonzero scalar `a`, then the existence
   of one nonzero quadratic coefficient forces every supported monomial to
   have ordinary degree exactly two.

Thus the scalar terminal cocharacter already forces the terminal fibre to
be purely quadratic at the support level.  The next terminal module only
needs to derive nondegeneracy of the quadratic Hessian from the unit
terminal Hessian determinant and then dispatch the non-scalar conformal
endpoint.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Integral weighted degree of a multivariate exponent. -/
def integralWeightedDegree
    (lambda : σ -> ℤ)
    (m : σ →₀ ℕ) : ℤ :=
  m.sum (fun i n => (n : ℤ) * lambda i)

/-- Ordinary total degree, viewed as an integer. -/
def integralOrdinaryDegree
    (m : σ →₀ ℕ) : ℤ :=
  m.sum (fun _ n => (n : ℤ))

/-- Weighted homogeneity stated directly on nonzero coefficients. -/
def IsIntegralWeightedHomogeneous
    (lambda : σ -> ℤ)
    (d : ℤ)
    (F : MvPolynomial σ K) : Prop :=
  ∀ m : σ →₀ ℕ,
    MvPolynomial.coeff m F ≠ 0 ->
      integralWeightedDegree lambda m = d

/-- Exponent of the quadratic monomial `X_i X_j`. -/
def quadraticExponent
    (i j : σ) : σ →₀ ℕ :=
  Finsupp.single i 1 + Finsupp.single j 1

/-- The weighted degree of a quadratic exponent is the sum of the two
coordinate weights, including the diagonal case `i=j`. -/
theorem integralWeightedDegree_quadraticExponent
    (lambda : σ -> ℤ)
    (i j : σ) :
    integralWeightedDegree lambda (quadraticExponent i j) =
      lambda i + lambda j := by
  classical
  let weightTerm : σ → ℕ → ℤ :=
    fun k n => (n : ℤ) * lambda k
  have hzero :
      ∀ k : σ, weightTerm k 0 = 0 := by
    intro k
    simp [weightTerm]
  have hadd :
      ∀ (k : σ) (n₁ n₂ : ℕ),
        weightTerm k (n₁ + n₂) =
          weightTerm k n₁ + weightTerm k n₂ := by
    intro k n₁ n₂
    simp [weightTerm, Nat.cast_add]
    ring
  have hsplit :
      (Finsupp.single i 1 + Finsupp.single j 1).sum weightTerm =
        (Finsupp.single i 1).sum weightTerm +
          (Finsupp.single j 1).sum weightTerm := by
    exact
      Finsupp.sum_add_index'
        (f := Finsupp.single i 1)
        (g := Finsupp.single j 1)
        (h := weightTerm)
        hzero hadd
  have hi :
      (Finsupp.single i 1).sum weightTerm = lambda i := by
    simpa [weightTerm] using
      (Finsupp.sum_single_index
        (a := i)
        (b := (1 : ℕ))
        (h := weightTerm)
        (hzero i))
  have hj :
      (Finsupp.single j 1).sum weightTerm = lambda j := by
    simpa [weightTerm] using
      (Finsupp.sum_single_index
        (a := j)
        (b := (1 : ℕ))
        (h := weightTerm)
        (hzero j))
  unfold integralWeightedDegree
  unfold quadraticExponent
  change
    (Finsupp.single i 1 + Finsupp.single j 1).sum weightTerm =
      lambda i + lambda j
  rw [hsplit, hi, hj]

/-- Every nonzero quadratic coefficient in a weighted-homogeneous fibre
lies on the conformal weight hyperplane `lambda_i + lambda_j = d`. -/
theorem weightedHomogeneous_quadraticCoeff_weightSum
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (i j : σ)
    (hcoeff :
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0) :
    lambda i + lambda j = d := by
  have hdeg :=
    hhom (quadraticExponent i j) hcoeff
  rw [integralWeightedDegree_quadraticExponent] at hdeg
  exact hdeg

/-- A constant integral weight factors out of the weighted degree. -/
theorem integralWeightedDegree_const
    (a : ℤ)
    (m : σ →₀ ℕ) :
    integralWeightedDegree (fun _ : σ => a) m =
      integralOrdinaryDegree m * a := by
  classical
  unfold integralWeightedDegree
  unfold integralOrdinaryDegree
  simp only [Finsupp.sum]
  rw [Finset.sum_mul]

/-- Under a constant weight `a`, a nonzero quadratic coefficient forces
the common weighted degree to be `2*a`. -/
theorem scalarWeightedHomogeneous_degree_eq_two_mul
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (i j : σ)
    (hcoeff :
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0) :
    d = 2 * a := by
  have h :=
    weightedHomogeneous_quadraticCoeff_weightSum
      hhom i j hcoeff
  simpa [two_mul] using h.symm

/-- **Scalar terminal weights are purely quadratic at support level.**
If all weights equal a nonzero integer `a`, and a weighted-homogeneous
polynomial has one nonzero quadratic coefficient, then every nonzero
monomial has ordinary degree exactly two. -/
theorem scalarWeightedHomogeneous_support_degree_two
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (ha : a ≠ 0)
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (i j : σ)
    (hquad :
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0) :
    ∀ m : σ →₀ ℕ,
      MvPolynomial.coeff m F ≠ 0 ->
        integralOrdinaryDegree m = 2 := by
  have hd :
      d = 2 * a :=
    scalarWeightedHomogeneous_degree_eq_two_mul
      hhom i j hquad
  intro m hm
  have hwm :=
    hhom m hm
  rw [integralWeightedDegree_const] at hwm
  rw [hd] at hwm
  have hprod :
      (integralOrdinaryDegree m - 2) * a = 0 := by
    calc
      (integralOrdinaryDegree m - 2) * a =
          integralOrdinaryDegree m * a - 2 * a := by
            ring
      _ = 0 := by
            rw [hwm]
            ring
  rcases mul_eq_zero.mp hprod with hdeg | ha0
  · omega
  · exact False.elim (ha ha0)

/-- Support-level formulation of the scalar terminal conclusion. -/
def HasPureQuadraticSupport
    (F : MvPolynomial σ K) : Prop :=
  ∀ m : σ →₀ ℕ,
    MvPolynomial.coeff m F ≠ 0 ->
      integralOrdinaryDegree m = 2

/-- Packaged scalar terminal weight theorem. -/
theorem scalarWeightedHomogeneous_hasPureQuadraticSupport
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (ha : a ≠ 0)
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (i j : σ)
    (hquad :
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0) :
    HasPureQuadraticSupport F := by
  exact
    scalarWeightedHomogeneous_support_degree_two
      ha hhom i j hquad

end

end HC4.Newton
