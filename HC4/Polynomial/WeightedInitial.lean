import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Exact weighted initial forms of multivariate polynomials

This module uses Mathlib's weighted-homogeneous decomposition as the exact
initial-form operator at a prescribed integer weight.  It records the
coefficient formula, homogeneity, idempotence, and the behaviour on already
homogeneous polynomials.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

variable {σ K : Type*} [CommSemiring K]

/-- The exact component of a polynomial at integer weight `m`. -/
noncomputable def initialForm (w : σ → ℤ) (m : ℤ) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  MvPolynomial.weightedHomogeneousComponent w m

/-- Coefficients of the exact weighted initial form are obtained by filtering by weight. -/
theorem coeff_initialForm (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K)
    (d : σ →₀ ℕ) :
    coeff d (initialForm w m p) =
      if Finsupp.weight w d = m then coeff d p else 0 := by
  simpa [initialForm] using
    (MvPolynomial.coeff_weightedHomogeneousComponent m p d)

/-- Every exact initial form is weighted homogeneous at the selected weight. -/
theorem initialForm_isWeightedHomogeneous (w : σ → ℤ) (m : ℤ)
    (p : MvPolynomial σ K) :
    MvPolynomial.IsWeightedHomogeneous w (initialForm w m p) m := by
  simpa [initialForm] using
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous m p)

@[simp]
theorem initialForm_zero (w : σ → ℤ) (m : ℤ) :
    initialForm (K := K) w m 0 = 0 := by
  simp [initialForm]

@[simp]
theorem initialForm_add (w : σ → ℤ) (m : ℤ)
    (p q : MvPolynomial σ K) :
    initialForm w m (p + q) = initialForm w m p + initialForm w m q := by
  simp [initialForm]

@[simp]
theorem initialForm_smul (w : σ → ℤ) (m : ℤ) (a : K)
    (p : MvPolynomial σ K) :
    initialForm w m (a • p) = a • initialForm w m p := by
  simp [initialForm]

/-- The selected component of a polynomial already homogeneous at that weight is itself. -/
theorem initialForm_eq_self_of_isWeightedHomogeneous
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m) :
    initialForm w m p = p := by
  simpa [initialForm] using hp.weightedHomogeneousComponent_same

/-- A different weighted component of a homogeneous polynomial vanishes. -/
theorem initialForm_eq_zero_of_isWeightedHomogeneous
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m)
    (n : ℤ) (hne : n ≠ m) :
    initialForm w n p = 0 := by
  simpa [initialForm] using hp.weightedHomogeneousComponent_ne n hne

/-- Exact initial-form extraction is idempotent. -/
theorem initialForm_idempotent (w : σ → ℤ) (m : ℤ)
    (p : MvPolynomial σ K) :
    initialForm w m (initialForm w m p) = initialForm w m p := by
  exact initialForm_eq_self_of_isWeightedHomogeneous
    (initialForm_isWeightedHomogeneous w m p)

end

end HC4.Polynomial
