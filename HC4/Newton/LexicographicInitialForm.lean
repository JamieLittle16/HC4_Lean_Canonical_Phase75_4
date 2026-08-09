import Mathlib.Algebra.MvPolynomial.Basic
import HC4.Newton.LexicographicRefinement

/-!
# Lexicographic exposed forms of multivariate polynomials

Phase 89.1 proved the finite order-theoretic fact that, when the secondary
weight is bounded by `M`, the maximisers of

    M * w₀ + w₁

are exactly the lexicographic maximisers of `(w₀,w₁)`.

This file lifts that statement from finite sets to actual
`MvPolynomial`s.  We define the exposed polynomial associated with a
predicate on exponent vectors by summing exactly the corresponding
monomials from the original support.  The main theorem says that the
single scaled-weight exposed polynomial is literally equal to the
lexicographically exposed polynomial.

The construction is intentionally independent of the older
`HC4.Polynomial.initialForm` implementation.  A later adapter can identify
these exposed sums with the legacy initial-form API without changing the
finite Newton--Rees argument proved here.
-/

namespace HC4.Newton

noncomputable section

open scoped BigOperators

variable {σ R : Type*} [CommSemiring R]

/-- Keep exactly those monomials of `p` whose exponent satisfies `P`. -/
noncomputable def selectedInitial
    (p : MvPolynomial σ R)
    (P : (σ →₀ ℕ) → Prop) :
    MvPolynomial σ R := by
  classical
  exact
    (p.support.filter P).sum
      (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d p))

/-- The finite subset of the support selected by a predicate. Classical
decidability is deliberately encapsulated here rather than appearing as an
extra instance argument in the public theorems below. -/
noncomputable def selectedSupport
    (p : MvPolynomial σ R)
    (P : (σ →₀ ℕ) → Prop) :
    Finset (σ →₀ ℕ) := by
  classical
  exact p.support.filter P

/-- The exposed polynomial obtained from the maximisers of the single
scaled weight `M*w₀+w₁`. -/
noncomputable def scaledInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (M : ℕ)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ) :
    MvPolynomial σ R :=
  selectedInitial p
    (fun d => IsScaledMaxOn p.support M w₀ w₁ d)

/-- The exposed polynomial obtained by lexicographically maximising
`(w₀,w₁)` on the support. -/
noncomputable def lexInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ) :
    MvPolynomial σ R :=
  selectedInitial p
    (fun d => IsLexMaxOn p.support w₀ w₁ d)

/-- **MvPolynomial lexicographic collapse.**
If every secondary weight occurring in the support of `p` is strictly
smaller than `M`, then the face exposed by the single scaled weight
`M*w₀+w₁` is exactly the lexicographically exposed face. -/
theorem scaledInitialForm_eq_lexInitialForm
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (M : ℕ)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ)
    (hbound : ∀ d ∈ p.support, w₁ d < M) :
    scaledInitialForm p M w₀ w₁ =
      lexInitialForm p w₀ w₁ := by
  classical
  have hfaces :
      p.support.filter
          (fun d => IsScaledMaxOn p.support M w₀ w₁ d) =
        p.support.filter
          (fun d => IsLexMaxOn p.support w₀ w₁ d) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hscaled⟩
      exact
        ⟨hd,
          (isScaledMaxOn_iff_isLexMaxOn hbound).mp hscaled⟩
    · rintro ⟨hd, hlex⟩
      exact
        ⟨hd,
          (isScaledMaxOn_iff_isLexMaxOn hbound).mpr hlex⟩
  unfold scaledInitialForm lexInitialForm selectedInitial
  rw [hfaces]

/-- Coefficient-free support-level reformulation of the same bridge:
the selected exponent finsets agree exactly. -/
theorem scaledSupportFilter_eq_lexSupportFilter
    [DecidableEq σ]
    (p : MvPolynomial σ R)
    (M : ℕ)
    (w₀ w₁ : (σ →₀ ℕ) → ℕ)
    (hbound : ∀ d ∈ p.support, w₁ d < M) :
    selectedSupport p
        (fun d => IsScaledMaxOn p.support M w₀ w₁ d) =
      selectedSupport p
        (fun d => IsLexMaxOn p.support w₀ w₁ d) := by
  classical
  unfold selectedSupport
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hscaled⟩
    exact
      ⟨hd,
        (isScaledMaxOn_iff_isLexMaxOn hbound).mp hscaled⟩
  · rintro ⟨hd, hlex⟩
    exact
      ⟨hd,
        (isScaledMaxOn_iff_isLexMaxOn hbound).mpr hlex⟩

end

end HC4.Newton
