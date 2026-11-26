import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Compatibility with the pre-4.35 coefficient API
-/

namespace MvPolynomial

/-- The former exponent-first coefficient accessor. -/
abbrev coeff {σ K : Type*} [CommSemiring K]
    (d : σ →₀ ℕ) (p : MvPolynomial σ K) : K :=
  AddMonoidAlgebra.coeff p d

end MvPolynomial
