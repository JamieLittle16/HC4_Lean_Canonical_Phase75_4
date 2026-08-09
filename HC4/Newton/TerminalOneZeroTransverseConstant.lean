import HC4.Newton.TerminalOneZeroAffineRecovery
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic

/-!
# Constant transverse determinant in the one-zero branch

Phase 93.34 proves

    -(S)^2 * Δ₂₃ = 1,

where `S = ∂₀∂₁F` and `Δ₂₃` is the Hessian cross-determinant in the
interior coordinates `2,3`.

This already makes `Δ₂₃` a unit in the ambient multivariate polynomial
ring.  Over a field, every unit multivariate polynomial is a constant
unit.  Hence

    Δ₂₃ = C t,   t ≠ 0.

This is exactly the planar Keller certificate needed on every fixed
one-zero fibre.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The transverse `2,3` Hessian determinant is a unit under the
one-zero Monge--Ampère factorisation. -/
theorem standardOneZero_transverseDet_isUnit
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    IsUnit (standardOneZeroTransverseDet F) := by
  rw [isUnit_iff_exists_inv]
  refine
    ⟨-(standardOneZeroSlope F)^2, ?_⟩
  have hfactor :=
    standardOneZero_mongeAmpere_factor_eq_one
      ha had hhom hMA
  calc
    standardOneZeroTransverseDet F *
        (-(standardOneZeroSlope F)^2) =
      -(standardOneZeroSlope F)^2 *
        standardOneZeroTransverseDet F := by
          ring
    _ = 1 := hfactor

/-- The transverse Hessian determinant is a nonzero scalar polynomial. -/
theorem standardOneZero_transverseDet_eq_C_nonzero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    ∃ t : K,
      t ≠ 0 ∧
      standardOneZeroTransverseDet F =
        MvPolynomial.C t := by
  have hunit :
      IsUnit (standardOneZeroTransverseDet F) :=
    standardOneZero_transverseDet_isUnit
      ha had hhom hMA
  rcases
      (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit) with
    ⟨t, htunit, hdet⟩
  exact
    ⟨t, htunit.ne_zero, hdet⟩

end

end HC4.Newton
