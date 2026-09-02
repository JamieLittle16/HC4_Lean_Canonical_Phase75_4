import HC4.Newton.FirstSchurLayerLinearization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianRecognition
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileRigidityClosure
import Mathlib.Tactic

/-!
# A19.R18: integral active-pivot cancellation for the profile Hessian

The final Schur adapter produces the binary profile-Hessian determinant only
through multiplication by the surviving active transverse pivot.  Division by
that pivot is unnecessary.  Its constant parameter coefficient is nonzero, so
ordinary polynomial convolution is triangular: once all lower coefficients of
the right factor have been killed, the next product coefficient is exactly the
constant pivot coefficient times the next right coefficient.

This file isolates that cancellation once.  It reuses the generic convolution
lemma from `FirstSchurLayerLinearization`; no localization, inverse, or second
cancellation infrastructure is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u

/-- **R18 triangular constant-pivot cancellation.**  If the right factor has
vanished below `n`, a zero `n`th product coefficient and a nonzero constant
coefficient of the left factor force the `n`th right coefficient to vanish. -/
theorem polynomial_coeff_eq_zero_of_constant_pivot
    {R : Type u} [CommRing R] [IsDomain R]
    (A B : Polynomial R)
    {n : ℕ}
    (hA0 : A.coeff 0 ≠ 0)
    (hprod : (A * B).coeff n = 0)
    (hlower : ∀ k : ℕ, k < n → B.coeff k = 0) :
    B.coeff n = 0 := by
  have hlinear :=
    HC4.Newton.coeff_mul_eq_constant_mul_of_right_vanishes_below
      A B hlower
  have hmul : A.coeff 0 * B.coeff n = 0 := by
    rw [← hlinear]
    exact hprod
  exact (mul_eq_zero.mp hmul).resolve_left hA0

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 profile determinant cancellation.**  Any integral active factor with
nonzero constant coefficient may be cancelled coefficientwise from the honest
profile-Hessian determinant.  The hypothesis is intentionally coefficientwise:
this is the exact form delivered by the final cleared-Schur clock, and avoids
introducing a fraction field into R18. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet_eq_zero_of_constant_pivot
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (A : Polynomial (MvPolynomial (Fin 3) K))
    (hA0 : A.coeff 0 ≠ 0)
    (hprod : ∀ n : ℕ, (A * R.profileHessianDet).coeff n = 0) :
    R.profileHessianDet = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      exact polynomial_coeff_eq_zero_of_constant_pivot
        A R.profileHessianDet hA0 (hprod n)
        (fun k hk => ih k hk)

/-- Once the cleared-Schur calculation has supplied the coefficientwise active
product equation, the already-green R19 staircase rigidity closes the terminal
profile immediately. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.impossible_of_constant_pivot_profileHessianDet
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (A : Polynomial (MvPolynomial (Fin 3) K))
    (hA0 : A.coeff 0 ≠ 0)
    (hprod : ∀ n : ℕ, (A * R.profileHessianDet).coeff n = 0) : False := by
  apply R.impossible_of_profileHessianDet
  exact R.profileHessianDet_eq_zero_of_constant_pivot A hA0 hprod

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
