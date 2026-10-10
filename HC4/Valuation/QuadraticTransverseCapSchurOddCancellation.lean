import HC4.Valuation.QuadraticTransverseCapAdjugateSchur
import Mathlib.Tactic

/-!
# Odd transverse Schur coefficient, without differentiation of determinants

For a source with transverse degree at most two, the transverse 3x3
Hessian C is independent of the transverse variables. Along the two
opposite transverse unit sections, the 4x4 Hessian has the same C
and mixed columns v+z and v-z, where z is a column of C'(x).

If det(C)=0, subtracting the two determinant-one equations cancels
both longitudinal Hessian entries and the quadratic mixed terms.
It forces z·adj(C)v=0, exactly the needed C'w=0 coefficient.

The first theorem is the fully expanded commutative-ring identity.
The second consumes exact unit equations and has no analytic limit
or division by four in a polynomial ring.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- Difference between the two opposite mixed-column Schur cores;
the even quadratic terms cancel exactly. -/
theorem quadraticAxisFourBlockCore_oddPairing
    (uplus uminus v₀ v₁ v₂ z₀ z₁ z₂ : R)
    (C : GeneralThreeBlock R) :
    quadraticAxisFourBlockCore uplus
        (v₀ + z₀) (v₁ + z₁) (v₂ + z₂)
        C.a C.b C.c C.d C.e C.f -
      quadraticAxisFourBlockCore uminus
        (v₀ - z₀) (v₁ - z₁) (v₂ - z₂)
        C.a C.b C.c C.d C.e C.f =
      (uplus - uminus) * C.determinantCore -
        4 * (
          z₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
          z₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
          z₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) := by
  unfold quadraticAxisFourBlockCore
    quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
    GeneralThreeBlock.determinantCore
  ring

/-- The two represented-source determinant-one equations at opposite
transverse sections force the exact rank-two linear coefficient.
Here z can be any column of C'; no pseudo-inverse is introduced. -/
theorem quadraticAxisFourBlockCore_oddPairing_zero_of_unit
    [IsDomain R] [CharZero R]
    (uplus uminus v₀ v₁ v₂ z₀ z₁ z₂ : R)
    (C : GeneralThreeBlock R)
    (hthree : C.determinantCore = 0)
    (hplus :
      quadraticAxisFourBlockCore uplus
        (v₀ + z₀) (v₁ + z₁) (v₂ + z₂)
        C.a C.b C.c C.d C.e C.f = 1)
    (hminus :
      quadraticAxisFourBlockCore uminus
        (v₀ - z₀) (v₁ - z₁) (v₂ - z₂)
        C.a C.b C.c C.d C.e C.f = 1) :
    z₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
      z₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
      z₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂ = 0 := by
  have hodd :=
    quadraticAxisFourBlockCore_oddPairing
      uplus uminus v₀ v₁ v₂ z₀ z₁ z₂ C
  rw [hplus, hminus, hthree] at hodd
  have hfour :
      (4 : R) * (
        z₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
        z₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
        z₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) = 0 := by
    linear_combination -hodd
  exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)

end

end HC4.Valuation
