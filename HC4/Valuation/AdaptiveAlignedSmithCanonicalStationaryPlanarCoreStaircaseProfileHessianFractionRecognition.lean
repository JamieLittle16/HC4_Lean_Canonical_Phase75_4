import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessianRecognition
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# A19.R15: fraction-field recognition of the staircase Hessian

The honest contact profile has coefficients in the transverse polynomial ring,
not in a field.  A19.115 already embeds that ring injectively into its fraction
field, while A19.R14 recognizes the canonical staircase Hessian once its three
entries have the expected coefficient formulas.

This file packages exactly that representation change.  If three polynomial
entries over an integral coefficient ring have the weighted binary Hessian
coefficients and their determinant vanishes before localization, then after
mapping to the fraction field the stationary staircase residual vanishes.

No division is performed in the geometric coefficient ring and no second raw
residual is introduced.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [CharZero R]

/-- **Integral coefficient block to fraction-field staircase residual.**

This is the form needed by the final contact/Schur adapter: its geometric
calculation may stay over the transverse polynomial ring, while the already
proved field-valued R6 rigidity theorem is consumed only after localization. -/
theorem binaryStaircaseProfileResidual_fraction_eq_zero_of_coeffwise_hessian
    (D r : ℕ) (h H00 H01 H11 : Polynomial R)
    (h00 : ∀ n : ℕ,
      H00.coeff n =
        (((D : R) - (r : R) * (n : R)) *
          ((D : R) - (r : R) * (n : R) - 1)) * h.coeff n)
    (h01 : ∀ n : ℕ,
      H01.coeff n =
        (n : R) * ((D : R) - (r : R) * (n : R)) * h.coeff n)
    (h11 : ∀ n : ℕ,
      H11.coeff n = (n : R) * ((n : R) - 1) * h.coeff n)
    (hdet : H00 * H11 - H01 * H01 = 0) :
    binaryStaircaseProfileResidual D r
      (Polynomial.map (algebraMap R (FractionRing R)) h) = 0 := by
  let ι : R →+* FractionRing R := algebraMap R (FractionRing R)
  have h00' : ∀ n : ℕ,
      (Polynomial.map ι H00).coeff n =
        (((D : FractionRing R) - (r : FractionRing R) * (n : FractionRing R)) *
          ((D : FractionRing R) - (r : FractionRing R) * (n : FractionRing R) - 1)) *
            (Polynomial.map ι h).coeff n := by
    intro n
    simpa [ι] using congrArg ι (h00 n)
  have h01' : ∀ n : ℕ,
      (Polynomial.map ι H01).coeff n =
        (n : FractionRing R) *
          ((D : FractionRing R) - (r : FractionRing R) * (n : FractionRing R)) *
            (Polynomial.map ι h).coeff n := by
    intro n
    simpa [ι] using congrArg ι (h01 n)
  have h11' : ∀ n : ℕ,
      (Polynomial.map ι H11).coeff n =
        (n : FractionRing R) * ((n : FractionRing R) - 1) *
          (Polynomial.map ι h).coeff n := by
    intro n
    simpa [ι] using congrArg ι (h11 n)
  have hdet' :
      Polynomial.map ι H00 * Polynomial.map ι H11 -
          Polynomial.map ι H01 * Polynomial.map ι H01 = 0 := by
    calc
      Polynomial.map ι H00 * Polynomial.map ι H11 -
          Polynomial.map ι H01 * Polynomial.map ι H01 =
        Polynomial.map ι (H00 * H11 - H01 * H01) := by simp
      _ = 0 := by rw [hdet]; simp
  simpa [ι] using
    (binaryStaircaseProfileResidual_eq_zero_of_coeffwise_hessian
      D r (Polynomial.map ι h)
      (Polynomial.map ι H00) (Polynomial.map ι H01) (Polynomial.map ι H11)
      h00' h01' h11' hdet')

end

end HC4.Valuation
