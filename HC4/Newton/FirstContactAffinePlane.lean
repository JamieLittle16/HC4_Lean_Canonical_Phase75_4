import HC4.Newton.FirstNonfacetContact
import HC4.Newton.FiniteSupportExposedVertex
import Mathlib.Tactic

/-!
# A18.5.65: affine-plane equations on the genuine first-contact carrier

The final Newton/RationalRigidity splice needs an honest one-dimensional face,
not merely a distinguished boundary monomial.  The first-contact carrier
already supplies two independent exact linear equations on every supported
exponent:

* the symmetric torus balance equation; and
* the denominator-cleared first-contact weight equation.

Consequently a further coordinate-exposed face carries a third exact equation.
This file records that losslessly at the actual `MvPolynomial` support level.
It introduces no convexity assumption and no replacement polynomial; it is the
algebraic interface consumed by the finite-support edge extractor.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Every exponent of a balanced first-contact initial form satisfies both the
original toric balance equation and the exact cleared contact equation. -/
theorem firstContact_initialForm_support_constraints
    {a b m scale bump : ℕ} {j : Fin 4}
    {ψ : MvPolynomial (Fin 4) K}
    (hBal : HasBalancedMvSupport a b ψ) :
    ∀ d ∈ (initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ) ψ).support,
      IsBalancedExponent a b d ∧
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) := by
  intro d hd
  constructor
  · exact
      (hBal.initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ)) d hd
  · have hw :=
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump) (scale * m : ℤ) ψ)
        (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_scaledContactWeight] at hw
    exact hw

/-- A coordinate-maximal subface of a balanced contact carrier retains the two
contact-plane equations and adds the attained coordinate equation.  Thus its
support lies in the intersection of three explicit affine hyperplanes. -/
theorem CoordinateMaxInitialData.firstContact_lineSlice_constraints
    {a b m scale bump : ℕ} {j i : Fin 4}
    {G : MvPolynomial (Fin 4) K}
    (D : CoordinateMaxInitialData G i)
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ)) :
    ∀ d ∈ D.face.support,
      IsBalancedExponent a b d ∧
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) ∧
      d i = D.level := by
  intro d hd
  have hdG : d ∈ G.support := D.support_subset hd
  exact ⟨hBal d hdG, hcontact d hdG, D.coordinate_eq d hd⟩

/-- Direct first-contact form of the line-slice constraints.  Starting from a
balanced source polynomial, one coordinate-max refinement of its exact contact
carrier already has the three equations needed for affine-line recognition. -/
theorem coordinateMax_firstContact_support_constraints
    {a b m scale bump : ℕ} {j i : Fin 4}
    {ψ : MvPolynomial (Fin 4) K}
    (hBal : HasBalancedMvSupport a b ψ)
    (D : CoordinateMaxInitialData
      (initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ) ψ) i) :
    ∀ d ∈ D.face.support,
      IsBalancedExponent a b d ∧
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) ∧
      d i = D.level := by
  let G := initialForm
    (scaledContactWeight j scale bump) (scale * m : ℤ) ψ
  have hBalG : HasBalancedMvSupport a b G := by
    dsimp [G]
    exact hBal.initialForm
      (scaledContactWeight j scale bump) (scale * m : ℤ)
  have hcontactG : ∀ d ∈ G.support,
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) := by
    intro d hd
    exact (firstContact_initialForm_support_constraints hBal d hd).2
  change ∀ d ∈ D.face.support,
    IsBalancedExponent a b d ∧
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) ∧
      d i = D.level
  exact D.firstContact_lineSlice_constraints hBalG hcontactG

end

end HC4.Newton
