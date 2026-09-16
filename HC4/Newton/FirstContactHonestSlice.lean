import HC4.Newton.FirstContactAffinePlane
import Mathlib.Tactic

/-!
# A18.5.65b: honest finite support on a first-contact line slice

The first-contact carrier is already cut out by the toric balance equation and
its exact denominator-cleared contact equation.  Refining in the contact
coordinate adds one attained coordinate equation.

This file isolates the finite-support bookkeeping needed by the final
RationalRigidity splice.  The refined carrier is either literally supported at
one exponent, or it contains two distinct genuine supported exponents with
nonzero coefficients.  Moreover, when the refinement is made in the contact
coordinate, positivity of the contact scale makes ordinary total degree
constant on the whole refined support.

Thus the non-singleton branch is governed by the three simpler equations

* toric balance;
* fixed ordinary degree; and
* fixed omitted/contact coordinate.

No convex-geometric replacement and no artificial endpoint are introduced.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero coordinate-refined first-contact carrier is either supported at
one actual exponent, or contains two distinct actual support exponents.  In
the second branch both endpoint coefficients are nonzero literally because the
endpoints belong to the `MvPolynomial` support.  The affine constraints are
retained universally in either branch. -/
theorem coordinateMax_firstContact_singleton_or_honestPair
    {a b m scale bump : ℕ} {j i : Fin 4}
    {psi : MvPolynomial (Fin 4) K}
    (hBal : HasBalancedMvSupport a b psi)
    (D : CoordinateMaxInitialData
      (initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ) psi) i) :
    (∀ d ∈ D.face.support,
      IsBalancedExponent a b d ∧
      scaledContactExponentWeight j scale bump d = (scale * m : ℕ) ∧
      d i = D.level) ∧
    ((∃ p, p ∈ D.face.support ∧
        ∀ q ∈ D.face.support, q = p) ∨
      ∃ p q,
        p ∈ D.face.support ∧
        q ∈ D.face.support ∧
        p ≠ q ∧
        MvPolynomial.coeff p D.face ≠ 0 ∧
        MvPolynomial.coeff q D.face ≠ 0) := by
  classical
  constructor
  · exact coordinateMax_firstContact_support_constraints hBal D
  · rcases MvPolynomial.support_nonempty.mpr D.face_ne_zero with ⟨p, hp⟩
    by_cases hunique : ∀ q ∈ D.face.support, q = p
    · exact Or.inl ⟨p, hp, hunique⟩
    · right
      push_neg at hunique
      rcases hunique with ⟨q, hq, hqp⟩
      exact ⟨p, q, hp, hq, Ne.symm hqp,
        MvPolynomial.mem_support_iff.mp hp,
        MvPolynomial.mem_support_iff.mp hq⟩

/-- On a coordinate-maximal refinement taken in the contact coordinate itself,
all surviving exponents have the same ordinary total degree.  The bump term
cancels because the contact coordinate is fixed, while positive `scale`
cancels the remaining degree difference. -/
theorem coordinateMax_contactCoordinate_ordinaryDegree_eq
    {a b m scale bump : ℕ} {j : Fin 4}
    {psi : MvPolynomial (Fin 4) K}
    (hscale : 0 < scale)
    (hBal : HasBalancedMvSupport a b psi)
    (D : CoordinateMaxInitialData
      (initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ) psi) j) :
    ∀ p ∈ D.face.support, ∀ q ∈ D.face.support,
      ordinaryDegree4 p = ordinaryDegree4 q := by
  intro p hp q hq
  have hpC := coordinateMax_firstContact_support_constraints hBal D p hp
  have hqC := coordinateMax_firstContact_support_constraints hBal D q hq
  have hpcontact := hpC.2.1
  have hqcontact := hqC.2.1
  have hpj : p j = q j := hpC.2.2.trans hqC.2.2.symm
  unfold scaledContactExponentWeight at hpcontact hqcontact
  have hscaleZ : (0 : ℤ) < (scale : ℤ) := by exact_mod_cast hscale
  have hpjZ : (p j : ℤ) = (q j : ℤ) := by exact_mod_cast hpj
  have hdegZ : (ordinaryDegree4 p : ℤ) = (ordinaryDegree4 q : ℤ) := by
    push_cast at hpcontact hqcontact
    nlinarith
  exact_mod_cast hdegZ

/-- Caller-facing non-singleton branch in the contact coordinate.  It packages
an honest pair of distinct supported exponents together with their literal
nonzero coefficients and the fixed-degree conclusion that will be consumed by
the affine-line recogniser. -/
theorem coordinateMax_contactCoordinate_honestPair_sameDegree
    {a b m scale bump : ℕ} {j : Fin 4}
    {psi : MvPolynomial (Fin 4) K}
    (hscale : 0 < scale)
    (hBal : HasBalancedMvSupport a b psi)
    (D : CoordinateMaxInitialData
      (initialForm
        (scaledContactWeight j scale bump) (scale * m : ℤ) psi) j)
    (hnonsingleton : ¬ ∃ p, p ∈ D.face.support ∧
      ∀ q ∈ D.face.support, q = p) :
    ∃ p q,
      p ∈ D.face.support ∧
      q ∈ D.face.support ∧
      p ≠ q ∧
      MvPolynomial.coeff p D.face ≠ 0 ∧
      MvPolynomial.coeff q D.face ≠ 0 ∧
      ordinaryDegree4 p = ordinaryDegree4 q ∧
      p j = q j := by
  rcases (coordinateMax_firstContact_singleton_or_honestPair hBal D).2 with
    hsingle | hpair
  · exact (hnonsingleton hsingle).elim
  · rcases hpair with ⟨p, q, hp, hq, hpq, hcp, hcq⟩
    have hdeg := coordinateMax_contactCoordinate_ordinaryDegree_eq
      hscale hBal D p hp q hq
    have hpC := coordinateMax_firstContact_support_constraints hBal D p hp
    have hqC := coordinateMax_firstContact_support_constraints hBal D q hq
    have hpj : p j = q j := hpC.2.2.trans hqC.2.2.symm
    exact ⟨p, q, hp, hq, hpq, hcp, hcq, hdeg, hpj⟩

end

end HC4.Newton
