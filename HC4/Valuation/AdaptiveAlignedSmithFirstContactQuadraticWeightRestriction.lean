import HC4.Valuation.AdaptiveAlignedSmithFirstContactUniqueZeroElimination
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingQuadraticSupport
import Mathlib.Tactic

/-!
# Quadratic first-contact restrictions on the terminal cocharacter

The direct-closing audit has isolated a genuine quadratic source event at the
first actual closing layer.  Independently, the honest first-contact terminal
machinery proves that every surviving terminal cocharacter has the marked
longitudinal zero and at least one second zero.

This file records the compatibility constraint between those two facts.

If the distinguished first-contact monomial is quadratic, say `X_i X_k`, then
weighted homogeneity of the actual terminal Monge--Ampere fibre forces

    w_i + w_k = d.

Since the terminal weighted degree `d` is positive, the two coordinates of a
quadratic contact cannot both have zero terminal weight.  In the especially
important square-contact case `X_i^2`, one gets

    2 w_i = d,

so `w_i > 0`.  Consequently the second terminal zero forced by the marked
collision must lie in a coordinate different from both the marked
longitudinal axis and the square-contact coordinate.

This is the exact restriction needed by the next kernel-contact source-lift
step: if the fresh aligned-kernel observable can be lifted to a genuine
kernel-square source contact, the planar/two-zero endpoint is forced to put
its second zero somewhere else.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- The distinguished positive first-contact exponent really occurs in the
actual terminal fibre. -/
theorem contactExponent_coeff_ne_zero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    MvPolynomial.coeff T.lattice.contactExponent T.fibre ≠ 0 := by
  simpa [AdaptiveAlignedSmithClosingFirstContactTerminalData.fibre] using
    T.lattice.contactCoefficient_specialFiber_ne_zero

/-- Hence the terminal cocharacter assigns the distinguished first-contact
exponent exactly the terminal weighted degree. -/
theorem contactExponent_weightedDegree
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    integralWeightedDegree
        (fun i => (C.weight i : ℤ))
        T.lattice.contactExponent =
      (C.degree : ℤ) := by
  exact C.homogeneous T.lattice.contactExponent C.contactExponent_coeff_ne_zero

/-- If the distinguished contact exponent is the quadratic monomial
`X_i X_k`, its two terminal source weights add to the terminal degree. -/
theorem quadraticContact_weightSum
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k) :
    (C.weight i : ℤ) + (C.weight k : ℤ) = (C.degree : ℤ) := by
  have hcoeff :
      MvPolynomial.coeff
          (HC4.Newton.quadraticExponent i k) T.fibre ≠ 0 := by
    have h := C.contactExponent_coeff_ne_zero
    rw [hquad] at h
    simpa [
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent,
      HC4.Newton.quadraticExponent,
      add_comm] using h
  exact
    weightedHomogeneous_quadraticCoeff_weightSum
      C.homogeneous i k hcoeff

/-- A quadratic first-contact monomial cannot be supported entirely in the
terminal zero-weight plane. -/
theorem not_both_zero_of_quadraticContact
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k) :
    ¬ (C.weight i = 0 ∧ C.weight k = 0) := by
  intro hzero
  have hsum := C.quadraticContact_weightSum i k hquad
  have hdpos : 0 < (C.degree : ℤ) := C.degree_pos
  rw [hzero.1, hzero.2] at hsum
  norm_num at hsum
  omega

/-- In the kernel-square case the contact coordinate itself has positive
terminal weight. -/
theorem squareContact_weight_pos
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4)
    (hsquare :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i i) :
    0 < C.weight i := by
  have hsum := C.quadraticContact_weightSum i i hsquare
  have hdpos : 0 < (C.degree : ℤ) := C.degree_pos
  have hiInt : 0 < (C.weight i : ℤ) := by
    linarith
  exact_mod_cast hiInt

/-- Therefore a zero-weight coordinate can never be the coordinate carrying
a square first-contact monomial. -/
theorem zeroWeight_ne_squareContactCoordinate
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i z : Fin 4)
    (hsquare :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i i)
    (hz : C.weight z = 0) :
    z ≠ i := by
  intro hzi
  subst z
  have hpos := C.squareContact_weight_pos i hsquare
  omega

/-- **Second-zero displacement by a square contact.**

Every surviving honest first-contact terminal cocharacter has a second zero
coordinate.  If the distinguished contact is `X_i^2`, that second zero is
forced to be different from both the marked longitudinal coordinate `0` and
from the square-contact coordinate `i`. -/
theorem exists_secondMarkedZero_away_from_squareContact
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4)
    (hsquare :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i i) :
    ∃ z : Fin 4,
      z ≠ 0 ∧ z ≠ i ∧ C.weight z = 0 := by
  rcases C.hasSecondMarkedTerminalZero with ⟨z, hz0, hzw⟩
  refine ⟨z, hz0, ?_, hzw⟩
  exact C.zeroWeight_ne_squareContactCoordinate i z hsquare hzw

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
