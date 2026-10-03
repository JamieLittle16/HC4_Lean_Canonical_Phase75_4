import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoDepartureSplit
import Mathlib.Tactic

/-!
# A19 codimension-two joint versus separated departures

After `constantKernel_or_bothPositiveSupports`, the only active A19.55 case has
actual top-face support leaving both coordinate hyperplanes.  There is a
further elementary exhaustive split:

* some supported exponent is positive in both missing coordinates (`joint`);
* or no such exponent exists, in which case an exponent positive in the first
  missing coordinate is forced to stay on the second hyperplane, and vice
  versa.

The second branch is exactly the source-support shape needed by the primitive
departure pencil.  This module is combinatorial only: it does not assert that
the chosen departures are yet extremal enough for the determinant coefficient
calculation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Actual support simultaneously opening both missing coordinates. -/
def HasJointCodimensionTwoDeparture
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) : Prop :=
  ∃ d ∈ F.support, 0 < d i ∧ 0 < d j

/-- Actual separated departures from the two coordinate hyperplanes. -/
def HasSeparatedCodimensionTwoDepartures
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) : Prop :=
  ∃ u w : Fin 4 →₀ ℕ,
    u ∈ F.support ∧ w ∈ F.support ∧
      0 < u i ∧ u j = 0 ∧
      w i = 0 ∧ 0 < w j

/-- If both positive-coordinate support sets are nonempty, then either one
monomial opens both coordinates or actual departures exist separately on the
two opposite coordinate hyperplanes. -/
theorem joint_or_separated_of_bothPositiveSupports
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (hi : (positiveCoordinateSupport i F).Nonempty)
    (hj : (positiveCoordinateSupport j F).Nonempty) :
    HasJointCodimensionTwoDeparture F i j ∨
      HasSeparatedCodimensionTwoDepartures F i j := by
  classical
  by_cases hjoint : HasJointCodimensionTwoDeparture F i j
  · exact Or.inl hjoint
  · right
    rcases hi with ⟨u, hu⟩
    rcases hj with ⟨w, hw⟩
    have huData := mem_positiveCoordinateSupport.mp hu
    have hwData := mem_positiveCoordinateSupport.mp hw
    have huj : u j = 0 := by
      by_contra hne
      have hpos : 0 < u j := Nat.pos_of_ne_zero hne
      exact hjoint ⟨u, huData.1, huData.2, hpos⟩
    have hwi : w i = 0 := by
      by_contra hne
      have hpos : 0 < w i := Nat.pos_of_ne_zero hne
      exact hjoint ⟨w, hwData.1, hpos, hwData.2⟩
    exact ⟨u, w, huData.1, hwData.1, huData.2, huj, hwi, hwData.2⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- A19-facing four-way split: literal kernel in either missing coordinate,
joint departure, or genuinely separated departures. -/
theorem constantKernel_or_joint_or_separated
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData T) :
    MvPolynomial.pderiv C.first T.topFace.face = 0 ∨
      MvPolynomial.pderiv C.second T.topFace.face = 0 ∨
      HasJointCodimensionTwoDeparture T.topFace.face C.first C.second ∨
      HasSeparatedCodimensionTwoDepartures T.topFace.face C.first C.second := by
  rcases C.constantKernel_or_bothPositiveSupports with
    hfirst | hsecond | hboth
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · rcases joint_or_separated_of_bothPositiveSupports hboth.1 hboth.2 with
      hjoint | hsep
    · exact Or.inr (Or.inr (Or.inl hjoint))
    · exact Or.inr (Or.inr (Or.inr hsep))

end AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData

end

end HC4.Valuation
