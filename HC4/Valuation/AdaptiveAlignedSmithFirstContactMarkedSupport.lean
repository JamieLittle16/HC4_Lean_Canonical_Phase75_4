import HC4.Valuation.AdaptiveAlignedSmithClosingFirstContactWeightSeparation
import HC4.Valuation.AdaptiveAlignedSmithMarkedAxisTerminal
import HC4.Newton.TerminalNonnegativeWeights
import Mathlib.Tactic

/-!
# Marked support of the terminal first-contact collision

The terminal cocharacter is an honest diagonal source scaling of the
first-contact Monge--Ampère fibre.  Its right collision point is transported
through that scaling by an integral constant section.

This gives a very strong support restriction:

    rightPoint i ≠ 0  ==>  terminalWeight i = 0.

Thus the marked collision can move only inside the zero-weight coordinate
subspace.  Since coordinate `0` is already known to have weight zero and the
right point has coordinate `-1` there, only two possibilities remain:

* some transverse coordinate has a second zero terminal weight; or
* every transverse coordinate has positive weight, in which case the right
  point is literally `-e₀`.

The latter is exactly the marked-axis configuration already isolated by the
one-zero endpoint analysis.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- Every nonzero coordinate of the transported terminal right point lies in
a zero-weight source direction. -/
theorem weight_eq_zero_of_rightPoint_ne_zero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4)
    (hi : T.rightPoint i ≠ 0) :
    C.weight i = 0 := by
  apply
    integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
      C.weight
      (firstContactTerminalRightConstantSection T)
      C.rightPointIntegrality
      i
  unfold firstContactTerminalRightConstantSection polynomialConstantSection
  simpa using hi

/-- Contrapositive form: every positive-weight terminal coordinate of the
right collision point is zero. -/
theorem rightPoint_eq_zero_of_weight_ne_zero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4)
    (hi : C.weight i ≠ 0) :
    T.rightPoint i = 0 := by
  by_contra hpoint
  exact hi (C.weight_eq_zero_of_rightPoint_ne_zero i hpoint)

/-- A second marked terminal zero means a zero-weight coordinate distinct
from the distinguished longitudinal coordinate `0`. -/
def HasSecondMarkedTerminalZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) : Prop :=
  ∃ i : Fin 4, i ≠ 0 ∧ C.weight i = 0

/-- If no second zero weight exists, every transverse coordinate of the
right point vanishes.  Together with the already-green longitudinal value
`-1`, the right point is exactly the canonical negative longitudinal axis
point. -/
theorem rightPoint_eq_negativeLongitudinalAxis_of_noSecondZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (hno : ¬ C.HasSecondMarkedTerminalZero) :
    T.rightPoint =
      negativeLongitudinalAxisPoint (K := K) := by
  funext i
  by_cases hi : i = 0
  · subst i
    simpa [negativeLongitudinalAxisPoint, coordinateAxisPoint] using
      T.rightPoint_zero
  · have hweight : C.weight i ≠ 0 := by
      intro hzero
      exact hno ⟨i, hi, hzero⟩
    have hpoint : T.rightPoint i = 0 :=
      C.rightPoint_eq_zero_of_weight_ne_zero i hweight
    simp [negativeLongitudinalAxisPoint, coordinateAxisPoint, hi, hpoint]

/-- Hence the terminal first-contact collision has a sharp support
dichotomy: either the terminal cocharacter has a second zero direction, or
the collision is literally the marked-axis collision `0 ~ -e₀`. -/
theorem secondZero_or_rightPoint_negativeAxis
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    C.HasSecondMarkedTerminalZero ∨
      T.rightPoint =
        negativeLongitudinalAxisPoint (K := K) := by
  classical
  by_cases hsecond : C.HasSecondMarkedTerminalZero
  · exact Or.inl hsecond
  · exact Or.inr
      (C.rightPoint_eq_negativeLongitudinalAxis_of_noSecondZero hsecond)

/-- In the no-second-zero branch the exact terminal collision itself is
literally the canonical marked-axis collision. -/
theorem exactMarkedAxisCollision_of_noSecondZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (hno : ¬ C.HasSecondMarkedTerminalZero) :
    HasExactGradientCollision
      T.fibre
      (fun _ : Fin 4 => (0 : K))
      (negativeLongitudinalAxisPoint (K := K)) := by
  have hcoll := T.exactCollision
  rw [T.leftPoint_eq_zero,
    C.rightPoint_eq_negativeLongitudinalAxis_of_noSecondZero hno] at hcoll
  exact hcoll

/-- The terminal degree is strictly positive.  This follows from the
non-scalar residual direct-jump certificate and nonnegativity of the honest
source cocharacter. -/
theorem degree_pos
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    0 < (C.degree : ℤ) := by
  exact
    nonnegative_nonScalar_terminal_degree_pos
      C.residualNonScalarJump.1
      C.nonnegative

/-- Every terminal source weight is bounded above by the terminal weighted
degree.  This is useful in the next zero-count classification. -/
theorem weight_le_degree
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4) :
    (C.weight i : ℤ) ≤ (C.degree : ℤ) := by
  exact
    nonnegative_terminal_weight_le_degree
      C.residualNonScalarJump.1
      C.nonnegative
      i

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
