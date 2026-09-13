import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStrata
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# A19 codimension-two top-face departure split

The A19.55 codimension-two branch stores two distinct zero coordinates of an
actual supported exponent on the same singular maximal ordinary top face.
Before doing any Hessian coefficient algebra, there is a simpler exhaustive
support split.

For either missing coordinate:

* if the top face has no supported monomial with positive exponent in that
  coordinate, then the corresponding formal source derivative vanishes
  identically, hence that coordinate is already a literal constant Hessian
  kernel direction;
* otherwise the finite positive-coordinate support is nonempty.

Thus a genuine two-sided codimension-two departure problem only remains when
both missing coordinates occur positively somewhere on the same top face.
This file retains those actual finite-support sets.  It does not project to a
planar/JC2 carrier and does not attach any repair progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Concrete A19.55 codimension-two data, keeping the two missing coordinates
and their actual zero support witness on the singular top face. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) where
  first : Fin 4
  second : Fin 4
  distinct : first ≠ second
  first_zero : T.exposedSingularBoundaryVertex.exponent first = 0
  second_zero : T.exposedSingularBoundaryVertex.exponent second = 0

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The stored boundary exponent gives a literal nonempty zero-coordinate
support slice in the first missing coordinate. -/
theorem first_zeroSupport_nonempty
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData T) :
    (zeroCoordinateSupport C.first T.topFace.face).Nonempty := by
  exact ⟨T.exposedSingularBoundaryVertex.exponent,
    mem_zeroCoordinateSupport.mpr
      ⟨T.exposedBoundary_exponent_mem_topFace, C.first_zero⟩⟩

/-- Cyclic companion for the second missing coordinate. -/
theorem second_zeroSupport_nonempty
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData T) :
    (zeroCoordinateSupport C.second T.topFace.face).Nonempty := by
  exact ⟨T.exposedSingularBoundaryVertex.exponent,
    mem_zeroCoordinateSupport.mpr
      ⟨T.exposedBoundary_exponent_mem_topFace, C.second_zero⟩⟩

/-- If no supported exponent leaves one coordinate hyperplane, the top face is
literally independent of that coordinate. -/
theorem pderiv_eq_zero_of_positiveCoordinateSupport_empty
    (F : MvPolynomial (Fin 4) K)
    (i : Fin 4)
    (hempty : (positiveCoordinateSupport i F).Nonempty → False) :
    MvPolynomial.pderiv i F = 0 := by
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hd
  by_contra hdi
  have hpos : 0 < d i := Nat.pos_of_ne_zero hdi
  exact hempty ⟨d, mem_positiveCoordinateSupport.mpr
    ⟨MvPolynomial.mem_support_iff.mpr hd, hpos⟩⟩

/-- **A19 same-carrier codimension-two departure frontier.**

Either one of the two missing coordinates is already a literal constant
source/Hessian kernel of the entire singular top face, or both coordinates
have genuine positive support on that same face. -/
theorem constantKernel_or_bothPositiveSupports
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData T) :
    MvPolynomial.pderiv C.first T.topFace.face = 0 ∨
      MvPolynomial.pderiv C.second T.topFace.face = 0 ∨
      ((positiveCoordinateSupport C.first T.topFace.face).Nonempty ∧
        (positiveCoordinateSupport C.second T.topFace.face).Nonempty) := by
  classical
  by_cases hfirst : (positiveCoordinateSupport C.first T.topFace.face).Nonempty
  · by_cases hsecond : (positiveCoordinateSupport C.second T.topFace.face).Nonempty
    · exact Or.inr (Or.inr ⟨hfirst, hsecond⟩)
    · exact Or.inr (Or.inl
        (pderiv_eq_zero_of_positiveCoordinateSupport_empty
          T.topFace.face C.second hsecond))
  · exact Or.inl
      (pderiv_eq_zero_of_positiveCoordinateSupport_empty
        T.topFace.face C.first hfirst)

end AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Package the codimension-two constructor of the A19.55 boundary stratum
without losing the actual two zero coordinates. -/
noncomputable def codimensionTwoTopFaceData_of_stratum
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i j : Fin 4)
    (hij : i ≠ j)
    (hi : T.exposedSingularBoundaryVertex.exponent i = 0)
    (hj : T.exposedSingularBoundaryVertex.exponent j = 0) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoTopFaceData T where
  first := i
  second := j
  distinct := hij
  first_zero := hi
  second_zero := hj

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
