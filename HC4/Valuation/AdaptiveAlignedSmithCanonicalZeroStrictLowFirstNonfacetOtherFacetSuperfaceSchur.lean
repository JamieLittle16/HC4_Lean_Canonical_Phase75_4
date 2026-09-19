import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfacePivot
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import Mathlib.Tactic

/-!
# A19.127: cyclic coordinate permutations for the closing Schur blocks

The first-superface support package remains useful for identifying the three
cyclic active coordinate pairs.  The historical attempt to deduce singularity
of the larger first superface directly from singularity of the smaller contact
face was invalid and is deliberately not retained here.

The current A19.135--A19.136 closing route uses these same permutations on the
honest binary contact family, where cleared-Schur coefficient vanishing comes
from the determinant clock rather than from a false superface-singularity
shortcut.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Put the `.pr` active pair `(2,3)` into four-block coordinates `(0,1)`. -/
def qsPrSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3).trans
    (Equiv.swap (0 : Fin 4) 2)

/-- Put the `.sp` active pair `(1,3)` into four-block coordinates `(0,1)`. -/
def qsSpSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)

/-- Put the `.rq` active pair `(1,2)` into four-block coordinates `(0,1)`. -/
def qsRqSuperfaceSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)

end

end HC4.Valuation
