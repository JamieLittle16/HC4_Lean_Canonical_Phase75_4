import HC4.Valuation.AlignedSmithEndpoint
import HC4.Valuation.PrimitiveSmithEndpoint

/-!
# Full spatial homogeneity through the aligned first-wall transform

The global restart state carries homogeneity of the whole polynomial family,
not merely of its special fibre.  The once-ramified aligned Smith first-wall
construction changes only the coefficient ring and therefore preserves the
source degree.  This small adapter exposes that fact at the exact transform
used by the departure frontier.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- The actual once-ramified aligned Smith first-wall family retains the full
spatial homogeneity of the incoming family. -/
theorem alignedSmithGenuineFirstWallFamily_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    (alignedSmithGenuineFirstWallFamily (K := K) P a b hwall).IsHomogeneous D := by
  unfold alignedSmithGenuineFirstWallFamily
  apply integralSmithConformalFamily_isHomogeneous
  exact hP.map _

end

end HC4.Valuation
