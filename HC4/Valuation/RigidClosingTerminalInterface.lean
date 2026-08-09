import HC4.Valuation.RigidPacketZeroSchurBridge
import HC4.Newton.TerminalAssociatedGradedEndpoint

/-!
# Rigid closing to terminal associated-graded interface

The green rigid Schur clock now ends in a frontier-relative closing
certificate.  The terminal endpoint machinery consumes an actual polynomial
associated-graded collision datum.

This file names that last conversion exactly.  It does not postulate that a
matrix Schur clock is already a polynomial potential: an implementation must
construct the terminal fibre, its exact collision, and its certified endpoint
from the retained frontier-relative closing certificate.

Once this extraction is supplied, the rigid Smith branch has no remaining
terminal case under `JC₂`: it must make strict rank-two repair progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The exact remaining terminal extraction interface for one canonical
Smith departure frontier.  The source is now provenance-preserving, so an
implementation has access to the actual defect-preserving family and its
left/right rigid chart. -/
def HasRigidClosingTerminalExtraction
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∀ _hclosing : f.RigidClosingCertificate,
    Nonempty (TerminalAssociatedGradedCollisionData K)

/-- Under `JC₂`, a completed closing-to-terminal extraction eliminates the
closing alternative and leaves strict rank-two repair progress. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_of_JC2_of_closingExtraction
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D)
    (hextract : HasRigidClosingTerminalExtraction f) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity) := by
  rcases f.rankTwoProgress_or_rigidClosingCertificate hD with
    hprogress | hclosing
  · exact hprogress
  · rcases hextract hclosing with ⟨T⟩
    exact False.elim (T.impossible_of_JC2 hJC2)

end

end HC4.Valuation
