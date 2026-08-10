import HC4.Valuation.RigidClosingRecenteredSource
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
Smith departure frontier.

The input is no longer a bare evaluated matrix clock.  It is the canonically
recentered source-level record: the left moving section is literally zero,
the right section reduces to `e0`, the exact family collision is retained,
and the pure Hessian defect is unchanged.  A future implementation must
construct the terminal associated-graded fibre from this affine source data;
it may not silently identify the evaluated Schur block with that fibre. -/
def HasRigidClosingTerminalExtraction
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∀ _source : f.RigidClosingRecenteredSourceData,
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
  · let source0 := f.rigidClosingExactCollisionSourceData hclosing
    let source := source0.recenteredSourceData
    rcases hextract source with ⟨T⟩
    exact False.elim (T.impossible_of_JC2 hJC2)

end

end HC4.Valuation
