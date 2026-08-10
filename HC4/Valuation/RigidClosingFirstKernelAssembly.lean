import HC4.Valuation.RigidClosingFirstKernelStage

/-!
# Canonical frontier assembly through the first global closing stage

Phase 75.12--75.16 reduced the rigid Smith branch to a provenance-preserving
closing certificate and recentered its actual moving collision.  Phase 75.17
now replaces that abstract closing branch by a source-level finite-support
trichotomy.

This file performs the short assembly back at the canonical frontier:

* immediate strict rank-two repair progress; or
* a direct first kernel stage with zero residual determinant clock; or
* an integral first kernel stage with a positive residual clock; or
* an explicit supported source monomial whose coefficient is not integral
  for the candidate closing blow-up.

The last two branches are exactly the two tasks for the next phase:
continue the retained residual rank-one clock, or use the offender to make a
strict Newton/valuation refinement.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Source-level resolution data replacing a bare rigid-closing proposition. -/
def HasRigidClosingFirstKernelResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∃ S : f.RigidClosingRecenteredSourceData,
    ∃ B : ExactZeroSchurFourBlockData K,
      B.defect = alignedSmithRamificationIndex * f.defect ∧
      ((B.toClock.residualDefect = 0 ∧
          S.HasIntegralRigidClosingFirstKernelStage B) ∨
       (0 < B.toClock.residualDefect ∧
          S.HasIntegralRigidClosingFirstKernelStage B) ∨
       S.HasRigidClosingFirstKernelOffender B)

/-- Every rigid closing certificate produces the concrete first-stage source
resolution data. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingCertificate.toFirstKernelResolution
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (hclosing : f.RigidClosingCertificate) :
    HasRigidClosingFirstKernelResolution f := by
  let source := f.rigidClosingExactCollisionSourceData hclosing
  let S := source.recenteredSourceData
  rcases S.firstClosingKernelStage_terminal_or_residual_or_offender with
    ⟨B, hBdef, hout⟩
  exact ⟨S, B, hBdef, hout⟩

/-- **Canonical rigid frontier after Phase 75.17.**

The old terminal/closing alternative is now replaced by an actual
source-family resolution carrying either an integral first stage or an
explicit finite-support obstruction. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_firstKernelResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidClosingFirstKernelResolution f := by
  rcases f.rankTwoProgress_or_rigidClosingCertificate hD with
    hprogress | hclosing
  · exact Or.inl hprogress
  · exact Or.inr hclosing.toFirstKernelResolution


/-- Strong first-stage resolution: an explicit source offender has already
been discharged as far as the existing one-coordinate integral-slope machine
can take it.  Thus only the genuinely anisotropic zero-maximal-slope
obstruction remains alongside direct/residual integral stages and a concrete
strict restart certificate. -/
def HasRigidClosingFirstKernelEndgameResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∃ S : f.RigidClosingRecenteredSourceData,
    ∃ B : ExactZeroSchurFourBlockData K,
      B.defect = alignedSmithRamificationIndex * f.defect ∧
      ((B.toClock.residualDefect = 0 ∧
          S.HasIntegralRigidClosingFirstKernelStage B) ∨
       (0 < B.toClock.residualDefect ∧
          S.HasIntegralRigidClosingFirstKernelStage B) ∨
       S.HasRigidClosingZeroCommonKernelSlopeObstruction ∨
       S.HasRigidClosingStrictKernelRestart)

/-- Every rigid closing certificate admits the strengthened first-stage
resolution.  The finite-support offender branch is immediately routed
through maximal integral slope extraction: positive slope gives a concrete
restart certificate; maximal slope zero is retained as the sole unresolved
anisotropic obstruction. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingCertificate.toFirstKernelEndgameResolution
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (hclosing : f.RigidClosingCertificate) :
    HasRigidClosingFirstKernelEndgameResolution f := by
  let source := f.rigidClosingExactCollisionSourceData hclosing
  let S := source.recenteredSourceData
  rcases S.firstClosingKernelStage_terminal_or_residual_or_offender with
    ⟨B, hBdef, hdirect | hresidual | hoffender⟩
  · exact ⟨S, B, hBdef, Or.inl hdirect⟩
  · exact ⟨S, B, hBdef, Or.inr (Or.inl hresidual)⟩
  · rcases S.firstKernelOffender_zeroSlope_or_strictRestart B hoffender with
      hzero | hrestart
    · exact ⟨S, B, hBdef, Or.inr (Or.inr (Or.inl hzero))⟩
    · exact ⟨S, B, hBdef, Or.inr (Or.inr (Or.inr hrestart))⟩

/-- **Canonical rigid frontier after the strengthened Phase 75.17 split.**

A bare rigid closing no longer survives.  The source-level alternatives are:

1. an honest first kernel stage already at determinant defect zero;
2. an honest first kernel stage retaining a positive residual clock;
3. the unique zero-maximal-slope anisotropic obstruction; or
4. a concrete strict polynomial-family restart certificate.
-/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_firstKernelEndgameResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidClosingFirstKernelEndgameResolution f := by
  rcases f.rankTwoProgress_or_rigidClosingCertificate hD with
    hprogress | hclosing
  · exact Or.inl hprogress
  · exact Or.inr hclosing.toFirstKernelEndgameResolution

end

end HC4.Valuation
