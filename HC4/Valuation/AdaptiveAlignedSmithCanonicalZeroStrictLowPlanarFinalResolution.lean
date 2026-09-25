import HC4.Valuation.PlanarKellerCollisionTerminalLift
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution

/-!
# Explicit planar Keller collisions are permitted zero-strict-low resolutions

The final zero-strict-low interface accepts an honest terminal
associated-graded collision. `PlanarKellerCollisionTerminalLift` constructs
exactly such a collision by normalising the planar Jacobian and taking the
standard four-variable Hessian doubling potential.

This file is the thin E-stage adapter: whenever the remaining geometry
produces a genuine `PlanarKellerCollisionData`, it can be returned immediately
as the existing `associatedGradedCollision` final-resolution constructor.
No new endpoint class is introduced.
-/

namespace HC4.Newton

noncomputable section

open HC4.Valuation

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace PlanarKellerCollisionData

/-- A genuine planar Keller collision is already a permitted final resolution
for any concrete singular strict-low terminal from which it was extracted. -/
noncomputable def toZeroStrictLowSingularFinalResolution
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : PlanarKellerCollisionData K)
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T :=
  .associatedGradedCollision P.toTerminalAssociatedGradedCollisionData

/-- Proposition-facing form convenient inside E-stage case splits. -/
theorem exists_zeroStrictLowSingularFinalResolution
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : PlanarKellerCollisionData K)
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  ⟨P.toZeroStrictLowSingularFinalResolution T⟩

end PlanarKellerCollisionData

/-- Existential planar Keller collision witnesses are already sufficient for a
permitted final resolution.  This is the form consumed by the mature A19
first-contact and standard two-zero endpoint theorems. -/
theorem HC4.HasPlanarKellerCollision.exists_zeroStrictLowSingularFinalResolution
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.HasPlanarKellerCollision K)
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases h.exists_terminalAssociatedGradedCollisionData with ⟨A⟩
  exact ⟨.associatedGradedCollision A⟩

end

end HC4.Newton
