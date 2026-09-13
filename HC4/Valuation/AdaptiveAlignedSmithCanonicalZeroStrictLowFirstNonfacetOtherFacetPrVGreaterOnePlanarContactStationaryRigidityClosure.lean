import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinarySchurSingularity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryRigidity

/-!
# A19 rooted stationary rigidity compatibility seam

This module intentionally contains no mathematical declarations.  The former
`StationaryRigidityClosure` implementation was removed because its theorem was
a duplicate of the canonical theorem now living in
`...PlanarContactStationaryRigidity`.

`HC4.lean` still roots this historical module path, so keep it as a thin import
seam until the root inventory is next reorganised.  Rooting both imports here
also ensures CI checks the source-honest planar binary Schur singularity and
the canonical stationary residual-to-no-interior adapter.
-/
