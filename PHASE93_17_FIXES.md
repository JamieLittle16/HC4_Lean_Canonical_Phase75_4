# Phase 93.17 — canonical refined-face polynomial and rigid packet assembly

## New module

    HC4/Newton/SmithRefinedFacePolynomial.lean

Phase 93.16 required an externally supplied homogeneous polynomial supported
on the symmetric Smith refined subface.

This phase constructs that polynomial canonically by filtering the original
polynomial's finitely supported coefficient function.

The new definition

    smithSubfacePolynomial y z w T F

retains exactly the monomials whose Smith projection lies in `T`.

Lean then proves:

* the exact coefficient formula for the restriction;
* automatic support on `T`;
* preservation of ordinary homogeneity;
* realisation of projected Smith support by actual nonzero monomials;
* nonvanishing of the restriction when `T` is nonempty and realised.

The theorem

    poleMinimal_symmetricSmithRestriction_rankOnePacket

therefore removes the external `IsSupportedOnSmithSubface` assumption from
Phase 93.16: the canonical restriction automatically lands in the green
Phase 92 rank-one packet model.

Finally

    poleMinimal_symmetricSmithRestriction_rigid_of_nonzero_collision

assembles the entire local chain.  Once the restart geometry supplies a
nonzero transverse wall point `(Y,Z)` and the Phase 93.4 leading transverse
gradient equations for the canonical restriction, the packet is forced to
the rigid discriminant-zero square/axis branch.

This sharply isolates the next genuinely geometric input: derive
`HasPersistentQuadraticGradientZero` at the first nonzero transverse wall
for the canonical refined packet.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
