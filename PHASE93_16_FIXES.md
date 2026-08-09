# Phase 93.16 — symmetric Smith refined face to rank-one packet

The green Phase 93.15 symmetric refinement gives only the three transverse
Smith exponent patterns `(0,2,0)`, `(1,1,0)`, `(2,0,0)`.

This phase introduces the projection from a polynomial multi-index to its
Smith triple and proves that any homogeneous polynomial supported on that
refined subface satisfies the already-green Phase 92 predicate
`HasRankOnePersistentPacketSupport`.

The proof does not assume the longitudinal exponent.  In a four-coordinate
chart, the refined Smith pattern gives transverse degree two and zero
w-exponent; homogeneity then forces the x-exponent to be `D-2`.

The main theorem is:

    poleMinimal_symmetricSmithRefinement_rankOnePacket

It packages nonemptiness of the refined subface together with the Phase 92
rank-one packet support conclusion.

The remaining global adapter is to construct the actual homogeneous
refined-face polynomial and establish the support-on-subface predicate for
it.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
