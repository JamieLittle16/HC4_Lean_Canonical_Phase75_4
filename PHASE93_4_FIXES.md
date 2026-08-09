# Phase 93.4 — Smith collision forces rank-one quadratic

## New module

    HC4/Newton/SmithCollisionQuadraticRankOne.lean

The latest restart proof sharpens the Phase 92 rank-one packet dichotomy.

At the first nonzero transverse collision wall, the leading transverse
gradient of the persistent binary quadratic vanishes at a nonzero point.
A nondegenerate binary quadratic has an invertible linear gradient map, so
this is impossible.

This phase formalises that argument entirely through already-green
infrastructure.

It proves the reusable binary lemma

    BinarySchurBlock.detCore_eq_zero_of_nonzero_kernel

from the Phase 92.3 trivial-kernel theorem.

For the persistent packet quadratic

    A Y^2 + B Y Z + C Z^2

the predicate

    HasPersistentQuadraticGradientZero

records

    2 A Y + B Z = 0
    B Y + 2 C Z = 0.

Lean proves that these are exactly the kernel equations of the
denominator-cleared Phase 92 block. Hence a nonzero transverse wall point
forces

    detCore = 0

and, in characteristic zero,

    discriminant = 0.

Finally,

    rankOnePersistentPacket_rigid_of_nonzero_collision

combines packet support, nonzeroness, a nonzero collision point and the
leading gradient equations to conclude the Phase 93 rigid rank-one
square/axis certificate directly.

Thus the nondegenerate rank-two branch of the abstract Phase 92 dichotomy is
eliminated at the actual first nonzero collision wall.

After this theorem, the latest restart audit says the remaining RS1
interface is the directional first-wall exclusion: low transverse blockers
and the w-linear zero-grade wall must be excluded in a pole-minimal exact
collision.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
