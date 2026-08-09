# Phase 92.1 — rank-one persistent packet support

## New module

    HC4/Newton/RankOnePersistentPacket.lean

With the rank-two homogeneous classification closed in Phase 91, this phase
begins the rank-one branch.

It formalises the support-theoretic packet shape

    x^(D-2) * q(y,z).

The predicate

    HasRankOnePersistentPacketSupport

requires every nonzero monomial to have:

    exponent(x) = D-2
    exponent(y) + exponent(z) = 2

and zero exponent in every other variable.

For pairwise distinct `x,y,z`, Lean proves that every support monomial is
exactly one of:

    x^(D-2) y^2
    x^(D-2) y z
    x^(D-2) z^2.

The theorem

    rankOnePersistentPacket_support_cases

is the support trichotomy, and

    coeff_eq_zero_outside_rankOnePacket

shows every other coefficient vanishes.

The three canonical packet coefficients are then exposed as

    rankOnePacketCoeffYY
    rankOnePacketCoeffYZ
    rankOnePacketCoeffZZ.

The next phase can package them as a binary quadratic and classify its
rank/determinant alternatives.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
