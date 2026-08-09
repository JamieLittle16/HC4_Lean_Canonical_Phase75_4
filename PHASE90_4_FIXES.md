# Phase 90.4 — explicit 4x4 rank-two Schur lift

## New module

    HC4/Newton/RankTwoFourBlockSchur.lean

This phase lifts the verified binary Schur machinery into the adapted 4x4
rank-two block used by the corank-entry argument.

For

    [ a  0  p  q ]
    [ 0  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ],

define the denominator-cleared Schur entries

    U = a*d*x - d*p^2 - a*r^2
    V = a*d*y - d*p*q - a*r*s
    W = a*d*z - d*q^2 - a*s^2.

Lean proves the exact identity

    U*W - V^2 = (a*d) * determinantCore(H).

Hence determinant-zero of the 4x4 block implies determinant-zero of its
binary Schur block. If that Schur block is nonzero, the already-verified
Phase 90.1 theorem produces the required rank-one pivot certificate.

The proof uses explicit polynomial identities (`ring`) and no general
matrix Schur-complement or Smith-normal-form API.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
