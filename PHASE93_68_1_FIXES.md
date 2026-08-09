# Phase 93.68.1 — Common-factor proof normalisation fix

The first Phase 93.68 build reduced the large genuine-endpoint theorem to
two local proof-shape issues inside the common-factor argument.

## 1. Natural exponent normalisation

The integer estimate naturally produces

    6*N <= N*raw + 20*v,

while the polynomial exponent target is written as

    4*N + 2*N <= ...

The proof now records explicitly

    4*N + 2*N = 6*N

before `exact_mod_cast`.

## 2. Smith quotient identity orientation

The available exact factorisation theorem states

    factor * coeff
      = multiplier * quotient.

The previous proof tried to rewrite a target already simplified to
`X^(4*N) * quotient`, so the left-hand pattern was no longer present.

The proof now first transports `hbig` to the unsimplified target

    multiplier * quotient

using `rw [← hspec]`, then simplifies the multiplier separately to
`X^(4*N)`.

No theorem statement, assumption, or mathematical content changes.
