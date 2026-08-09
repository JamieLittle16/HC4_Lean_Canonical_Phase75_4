# Phase 93.56.2 — Chain-rule induction hypothesis fix

The Phase 93.56.1 build reduced the file to two root problems.

## 1. `bind₁` form of the induction hypothesis

Inside the `p * X n` branch, simplification unfolds
`kernelInflateHom` to `MvPolynomial.bind₁`.  The induction hypothesis was
still stated using `kernelInflateHom`, so `simp [hp]` could not rewrite the
derivative of the bound polynomial.

The branch now first derives the syntactically matching hypothesis `hp'`:

    pderiv i (bind₁ inflateVariable p)
      =
    C factor_i * bind₁ inflateVariable (pderiv i p).

Both the `n = i` and `n != i` branches then simplify with `hp'` and close
by commutative-ring normalisation.

## 2. Orientation of `RingHom.map_det`

Mathlib states

    f (det M) = det (f.mapMatrix M).

The local helper needs the reverse orientation, so the proof now uses
`(RingHom.map_det ...).symm`.

No theorem statements, hypotheses, or mathematical content are changed.
