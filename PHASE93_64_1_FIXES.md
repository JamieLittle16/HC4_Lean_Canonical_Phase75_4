# Phase 93.64.1 — Special-fibre support timeout fix

The first Phase 93.64 build exposed two proof-engineering issues.

## 1. Avoid expensive `support_map_subset`

The proof of

    mem_polynomialFamilySpecialFiber_support_iff

timed out while reducing `MvPolynomial.support_map_subset`.

The replacement proof works coefficientwise:

- membership in the special-fibre support gives a nonzero mapped
  coefficient;
- `coeff_map` identifies it with the constant coefficient of the original
  family coefficient;
- a nonzero constant coefficient immediately implies the original
  coefficient is nonzero;
- source support membership then follows from `mem_support_iff`.

This removes the expensive support-map normalization entirely.

## 2. Base-zero strict-improvement branch

The family strict-improvement target contains the function

    fun e => (smithBinaryBase P e : Z).

Knowing `smithBinaryBase P e = 0` does not make `simp` rewrite that function
under the opaque Smith tilt definition automatically.

The proof now explicitly unfolds

    smithIntegralSeparatorTilt
    finiteIntegralRescaledTilt

in both the target and the special-fibre hypothesis, rewrites the single
value with `hzero`, and closes by `simpa`.

## 3. Minor cleanup

The non-survival contradiction now uses the available nonzero
constant-coefficient hypothesis directly rather than simplifying the
`constantCoeff` definition.

No theorem statement or mathematical content changes.
