# Phase 75.12.5 — General four-block API sync

This patch repairs the restored `SmithFrontierFourBlockExtraction` dependency against the actual Phase 75.8 `GeneralFourBlock` implementation.

It adds the matrix-facing API that the extraction/rigid bridge uses:

- `GeneralFourBlock.matrix`
- `GeneralFourBlock.ofSymmetricMatrix`
- `GeneralFourBlock.matrix_ofSymmetricMatrix`
- `GeneralFourBlock.matrix_det`

It also replaces a brittle `simp` in `parameterFirstEquiv_C_X` by the exact pinned mathlib theorem `MvPolynomial.optionEquivLeft_X_none`.

No theorem assumptions are strengthened and no `sorry`, `admit`, `unsafe`, or axioms are introduced.
