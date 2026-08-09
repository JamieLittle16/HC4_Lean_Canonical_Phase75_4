# Phase 75.5.1 — direct antidiagonal fix

Repairs the two convolution lemmas in `FirstSchurLayerLinearization.lean`.

The previous proof tried to rewrite an antidiagonal sum through a range theorem whose
left-hand side did not syntactically match the already-elaborated sum.  This patch
avoids that conversion entirely:

* `A*C`: `Finset.sum_eq_single (0,j)` directly on `Finset.antidiagonal j`; every
  other pair has second coordinate `< j`, hence its `C` coefficient vanishes.
* `B*B`: `Finset.sum_eq_zero`; on an antidiagonal of positive total `j`, at least
  one coordinate is `< j`, hence one `B` coefficient vanishes.

No theorem statements or downstream interfaces are changed.
