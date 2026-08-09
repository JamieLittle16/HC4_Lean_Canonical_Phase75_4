# Phase 93.67.2 — Product expansion fix

The Phase 93.67.1 build reduced the large first-stop construction to one
remaining arithmetic failure.

`omega` treats the nonlinear-looking product

    N * (raw - 4)

as an opaque atom and therefore cannot derive

    4*N <= N*raw + 20*v

from

    0 <= 20*v + N*(raw - 4).

The proof now inserts the exact ring identity

    20*v + N*(raw - 4)
      = N*raw + 20*v - 4*N

using `ring`, rewrites the nonnegativity hypothesis into that linear normal
form, and then closes the inequality with `omega`.

No theorem statement, assumption, or mathematical content changes.
