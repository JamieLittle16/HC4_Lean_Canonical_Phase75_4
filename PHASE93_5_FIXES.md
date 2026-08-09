# Phase 93.5 — elementary Smith-grade arithmetic

## New module

    HC4/Newton/SmithGradeArithmetic.lean

This phase formalises the lattice arithmetic from the RS1 Smith-wall
reduction.

For a monomial `x^a y^b z^c w^d` it defines

    Gamma_1 = b + d - 1
    Gamma_2 = c + d - 1

as integer-valued grades.

Lean proves:

* negative first grade => `b = d = 0`, and the first grade is exactly `-1`;
* negative second grade => `c = d = 0`, and the second grade is `-1`;
* after excluding the low first-wall grades, a surviving negative coordinate
  has the shape `(-1,k)` or `(l,-1)` with `k,l >= 1`;
* zero grade has exactly two exponent patterns:
      `yz`, or the `w`-linear wall;
* after excluding the `w`-linear wall, zero grade is exactly `yz`;
* the target quadratic monomials have grades:
      z^2 -> (-1,1)
      yz  -> (0,0)
      y^2 -> (1,-1);
* once convex balance supplies `k*l <= 1`, positivity forces `k=l=1`.

This deliberately stops before the pole-minimal convex-balance theorem.
The next phase can now formalise rational separation/finite balance on top
of a stable arithmetic interface.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
