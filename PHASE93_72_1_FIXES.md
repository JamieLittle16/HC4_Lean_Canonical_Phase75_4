# Phase 93.72.1 — parser and integer-cast fix

The initial Phase 93.72 build failed mostly because `section` was used as a
structure field name.  In Lean, `section` is a command keyword, so the
structure stopped parsing at that field; all later missing-field and scope
errors were parser fallout.

## Fixes

1. Rename the geometric-state field

       section

   to

       movingSection

   and update all projections / record construction.

2. Replace the two failing direct `exact_mod_cast` proofs into targets of
   the form

       1 <= A - 4*N

   by a stable two-stage argument:

   - first cast the natural inequality
         4*N + 1 <= A
     to the integer inequality
         (4*N + 1 : Z) <= A_Z;
   - then derive
         1 <= A_Z - 4*N
     with `omega`.

This avoids Lean translating natural subtraction through `Int.subNatNat`.

No theorem statement is weakened.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
