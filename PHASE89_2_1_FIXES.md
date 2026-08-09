# Phase 89.2.1 fixes

Affected file:

    HC4/Newton/LexicographicInitialForm.lean

The mathematical statement of Phase 89.2 is unchanged.

This repair addresses three Lean elaboration issues:

1. The parser rejected the bounded `∑ d in ...` syntax in this import context.
   The definition now uses explicit `Finset.sum`.
2. The predicates `IsScaledMaxOn` and `IsLexMaxOn` contain universal
   quantification, so raw `Finset.filter` expressions require classical
   decidability. `classical` is now introduced before the corresponding
   local type is elaborated.
3. The support-level public theorem no longer exposes a raw filter with an
   implicit undecidable predicate. Classical predicate selection is
   encapsulated in the noncomputable `selectedSupport` definition.

No theorem is weakened or mathematically changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
