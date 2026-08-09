# Phase 83.1 fixes

Phase 83 reached only two failures, both in scalar evaluation lemmas for the
rank-three target numerator/denominator polynomials. After `simp` unfolded the
polynomial definitions, the remaining goals differed only by commutative-ring
normalisation (`w_i * rho` versus `rho * w_i`, reassociation, etc.).

Phase 83.1 changes only those two proofs by appending `<;> ring` to the existing
`simp` calls. No definitions, theorem statements, hypotheses, or fraction-field
bridge code changed.
