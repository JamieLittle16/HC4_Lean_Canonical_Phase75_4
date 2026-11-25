# Next research steps

Checkpoint 25 November 2026. These are proposed investigation tasks, not claimed proved implications.

1. **Audit the latest mixed-residue theorem.** Open `sourceCubic_fixedMixedResidue_global_directionalSquare_eq_zero` at the end of [TransverseLeadingFirstCorrection.lean](../HC4/Polynomial/TransverseLeadingFirstCorrection.lean). Record the exact source of each premise: cap 3, constant determinant, anchor and nilpotent transport, prime p and p(0)=0, fixed nonzero direction d, principal cofactor survival, orthogonality, nonzero residue and the cleared mixed equation. Distinguish premises already derivable from those still required.
2. **Consume the directional square identity.** Investigate constant shear to an affine-in-one-direction source and whether determinant-one plus the actual collision gives a contradiction or a lower-dimensional endpoint. First search existing stationary, nilpotent and marked-collision consumers in the same file. Do not assume a generic affine-in-one-direction source is impossible.
3. **Close the complementary cases.** Audit the stationary, nonzero linear and genuine rational characteristic branches and the singular leading transverse block. The squarefree pole and rank-one pole results only exclude their respective hypotheses. Do not claim a cap-three theorem until the branches are exhaustive.
4. **Integrate with the global proof.** For the cap-two marked theorem and any new cap-three result, identify the exact canonical state and prove its weight-bound/collision adapter. For conditional HC4 discharge the extraction or producer hypothesis rather than adding a caller-supplied resolver; for unrestricted HC4 discharge reachable-terminal impossibility without JC2.
5. **Certify at each step.** Focused module build, full root build at a milestone, and endpoint axiom audit. Record commit and build result; no `sorry`, `admit` or new axioms. Keep the source-derived index fresh.

## Maintenance sequence (separate from proof work)

The current correction module is large. Split only after establishing declaration dependencies and a verified baseline. Keep names and compatibility imports, audit any private helpers and preserve the original import surface. Build each slice and the original aggregate; avoid simultaneous mathematical changes. A wider valuation reorganisation is deferred.

Do not use the September handoffs as current plans. They are preserved in the [historical checkpoint](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/tree/90b9d97e2937b34c12c2ab845a404048f4a3c4b1/docs).
