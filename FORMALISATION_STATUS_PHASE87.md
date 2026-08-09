# Formalisation status — Phase 87.1

Phase 87 remains the infinity-certificate layer for the logarithmic source.
Phase 87.1 only repairs elaboration/proof issues exposed by the user's pinned
Lean build.

Target statements remain:

- positive-degree Euler differentiation preserves natural degree;
- the canonical reduced numerator/denominator of `E(phi)/phi` have equal degree;
- the infinity value of the reduced logarithmic source is `natDegree phi`;
- the reduced eta numerator has degree strictly below twice the reduced source
  denominator degree;
- a singular rank-three endpoint core with eta=0 forces the raw autonomous
  numerator to vanish at that endpoint.

Status: candidate until `./verify.sh` is green on the user's pinned tree.
