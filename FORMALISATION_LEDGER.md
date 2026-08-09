# Manuscript-to-Lean ledger — Phase 75.2

Status labels:

- **Verified** — represented by proved Lean theorems in the cumulative source.
- **Substantial verified core** — major lemmas are proved, but the exact
  manuscript theorem/assembly is not yet present.
- **Missing / open formalisation obligation** — required before the paper's
  top classification theorem can be certified.

| Manuscript component | Lean status | Notes |
|---|---|---|
| Toric invariant cone / exponent normal forms | Verified / substantial core | `HC4/Toric/*` |
| Weighted initial-form calculus | Verified | `HC4/Polynomial/WeightedInitial.lean`, Hessian/Monge–Ampère bridge files |
| First non-facet contact construction | Verified / substantial core | `HC4/Newton/FirstNonfacetContact.lean` and related files |
| Boundary-cycle combinatorics | Verified / substantial core | `BoundaryCycle`, `FourBoundaryCycle`, `FacetCycleClassification` |
| Sparse/rank-three pencil determinant algebra | Verified | `RankThreePencils`, `RankThreeLinearCoefficient` |
| Complementary rank-two edge: local logarithmic/moment obstruction | Verified | Phases 68–72 infrastructure |
| Actual `MvPolynomial` complementary-line bridge | Verified | `ComplementaryMvSubstitution`, `ComplementaryMvMomentRealisation` |
| Complementary-edge endpoint theorem | **Verified** | `complementary_line_hessian_impossible` |
| Explicit inverse of classified `r`/`s` gradient families | Verified | `HC4/ClassifiedFamilies/*`, `MainAssembly.lean` |
| Exceptional arithmetic `(a,b)=(2,1)` from divisibility condition | Verified | `HC4/Toric/ExceptionalGrading.lean` |
| Gordan–Noether homogeneous zero-Hessian cone step (or specialised replacement) | **Missing** | Needed to derive the top-degree facet/cone conclusion from Hessian singularity rather than assume it upstream |
| Torus-stability / coordinate-character consequence paired with GN | **Missing as complete manuscript bridge** | Some toric character arithmetic exists, but not the full GN-to-coordinate omission theorem |
| Autonomous ODE front half: `t rho' = R(rho)` forces logistic/separated binomial ODE | **Missing** | `AutonomousODEReconstruction.lean` formalises only the reconstruction after the separated ODE is known |
| Complete rank-three edge rigidity theorem | **Not yet assembled** | Pencil algebra is verified; autonomous rational/projective forcing remains |
| Schur/binary-Hessian/eigenfunction argument producing the Laurent coefficient ratio for a four-sided face | **Missing** | `HC4/Toric/FourSidedCharacter.lean` explicitly treats this as a separate remaining obligation |
| Exceptional `(2,1)` four-sided exclusion in full manuscript form | **Not yet assembled** | Combinatorics/arithmetic pieces exist, upstream analytic/algebraic bridge remains |
| Full facet-supported potential classification `p+q+P(r)` or `p+q+Q(s)` from manuscript hypotheses | **Not yet assembled** | Terminal Euler/classified-family machinery exists |
| Final global Newton/branch assembly | **Missing** | No theorem yet derives `HasClassifiedPolynomialGradient` from the original paper hypotheses |
| Paper top theorem / symmetric-gradings classification | **Missing** | Required for final machine-checked-paper certification |

## Recommended next order

1. Formalise the autonomous-ODE **front half** and close the complete rank-three
   edge theorem.
2. Formalise the Gordan–Noether/torus top-degree step, or replace it by a
   specialised toric theorem with the same consequence.
3. Close the four-sided/exceptional branch, including the missing
   Schur/binary-Hessian-to-Laurent-ratio bridge.
4. Assemble facet rigidity and the global Newton dispatch into a single
   classification theorem matching the manuscript statement.
5. Add that top theorem to `HC4/Audit.lean`, run the full negative-control and
   forbidden-token audit, and freeze a final pinned release archive.
