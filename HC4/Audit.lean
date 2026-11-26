import HC4
import Lean.Util.CollectAxioms

#print axioms HC4.Polynomial.hc4_of_planarJC2
#print axioms HC4.StatementAudit.planarJC2_iff_hessianFour_injective
#print axioms HC4.StatementAudit.referenceJC2_iff_referenceHC4
#print axioms HC4.StatementAudit.jc2_iff_hc4_explicit
#print axioms HC4.Polynomial.RankThreeCubic.rationalMap_affinePlane

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``HC4.Polynomial.hc4_of_planarJC2,
      ``HC4.StatementAudit.planarJC2_iff_hessianFour_injective,
      ``HC4.StatementAudit.referenceJC2_iff_referenceHC4,
      ``HC4.StatementAudit.jc2_iff_hc4_explicit,
      ``HC4.Polynomial.RankThreeCubic.rationalMap_affinePlane] do
    for dep in (← Lean.collectAxioms decl) do
      unless allowed.contains dep do
        throwError "Unexpected logical dependency {dep} in {decl}"
