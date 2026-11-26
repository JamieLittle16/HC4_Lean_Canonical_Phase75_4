import HC4.FinalEquivalence
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-!
# Declaration dependency export

Run from the repository root after building HC4.FinalEquivalence:

    lake env lean tools/ExportProofDependencies.lean

This is a diagnostic, not a new mathematical theorem. Walk the checked
environment using the same constant-dependency convention as
Lean.Util.CollectAxioms (types, values including opaque proofs, inductive
constructors; quotient primitives are leaves). Export actual constant
references, not source imports or guessed names. Include external libraries
and private/generated declarations; classify by defining module later.
-/

open Lean

namespace HC4DependencyExport

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => toString (env.allImportedModuleNames[idx.toNat]!)
  | none => "<no imported module>"

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def dependencies (ci : ConstantInfo) : Array (String × Name) := Id.run do
  match ci with
  | .quotInfo _ => return #[]
  | _ =>
    let mut out := ci.type.getUsedConstants.map (fun n => ("type", n))
    if let some v := ci.value? (allowOpaque := true) then
      out := out ++ v.getUsedConstants.map (fun n => ("value", n))
    if let .inductInfo v := ci then
      out := out ++ v.ctors.toArray.map (fun n => ("constructor", n))
    return out

def exportGraph (env : Environment) (roots : Array Name) : IO Unit := do
  IO.FS.createDirAll "proof-dependencies"
  IO.FS.withFile "proof-dependencies/nodes.tsv" .write fun nodes => do
    IO.FS.withFile "proof-dependencies/edges.tsv" .write fun edges => do
      nodes.putStrLn "declaration\tmodule\tkind"
      edges.putStrLn "source\ttarget\trelation"
      let mut visited : NameSet := {}
      let mut pending := roots
      let mut count : Nat := 0
      let mut edgeCount : Nat := 0
      while !pending.isEmpty do
        let n := pending.back!
        pending := pending.pop
        unless visited.contains n do
          visited := visited.insert n
          let some ci := env.checked.get.find? n
            | throw (IO.userError s!"Missing checked constant: {n}")
          count := count + 1
          nodes.putStrLn s!"{n}\t{moduleOf env n}\t{kindOf ci}"
          for (relation, target) in dependencies ci do
            edges.putStrLn s!"{n}\t{target}\t{relation}"
            edgeCount := edgeCount + 1
            unless visited.contains target do
              pending := pending.push target
      IO.println s!"Exported {count} reachable declarations and {edgeCount} typed edges."

end HC4DependencyExport

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let roots := #[``HC4.StatementAudit.jc2_iff_hc4_explicit,
    ``HC4.Polynomial.hc4_of_planarJC2]
  HC4DependencyExport.exportGraph env roots
