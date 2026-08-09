import HC4.Newton.RestartClassification
import Mathlib.Tactic

/-!
# Global restart descent

The local repair system is already controlled by `RepairState.measure`.
The valuation restart has one additional, more significant coordinate:
the determinant defect.

This file formalises the exact lexicographic well-founded engine needed by
the global restart proof.

A global restart state records:

* `defect` — the nonnegative determinant defect;
* `repair` — the already-certified finite local repair state.

A genuine global step is either

1. a strict drop of determinant defect; or
2. the same determinant defect together with `RepairProgress`.

The crucial point is that a defect drop is allowed to reset the local repair
state completely.  Thus the proof cannot be replaced by a naive sum of the
two measures.  We instead prove termination by nested strong induction:
first on determinant defect, then on `RepairState.measure`.

For a positive integral kernel slope `q`, the arithmetic transformation

    Δ' = Δ - 2*q

is packaged separately.  Whenever `0 < q` and `2*q ≤ Δ`, it gives a strict
global restart step independently of the new local repair state.

This module is deliberately algebra/geometry agnostic: the later valuation
file must prove that the actual kernel blow-up preserves the exact collision
datum and has precisely this defect update.
-/

namespace HC4.Newton

noncomputable section

/-- State for the global restart induction. -/
structure GlobalRestartState where
  defect : ℕ
  repair : RepairState

/-- Lexicographic global progress:
determinant defect first, local finite repair measure second. -/
def GlobalRestartProgress
    (s t : GlobalRestartState) : Prop :=
  t.defect < s.defect ∨
    (t.defect = s.defect ∧
      RepairProgress s.repair t.repair)

/-- Any strict defect decrease is global restart progress, regardless of
what happens to the local repair state. -/
theorem globalRestartProgress_of_defect_lt
    {s t : GlobalRestartState}
    (hdefect : t.defect < s.defect) :
    GlobalRestartProgress s t :=
  Or.inl hdefect

/-- At fixed determinant defect, every certified local repair is a global
restart step. -/
theorem globalRestartProgress_of_repair
    {s t : GlobalRestartState}
    (hdefect : t.defect = s.defect)
    (hrepair : RepairProgress s.repair t.repair) :
    GlobalRestartProgress s t :=
  Or.inr ⟨hdefect, hrepair⟩

/-- Global restart progress is irreflexive. -/
theorem not_globalRestartProgress_self
    (s : GlobalRestartState) :
    ¬ GlobalRestartProgress s s := by
  intro h
  rcases h with hdefect | ⟨_hdefect, hrepair⟩
  · exact (Nat.lt_irrefl s.defect) hdefect
  · exact (not_repairProgress_self s.repair) hrepair

/-! ## Positive kernel-slope defect drop -/

/-- Arithmetic certificate corresponding to one positive integral
kernel Newton blow-up:

    Δ' = Δ - 2q.

The local repair component of `t` is intentionally unrestricted because a
defect-lowering valuation restart may expose a completely new local packet.
-/
def HasPositiveKernelDefectDrop
    (q : ℕ)
    (s t : GlobalRestartState) : Prop :=
  0 < q ∧
    2 * q ≤ s.defect ∧
    t.defect = s.defect - 2 * q

/-- A positive kernel-slope defect update is strictly defect lowering. -/
theorem positiveKernelDefectDrop_defect_lt
    {q : ℕ}
    {s t : GlobalRestartState}
    (hdrop : HasPositiveKernelDefectDrop q s t) :
    t.defect < s.defect := by
  rcases hdrop with ⟨hq, hqle, hdefect⟩
  rw [hdefect]
  omega

/-- Hence every positive kernel-slope defect update is automatically a
global restart step. -/
theorem globalRestartProgress_of_positiveKernelDefectDrop
    {q : ℕ}
    {s t : GlobalRestartState}
    (hdrop : HasPositiveKernelDefectDrop q s t) :
    GlobalRestartProgress s t :=
  globalRestartProgress_of_defect_lt
    (positiveKernelDefectDrop_defect_lt hdrop)

/-- The amount removed from the defect is nonzero. -/
theorem positiveKernelDefectDrop_two_q_pos
    {q : ℕ}
    {s t : GlobalRestartState}
    (hdrop : HasPositiveKernelDefectDrop q s t) :
    0 < 2 * q := by
  rcases hdrop with ⟨hq, _hqle, _hdefect⟩
  omega

/-- A positive kernel blow-up cannot preserve the determinant defect. -/
theorem positiveKernelDefectDrop_ne
    {q : ℕ}
    {s t : GlobalRestartState}
    (hdrop : HasPositiveKernelDefectDrop q s t) :
    t.defect ≠ s.defect := by
  exact
    Nat.ne_of_lt
      (positiveKernelDefectDrop_defect_lt hdrop)

/-! ## Global reachability -/

/-- Reflexive-transitive reachability by global restart steps. -/
inductive GlobalRestartReachable :
    GlobalRestartState -> GlobalRestartState -> Prop
  | refl (s : GlobalRestartState) :
      GlobalRestartReachable s s
  | step {s t u : GlobalRestartState}
      (hst : GlobalRestartProgress s t)
      (htu : GlobalRestartReachable t u) :
      GlobalRestartReachable s u

/-- Global restart reachability is transitive. -/
theorem GlobalRestartReachable.trans
    {s t u : GlobalRestartState}
    (hst : GlobalRestartReachable s t)
    (htu : GlobalRestartReachable t u) :
    GlobalRestartReachable s u := by
  induction hst generalizing u with
  | refl =>
      exact htu
  | step hxy hyz ih =>
      exact
        GlobalRestartReachable.step hxy (ih htu)

/-- One-step global restart interface. -/
def HasGlobalRestartOrTerminal
    (Terminal : Prop)
    (s : GlobalRestartState) : Prop :=
  Terminal ∨
    ∃ t : GlobalRestartState,
      GlobalRestartProgress s t

/-- A total global classifier supplies either a terminal certificate or one
strict lexicographic restart step at every state. -/
def IsTotalGlobalRestartClassifier
    (Terminal : GlobalRestartState -> Prop) : Prop :=
  ∀ s : GlobalRestartState,
    HasGlobalRestartOrTerminal (Terminal s) s

/-! ## Nested well-founded classification -/

/-- **Global restart termination/classification.**

Any total one-step global classifier reaches a terminal state after finitely
many restart steps.

This is the exact well-founded argument needed for the valuation restart:
the outer strong induction controls determinant defect.  At fixed defect,
the inner strong induction is on the already-proved finite
`RepairState.measure`.  A defect drop may therefore reset the local repair
measure arbitrarily without threatening termination.
-/
theorem globalRestartClassifier_reaches_terminal
    (Terminal : GlobalRestartState -> Prop)
    (hclassify : IsTotalGlobalRestartClassifier Terminal)
    (s : GlobalRestartState) :
    ∃ t : GlobalRestartState,
      GlobalRestartReachable s t ∧
        Terminal t := by
  have houter :
      ∀ d : ℕ,
        ∀ s : GlobalRestartState,
          s.defect = d ->
            ∃ t : GlobalRestartState,
              GlobalRestartReachable s t ∧
                Terminal t := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihDefect =>
      intro s hsdefect
      have hinner :
          ∀ m : ℕ,
            ∀ s : GlobalRestartState,
              s.defect = d ->
                s.repair.measure = m ->
                  ∃ t : GlobalRestartState,
                    GlobalRestartReachable s t ∧
                      Terminal t := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ihRepair =>
          intro s hsdefect' hsmeasure
          rcases hclassify s with
            hterminal | ⟨u, hprogress⟩
          · exact
              ⟨s, GlobalRestartReachable.refl s,
                hterminal⟩
          · rcases hprogress with
              hdefectDrop | ⟨hsameDefect, hrepair⟩
            · have hudefect :
                  u.defect < d := by
                rw [← hsdefect']
                exact hdefectDrop
              rcases
                  ihDefect u.defect hudefect u rfl with
                ⟨t, hut, hterminal⟩
              exact
                ⟨t,
                  GlobalRestartReachable.step
                    (Or.inl hdefectDrop) hut,
                  hterminal⟩
            · have hudefect :
                  u.defect = d := by
                calc
                  u.defect = s.defect := hsameDefect
                  _ = d := hsdefect'
              have humeasure :
                  u.repair.measure < m := by
                rw [← hsmeasure]
                exact
                  repairState_measure_lt_of_progress
                    hrepair
              rcases
                  ihRepair u.repair.measure humeasure
                    u hudefect rfl with
                ⟨t, hut, hterminal⟩
              exact
                ⟨t,
                  GlobalRestartReachable.step
                    (Or.inr ⟨hsameDefect, hrepair⟩)
                    hut,
                  hterminal⟩
      exact
        hinner s.repair.measure s hsdefect rfl
  exact
    houter s.defect s rfl

/-- Special case: if determinant defect is already zero, every nonterminal
step of a total classifier must be a same-defect local repair, so the global
theorem reduces to the previously certified finite repair mechanism. -/
theorem zeroDefect_globalRestart_reaches_terminal
    (Terminal : GlobalRestartState -> Prop)
    (hclassify : IsTotalGlobalRestartClassifier Terminal)
    (s : GlobalRestartState)
    (_hzero : s.defect = 0) :
    ∃ t : GlobalRestartState,
      GlobalRestartReachable s t ∧
        Terminal t := by
  exact
    globalRestartClassifier_reaches_terminal
      Terminal hclassify s

end

end HC4.Newton
