import HC4.Newton.GlobalRestartClassification
import Mathlib.Tactic

/-!
# Degree-adaptive global restart descent

The unrestricted restart argument has three lexicographic coordinates:

1. determinant defect;
2. the maximum still-visible nonlinear source degree;
3. the existing finite Smith/Rees repair state.

A drop in an earlier coordinate may reset every later coordinate.  This file
contains only the numerical well-founded engine; it deliberately makes no
claim about how the geometric degree-drop branch is constructed.
-/

namespace HC4.Newton

noncomputable section

/-- Numerical state for the degree-adaptive restart induction. -/
structure AdaptiveRestartState where
  defect : ℕ
  degreeCap : ℕ
  repair : RepairState

/-- Lexicographic progress in determinant defect, nonlinear degree cap, and
finally the existing local repair relation. -/
def AdaptiveRestartProgress
    (s t : AdaptiveRestartState) : Prop :=
  t.defect < s.defect ∨
    (t.defect = s.defect ∧ t.degreeCap < s.degreeCap) ∨
      (t.defect = s.defect ∧ t.degreeCap = s.degreeCap ∧
        RepairProgress s.repair t.repair)

theorem adaptiveRestartProgress_of_defect_lt
    {s t : AdaptiveRestartState}
    (h : t.defect < s.defect) :
    AdaptiveRestartProgress s t :=
  Or.inl h

theorem adaptiveRestartProgress_of_degree_lt
    {s t : AdaptiveRestartState}
    (hdefect : t.defect = s.defect)
    (hdegree : t.degreeCap < s.degreeCap) :
    AdaptiveRestartProgress s t :=
  Or.inr (Or.inl ⟨hdefect, hdegree⟩)

theorem adaptiveRestartProgress_of_repair
    {s t : AdaptiveRestartState}
    (hdefect : t.defect = s.defect)
    (hdegree : t.degreeCap = s.degreeCap)
    (hrepair : RepairProgress s.repair t.repair) :
    AdaptiveRestartProgress s t :=
  Or.inr (Or.inr ⟨hdefect, hdegree, hrepair⟩)

/-- Adaptive progress is irreflexive. -/
theorem not_adaptiveRestartProgress_self
    (s : AdaptiveRestartState) :
    ¬ AdaptiveRestartProgress s s := by
  intro h
  rcases h with hdefect | ⟨_hsame, hdegree⟩ | ⟨_hsame, _hdegree, hrepair⟩
  · exact (Nat.lt_irrefl s.defect) hdefect
  · exact (Nat.lt_irrefl s.degreeCap) hdegree
  · exact (not_repairProgress_self s.repair) hrepair

/-- Reflexive-transitive reachability by adaptive restart steps. -/
inductive AdaptiveRestartReachable :
    AdaptiveRestartState → AdaptiveRestartState → Prop
  | refl (s : AdaptiveRestartState) :
      AdaptiveRestartReachable s s
  | step {s t u : AdaptiveRestartState}
      (hst : AdaptiveRestartProgress s t)
      (htu : AdaptiveRestartReachable t u) :
      AdaptiveRestartReachable s u

theorem AdaptiveRestartReachable.trans
    {s t u : AdaptiveRestartState}
    (hst : AdaptiveRestartReachable s t)
    (htu : AdaptiveRestartReachable t u) :
    AdaptiveRestartReachable s u := by
  induction hst generalizing u with
  | refl => exact htu
  | step hxy _hyz ih =>
      exact AdaptiveRestartReachable.step hxy (ih htu)

def HasAdaptiveRestartOrTerminal
    (Terminal : Prop)
    (s : AdaptiveRestartState) : Prop :=
  Terminal ∨ ∃ t, AdaptiveRestartProgress s t

def IsTotalAdaptiveRestartClassifier
    (Terminal : AdaptiveRestartState → Prop) : Prop :=
  ∀ s, HasAdaptiveRestartOrTerminal (Terminal s) s

/-- **Three-level adaptive restart termination.**

Any total classifier reaches a terminal state.  The proof uses nested strong
induction, allowing a defect drop to reset degree and repair, and allowing a
degree drop to reset repair. -/
theorem adaptiveRestartClassifier_reaches_terminal
    (Terminal : AdaptiveRestartState → Prop)
    (hclassify : IsTotalAdaptiveRestartClassifier Terminal)
    (s : AdaptiveRestartState) :
    ∃ t, AdaptiveRestartReachable s t ∧ Terminal t := by
  have hdefect :
      ∀ defect : ℕ,
        ∀ s : AdaptiveRestartState,
          s.defect = defect →
            ∃ t, AdaptiveRestartReachable s t ∧ Terminal t := by
    intro defect
    induction defect using Nat.strong_induction_on with
    | h defect ihDefect =>
      intro s hsDefect
      have hdegree :
          ∀ degree : ℕ,
            ∀ s : AdaptiveRestartState,
              s.defect = defect →
              s.degreeCap = degree →
                ∃ t, AdaptiveRestartReachable s t ∧ Terminal t := by
        intro degree
        induction degree using Nat.strong_induction_on with
        | h degree ihDegree =>
          intro s hsDefect' hsDegree
          have hrepair :
              ∀ measure : ℕ,
                ∀ s : AdaptiveRestartState,
                  s.defect = defect →
                  s.degreeCap = degree →
                  s.repair.measure = measure →
                    ∃ t, AdaptiveRestartReachable s t ∧ Terminal t := by
            intro measure
            induction measure using Nat.strong_induction_on with
            | h measure ihRepair =>
              intro s hsDefect'' hsDegree' hsMeasure
              rcases hclassify s with hterminal | ⟨u, hprogress⟩
              · exact ⟨s, AdaptiveRestartReachable.refl s, hterminal⟩
              · rcases hprogress with
                  hDefectDrop | ⟨hSameDefect, hDegreeDrop⟩ |
                    ⟨hSameDefect, hSameDegree, hRepair⟩
                · have huDefect : u.defect < defect := by
                    rw [← hsDefect'']
                    exact hDefectDrop
                  rcases ihDefect u.defect huDefect u rfl with
                    ⟨t, hut, ht⟩
                  exact ⟨t, AdaptiveRestartReachable.step
                    (Or.inl hDefectDrop) hut, ht⟩
                · have huDefect : u.defect = defect :=
                    hSameDefect.trans hsDefect''
                  have huDegree : u.degreeCap < degree := by
                    rw [← hsDegree']
                    exact hDegreeDrop
                  rcases ihDegree u.degreeCap huDegree u huDefect rfl with
                    ⟨t, hut, ht⟩
                  exact ⟨t, AdaptiveRestartReachable.step
                    (Or.inr (Or.inl ⟨hSameDefect, hDegreeDrop⟩)) hut, ht⟩
                · have huDefect : u.defect = defect :=
                    hSameDefect.trans hsDefect''
                  have huDegree : u.degreeCap = degree :=
                    hSameDegree.trans hsDegree'
                  have huMeasure : u.repair.measure < measure := by
                    rw [← hsMeasure]
                    exact repairState_measure_lt_of_progress hRepair
                  rcases ihRepair u.repair.measure huMeasure u
                      huDefect huDegree rfl with ⟨t, hut, ht⟩
                  exact ⟨t, AdaptiveRestartReachable.step
                    (Or.inr (Or.inr
                      ⟨hSameDefect, hSameDegree, hRepair⟩)) hut, ht⟩
          exact hrepair s.repair.measure s hsDefect' hsDegree rfl
      exact hdegree s.degreeCap s hsDefect rfl
  exact hdefect s.defect s rfl

end

end HC4.Newton
