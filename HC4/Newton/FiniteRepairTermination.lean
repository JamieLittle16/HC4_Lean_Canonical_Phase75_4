import HC4.Newton.RankOnePacketReentry
import Mathlib.Tactic

/-!
# Finite repair termination measure

Phases 88--92 classify the local corank-entry branches.  The next global
task is to rule out an endless sequence of nonterminal repairs.

This file isolates the purely finite combinatorics of that argument.

A repair state remembers

* the active transverse rank, constrained to `1,2,3`;
* a natural-valued Rees/Newton complexity.

A genuine repair counts as progress when either

1. the complexity strictly decreases; or
2. the complexity stays fixed and the active rank strictly increases.

The numerical measure

    3 * complexity + (3 - rank)

strictly decreases under either form of progress.  The factor `3` is chosen
because the rank defect lies in `{0,1,2}`.

Lean then proves that no infinite sequence of progressing repair states can
exist.  This is the well-founded engine needed by the corank trichotomy.

The geometric work still remaining is to prove that every actual
nonterminal Rees repair satisfies `RepairProgress`.
-/

namespace HC4.Newton

noncomputable section

/-- Finite state used by the repair/termination argument. -/
structure RepairState where
  rank : ℕ
  complexity : ℕ
  rank_pos : 1 ≤ rank
  rank_le_three : rank ≤ 3

/-- Defect of the active transverse rank from the maximal relevant rank
three. -/
def RepairState.rankDefect
    (s : RepairState) : ℕ :=
  3 - s.rank

/-- Numerical termination measure. -/
def RepairState.measure
    (s : RepairState) : ℕ :=
  3 * s.complexity + s.rankDefect

/-- A repair makes genuine progress if it lowers complexity, or preserves
complexity while strictly raising active transverse rank. -/
def RepairProgress
    (s t : RepairState) : Prop :=
  t.complexity < s.complexity ∨
    (t.complexity = s.complexity ∧ s.rank < t.rank)

/-- The rank defect is always at most two. -/
theorem RepairState.rankDefect_le_two
    (s : RepairState) :
    s.rankDefect ≤ 2 := by
  have hrankPos : 1 ≤ s.rank := s.rank_pos
  have hrankLe : s.rank ≤ 3 := s.rank_le_three
  unfold RepairState.rankDefect
  omega

/-- Strict rank growth at fixed complexity strictly lowers rank defect. -/
theorem RepairState.rankDefect_lt_of_rank_lt
    {s t : RepairState}
    (hrank : s.rank < t.rank) :
    t.rankDefect < s.rankDefect := by
  have hsRankPos : 1 ≤ s.rank := s.rank_pos
  have hsRankLe : s.rank ≤ 3 := s.rank_le_three
  have htRankPos : 1 ≤ t.rank := t.rank_pos
  have htRankLe : t.rank ≤ 3 := t.rank_le_three
  unfold RepairState.rankDefect
  omega

/-- **Every progressing repair strictly lowers the finite measure.** -/
theorem repairState_measure_lt_of_progress
    {s t : RepairState}
    (hprogress : RepairProgress s t) :
    t.measure < s.measure := by
  rcases hprogress with hcomplex | ⟨hcomplex, hrank⟩
  · have htdef : t.rankDefect ≤ 2 :=
      t.rankDefect_le_two
    have hsdef : 0 ≤ s.rankDefect := Nat.zero_le _
    unfold RepairState.measure
    omega
  · have hdef :
        t.rankDefect < s.rankDefect :=
      RepairState.rankDefect_lt_of_rank_lt hrank
    unfold RepairState.measure
    rw [hcomplex]
    omega

/-- Progress is irreflexive. -/
theorem not_repairProgress_self
    (s : RepairState) :
    ¬ RepairProgress s s := by
  intro h
  have hlt := repairState_measure_lt_of_progress h
  exact (Nat.lt_irrefl s.measure) hlt

/-- A sequence is a strict repair chain if every successive state makes
`RepairProgress`. -/
def IsStrictRepairChain
    (states : ℕ → RepairState) : Prop :=
  ∀ n, RepairProgress (states n) (states (n + 1))

/-- Along a strict repair chain, the initial measure dominates the current
measure plus the number of repair steps already taken. -/
theorem strictRepairChain_measure_bound
    (states : ℕ → RepairState)
    (hchain : IsStrictRepairChain states) :
    ∀ n,
      (states n).measure + n ≤ (states 0).measure := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep :
          (states (n + 1)).measure <
            (states n).measure :=
        repairState_measure_lt_of_progress (hchain n)
      omega

/-- **Finite repair termination.**
There is no infinite sequence in which every repair makes genuine progress. -/
theorem no_infinite_strictRepairChain
    (states : ℕ → RepairState) :
    ¬ IsStrictRepairChain states := by
  intro hchain
  have hbound :=
    strictRepairChain_measure_bound states hchain
      ((states 0).measure + 1)
  omega

/-- Quantitative version: a strict repair chain cannot make more steps than
the initial measure. -/
theorem strictRepairChain_step_bound
    (states : ℕ → RepairState)
    (hchain : IsStrictRepairChain states)
    (n : ℕ) :
    n ≤ (states 0).measure := by
  have hbound :=
    strictRepairChain_measure_bound states hchain n
  omega


/-! ## Exact numerical characterisation of repair progress -/

/-- The numerical measure is not merely decreasing along `RepairProgress`:
with ranks constrained to `1,2,3`, strict measure decrease is *equivalent*
to repair progress.

This equivalence is useful for global restart assembly because it means the
abstract repair relation carries no extra combinatorial content beyond the
single natural-valued measure. -/
theorem repairProgress_of_measure_lt
    {s t : RepairState}
    (hmeasure : t.measure < s.measure) :
    RepairProgress s t := by
  unfold RepairProgress
  by_cases hcomplex : t.complexity < s.complexity
  · exact Or.inl hcomplex
  · right
    have hs_le_t :
        s.complexity ≤ t.complexity :=
      Nat.le_of_not_gt hcomplex
    have hsdef :
        s.rankDefect ≤ 2 :=
      s.rankDefect_le_two
    have htdef_nonneg :
        0 ≤ t.rankDefect :=
      Nat.zero_le _
    have ht_le_s :
        t.complexity ≤ s.complexity := by
      unfold RepairState.measure at hmeasure
      omega
    have hcomplex_eq :
        t.complexity = s.complexity :=
      Nat.le_antisymm ht_le_s hs_le_t
    refine ⟨hcomplex_eq, ?_⟩
    have hdef :
        t.rankDefect < s.rankDefect := by
      unfold RepairState.measure at hmeasure
      rw [hcomplex_eq] at hmeasure
      omega
    have hspos := s.rank_pos
    have hsle := s.rank_le_three
    have htpos := t.rank_pos
    have htle := t.rank_le_three
    unfold RepairState.rankDefect at hdef
    omega

/-- `RepairProgress` is exactly strict descent of `RepairState.measure`. -/
theorem repairProgress_iff_measure_lt
    {s t : RepairState} :
    RepairProgress s t ↔ t.measure < s.measure := by
  constructor
  · exact repairState_measure_lt_of_progress
  · exact repairProgress_of_measure_lt

/-- Repair progress is transitive.  This follows immediately from the exact
measure characterisation and is convenient when several local restart
moves are packaged into one global step. -/
theorem repairProgress_trans
    {s t u : RepairState}
    (hst : RepairProgress s t)
    (htu : RepairProgress t u) :
    RepairProgress s u := by
  apply repairProgress_of_measure_lt
  exact
    lt_trans
      (repairState_measure_lt_of_progress htu)
      (repairState_measure_lt_of_progress hst)



/-! ## Well-founded repair classification

The numerical termination theorem above rules out infinite strict chains.
For restart assembly it is more convenient to package the constructive
well-founded consequence directly: if every nonterminal state admits a
`RepairProgress` successor, then some terminal state is reached after
finitely many repairs.

This is still purely finite combinatorics.  The geometric restart theorem
only has to provide the one-step classifier.
-/

/-- Reflexive-transitive reachability by genuine repair steps. -/
inductive RepairReachable : RepairState -> RepairState -> Prop
  | refl (s : RepairState) :
      RepairReachable s s
  | step {s t u : RepairState}
      (hst : RepairProgress s t)
      (htu : RepairReachable t u) :
      RepairReachable s u

/-- Reachability is transitive. -/
theorem RepairReachable.trans
    {s t u : RepairState}
    (hst : RepairReachable s t)
    (htu : RepairReachable t u) :
    RepairReachable s u := by
  induction hst generalizing u with
  | refl =>
      exact htu
  | step hxy hyz ih =>
      exact RepairReachable.step hxy (ih htu)

/-- Every nontrivial reachable endpoint has no larger repair measure than
its source. -/
theorem RepairReachable.measure_le
    {s t : RepairState}
    (hst : RepairReachable s t) :
    t.measure ≤ s.measure := by
  induction hst with
  | refl =>
      exact le_rfl
  | step hxy hyz ih =>
      have hlt :
          _ < _ :=
        repairState_measure_lt_of_progress hxy
      omega

/-- One-step interface expected from a local geometric restart
classification. -/
def HasRepairOrTerminal
    (Terminal : Prop)
    (s : RepairState) : Prop :=
  Terminal ∨ ∃ t : RepairState, RepairProgress s t

/-- A total local classifier either declares the current state terminal or
produces a genuine repair successor. -/
def IsTotalRepairClassifier
    (Terminal : RepairState -> Prop) : Prop :=
  ∀ s : RepairState,
    HasRepairOrTerminal (Terminal s) s

/-- **Well-founded finite restart classification.**

Once a total one-step classifier has been supplied, iteration cannot remain
forever in the repair branch: some terminal state is reachable.

The proof is strong induction on the already-certified natural-valued
`RepairState.measure`. -/
theorem repairClassifier_reaches_terminal
    (Terminal : RepairState -> Prop)
    (hclassify : IsTotalRepairClassifier Terminal)
    (s : RepairState) :
    ∃ t : RepairState,
      RepairReachable s t ∧ Terminal t := by
  have haux :
      ∀ n : ℕ,
        ∀ s : RepairState,
          s.measure = n ->
            ∃ t : RepairState,
              RepairReachable s t ∧ Terminal t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hmeasure
      rcases hclassify s with hterminal | ⟨t, hprogress⟩
      · exact
          ⟨s, RepairReachable.refl s, hterminal⟩
      · have hlt :
            t.measure < n := by
          rw [← hmeasure]
          exact
            repairState_measure_lt_of_progress hprogress
        rcases
            ih t.measure hlt t rfl with
          ⟨u, htu, hu⟩
        exact
          ⟨u, RepairReachable.step hprogress htu, hu⟩
  exact
    haux s.measure s rfl

/-- The terminal state supplied by the classifier has measure bounded by the
initial state. -/
theorem repairClassifier_terminal_measure_le
    (Terminal : RepairState -> Prop)
    (hclassify : IsTotalRepairClassifier Terminal)
    (s : RepairState) :
    ∃ t : RepairState,
      Terminal t ∧ t.measure ≤ s.measure := by
  rcases
      repairClassifier_reaches_terminal
        Terminal hclassify s with
    ⟨t, hreach, hterminal⟩
  exact
    ⟨t, hterminal, RepairReachable.measure_le hreach⟩


end

end HC4.Newton
