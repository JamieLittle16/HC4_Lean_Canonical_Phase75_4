import HC4.Valuation.SeparatedRightWallScaleDescent
import HC4.Newton.RestartClassification
import Mathlib.Tactic

/-!
# Final geometric restart assembly

The separated-right-wall scale theorem closes the last geometric Smith
branch at the level of the actual determinant defect.  This file performs
the corresponding well-founded assembly on the full polynomial-family
state.

There are three layers.

1. A strict geometric restart is converted into a new
   `CanonicalGeometricRestartState`, retaining the family, the moving
   section, homogeneity, exact collision and the canonical marked point.

2. Repeated geometric restarts are iterated by strong induction on the
   determinant defect.  Every canonical state therefore reaches a
   canonical Smith local frontier after finitely many strict defect drops.

3. Exact collision on a canonical family is connected directly to the
   already-certified terminal endpoint theorem.  Thus a certified terminal
   special fibre contradicts JC2 immediately.

The file also records the exact two external interfaces still required for
a proposition-level `JC2 => HC4` statement:

* construction of a canonical exact-collision entry from the chosen
  formulation of an HC4 counterexample;
* exhaustion of the canonical Smith local frontier into the already
  certified terminal endpoint families.

The current project tree does not define a proposition named `HC4`, so this
module deliberately supplies a generic final assembly theorem instead of
inventing a top-level statement.

The important point is that there is no longer any open geometric restart
or scale branch inside this assembly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Exact family entry
------------------------------------------------------------------------ -/

/-- Data required to enter the now-closed geometric restart machine.

This is deliberately independent of any particular formulation of an HC4
counterexample.  A later global theorem only has to construct this object
from its preferred counterexample predicate. -/
structure CanonicalExactCollisionEntry
    (D : ℕ) where
  defect : ℕ
  family : MvPolynomial (Fin 4) (Polynomial K)
  movingSection : Fin 4 → Polynomial K
  homogeneous :
    family.IsHomogeneous D
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) family defect
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family
      (zeroPolynomialSection (K := K))
      movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- An exact-collision entry becomes a full geometric restart state after
choosing the finite local-repair bookkeeping state. -/
def CanonicalExactCollisionEntry.toRestartState
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    CanonicalGeometricRestartState (K := K) D :=
  { defect := e.defect
    repair := repair
    family := e.family
    movingSection := e.movingSection
    homogeneous := e.homogeneous
    hessianDefect := e.hessianDefect
    exactCollision := e.exactCollision
    sectionSpecial := e.sectionSpecial }

@[simp] theorem CanonicalExactCollisionEntry.toRestartState_defect
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    (e.toRestartState repair).defect = e.defect := rfl

@[simp] theorem CanonicalExactCollisionEntry.toRestartState_family
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    (e.toRestartState repair).family = e.family := rfl

@[simp] theorem CanonicalExactCollisionEntry.toRestartState_movingSection
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    (e.toRestartState repair).movingSection =
      e.movingSection := rfl

/-! -----------------------------------------------------------------------
  Full-state geometric reachability
------------------------------------------------------------------------ -/

/-- Reachability through the existing lexicographic global progress
relation, while retaining a full canonical polynomial-family state at every
vertex. -/
inductive CanonicalGeometricReachable
    (D : ℕ) :
    CanonicalGeometricRestartState (K := K) D →
      CanonicalGeometricRestartState (K := K) D →
      Prop
  | refl
      (s : CanonicalGeometricRestartState (K := K) D) :
      CanonicalGeometricReachable D s s
  | step
      {s t u : CanonicalGeometricRestartState (K := K) D}
      (hst : GlobalRestartProgress s.toGlobal t.toGlobal)
      (htu : CanonicalGeometricReachable D t u) :
      CanonicalGeometricReachable D s u

/-- Full-state reachability is transitive. -/
theorem canonicalGeometricReachable_trans
    {D : ℕ}
    {a b c : CanonicalGeometricRestartState (K := K) D}
    (hab : CanonicalGeometricReachable (K := K) D a b)
    (hbc : CanonicalGeometricReachable (K := K) D b c) :
    CanonicalGeometricReachable (K := K) D a c := by
  induction hab with
  | refl _ =>
      exact hbc
  | step hst htu ih =>
      exact CanonicalGeometricReachable.step hst (ih hbc)

/-- Forgetting family geometry sends canonical reachability to the already
green numerical global-restart reachability relation. -/
theorem canonicalGeometricReachable_toGlobal
    {D : ℕ}
    {s t : CanonicalGeometricRestartState (K := K) D}
    (hreach :
      CanonicalGeometricReachable (K := K) D s t) :
    GlobalRestartReachable s.toGlobal t.toGlobal := by
  induction hreach with
  | refl s =>
      exact GlobalRestartReachable.refl s.toGlobal
  | step hst htu ih =>
      exact GlobalRestartReachable.step hst ih

/-! -----------------------------------------------------------------------
  Strict geometric restart -> full canonical state
------------------------------------------------------------------------ -/

/-- Every strict geometric restart certificate from Phase 93.74 really
contains a successor `CanonicalGeometricRestartState`.

The local repair bookkeeping is kept unchanged because a strict defect
drop is already global restart progress independently of that component. -/
theorem canonicalState_of_strictGeometricDefectRestart
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D)
    (hrestart :
      HasCanonicalStrictGeometricDefectRestart
        (K := K) D s.defect) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      t.defect < s.defect ∧
      GlobalRestartProgress s.toGlobal t.toGlobal := by
  rcases hrestart with
    ⟨Delta', hDelta, P', b',
      hhom, hdef, hcoll, hb⟩
  let t : CanonicalGeometricRestartState (K := K) D :=
    { defect := Delta'
      repair := s.repair
      family := P'
      movingSection := b'
      homogeneous := hhom
      hessianDefect := hdef
      exactCollision := hcoll
      sectionSpecial := hb }
  refine ⟨t, ?_, ?_⟩
  · exact hDelta
  · exact
      globalRestartProgress_of_defect_lt
        (s := s.toGlobal)
        (t := t.toGlobal)
        hDelta

/-- Phase 93.74 is therefore a genuine one-step classifier on the full
canonical state: either the local Smith frontier has been reached, or a
strictly lower-defect canonical state exists. -/
theorem canonicalGeometricState_closedStep
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity ∨
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        t.defect < s.defect ∧
        GlobalRestartProgress s.toGlobal t.toGlobal := by
  rcases
      alignedSmith_zeroSection_closedGeometricStep
        s.family
        s.homogeneous
        s.movingSection
        s.hessianDefect
        hD
        s.exactCollision
        s.sectionSpecial
        complexity with
    hlocal | hrestart
  · exact Or.inl hlocal
  · exact
      Or.inr
        (canonicalState_of_strictGeometricDefectRestart
          s hrestart)

/-! -----------------------------------------------------------------------
  Well-founded geometric exhaustion
------------------------------------------------------------------------ -/

/-- Auxiliary strong-induction theorem at a fixed numerical defect.

Every state of defect exactly `n` reaches a state satisfying the canonical
Smith local-frontier predicate. -/
theorem canonicalGeometricRestart_reachesSmithFrontier_aux
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (n : ℕ) :
    ∀ s : CanonicalGeometricRestartState (K := K) D,
      s.defect = n →
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        CanonicalGeometricReachable (K := K) D s t ∧
        HasCanonicalSmithRepairOrTerminal
          (K := K) D complexity := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hs
      rcases
          canonicalGeometricState_closedStep
            (K := K) hD complexity s with
        hlocal | hnext
      · exact
          ⟨s,
            CanonicalGeometricReachable.refl s,
            hlocal⟩
      · rcases hnext with ⟨u, huDefect, huProgress⟩
        have huN : u.defect < n := by
          omega
        rcases
            ih u.defect huN u rfl with
          ⟨t, hut, hlocal⟩
        exact
          ⟨t,
            CanonicalGeometricReachable.step
              huProgress hut,
            hlocal⟩

/-- **Global geometric restart termination.**

Starting from any canonical exact-collision family of degree at least two,
the now-closed geometric restart machine reaches the canonical Smith local
frontier after finitely many strict determinant-defect drops.

This theorem has no geometric continuation hypothesis. -/
theorem canonicalGeometricRestart_reachesSmithFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable (K := K) D s t ∧
      HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesSmithFrontier_aux
      (K := K) hD complexity s.defect s rfl

/-- Entry-facing version of the global geometric exhaustion theorem. -/
theorem canonicalExactCollisionEntry_reachesSmithFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable
        (K := K) D (e.toRestartState repair) t ∧
      HasCanonicalSmithRepairOrTerminal
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesSmithFrontier
      (K := K) hD complexity (e.toRestartState repair)

/-! -----------------------------------------------------------------------
  Special-fibre terminal contradiction
------------------------------------------------------------------------ -/

/-- A canonical geometric state always induces the canonical distinct exact
collision `0 ~ e0` on its special fibre. -/
theorem canonicalGeometricState_specialFiber_exactCollision
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber s.family)
      (fun _ => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have hcoll :=
    polynomialFamilyExactGradientCollision_specialFiber
      s.family
      (zeroPolynomialSection (K := K))
      s.movingSection
      s.exactCollision
  simpa [s.sectionSpecial] using hcoll

/-- The two canonical special-fibre collision points are distinct. -/
theorem canonicalSpecialFiberPoints_ne :
    (fun _ => (0 : K)) ≠
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact
    Ne.symm
      (coordinateAxisPoint_zero_ne_zeroPoint
        (K := K))

/-- **Terminal collision bridge.**

If the special fibre of a canonical geometric state is one of the already
certified terminal endpoint families, JC2 immediately contradicts the
preserved exact collision. -/
theorem canonicalGeometricState_terminalEndpoint_impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {D : ℕ}
    (s : CanonicalGeometricRestartState (K := K) D)
    (hterminal :
      CertifiedTerminalEndpoint
        (polynomialFamilySpecialFiber s.family)) :
    False := by
  exact
    certifiedTerminalEndpoint_collision_impossible_of_JC2
      hJC2
      hterminal
      (canonicalSpecialFiberPoints_ne (K := K))
      (canonicalGeometricState_specialFiber_exactCollision
        (K := K) s)

/-- Entry-facing terminal contradiction. -/
theorem canonicalExactCollisionEntry_terminalEndpoint_impossible_of_JC2
    [CharZero K]
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {D : ℕ}
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState)
    (hterminal :
      CertifiedTerminalEndpoint
        (polynomialFamilySpecialFiber
          (e.toRestartState repair).family)) :
    False := by
  exact
    canonicalGeometricState_terminalEndpoint_impossible_of_JC2
      (K := K)
      hJC2
      (e.toRestartState repair)
      hterminal

/-! -----------------------------------------------------------------------
  Exact final assembly interfaces
------------------------------------------------------------------------ -/

/-- Generic entry interface from a proposition expressing the existence of
a counterexample.

The project can instantiate `Counterexample` with its eventual concrete
HC4-counterexample predicate without changing any restart theorem. -/
def HasCanonicalExactCollisionEntryFrom
    (Counterexample : Prop) : Prop :=
  Counterexample →
    ∃ D : ℕ,
      ∃ e : CanonicalExactCollisionEntry (K := K) D,
        2 ≤ D

/-- The remaining local theorem, stated without hiding the boundary.

It says that under JC2 the exact local Smith frontier reached by the global
geometric induction is impossible.  This is the precise place where the
rigid rank-one / first-departure / rank-two endpoint continuation must be
connected to `CertifiedTerminalEndpoint`.

No global geometric statement is bundled into this interface. -/
def CanonicalSmithFrontierExhaustionUnderJC2 : Prop :=
  ∀ hJC2 : HC4.PlanarJC2Injectivity K,
    ∀ D : ℕ,
      2 ≤ D →
      ∀ s : CanonicalGeometricRestartState (K := K) D,
        HasCanonicalSmithRepairOrTerminal
            (K := K) D 0 →
          False

/-- **Generic final implication assembly.**

Once a chosen counterexample predicate supplies the canonical exact
collision entry and the local Smith frontier is exhausted under JC2, no
such counterexample exists.

Everything between those two interfaces is now an unconditional Lean
theorem: exact-family state construction, all Smith wall geometry, strict
unramified scale descent, well-founded defect termination, and terminal
exact-collision contradiction. -/
theorem noCounterexample_of_JC2_canonicalEntry_and_frontierExhaustion
    [CharZero K]
    (Counterexample : Prop)
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hentry :
      HasCanonicalExactCollisionEntryFrom
        (K := K) Counterexample)
    (hexhaust :
      CanonicalSmithFrontierExhaustionUnderJC2
        (K := K)) :
    ¬ Counterexample := by
  intro hcounter
  rcases hentry hcounter with
    ⟨D, e, hD⟩
  rcases
      canonicalExactCollisionEntry_reachesSmithFrontier
        (K := K)
        hD
        0
        e
        (rankOneRepairState 0) with
    ⟨t, _hreach, hfrontier⟩
  exact
    hexhaust hJC2 D hD t hfrontier

/-- Convenience package for a complete reduction of a chosen
counterexample predicate to JC2. -/
def HasCompleteCanonicalReductionToJC2
    (Counterexample : Prop) : Prop :=
  HasCanonicalExactCollisionEntryFrom
      (K := K) Counterexample ∧
    CanonicalSmithFrontierExhaustionUnderJC2
      (K := K)

/-- Packaged form of the generic final implication theorem. -/
theorem noCounterexample_of_JC2_completeCanonicalReduction
    [CharZero K]
    (Counterexample : Prop)
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hcomplete :
      HasCompleteCanonicalReductionToJC2
        (K := K) Counterexample) :
    ¬ Counterexample := by
  exact
    noCounterexample_of_JC2_canonicalEntry_and_frontierExhaustion
      (K := K)
      Counterexample
      hJC2
      hcomplete.1
      hcomplete.2

end

end HC4.Valuation
