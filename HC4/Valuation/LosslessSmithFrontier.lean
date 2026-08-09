import HC4.Valuation.FinalRestartAssembly
import Mathlib.Tactic

/-!
# Lossless canonical Smith frontier

The first global restart assembly intentionally used the compact predicate

`HasCanonicalSmithRepairOrTerminal`.

That predicate is sufficient for numerical bookkeeping, but it forgets the
family and the actual rank-two Smith escalation certificate.  Those data are
exactly what the remaining first-departure theorem must consume.

This file keeps the green global geometry unchanged and adds a stronger,
lossless local frontier.

A lossless frontier retains:

* the actual polynomial family over the parameter ring;
* the two marked sections and their canonical special points;
* homogeneous special fibre and its exact marked collision;
* the symmetric-minimal Smith condition;
* the canonical balanced Smith subface and packet polynomial;
* nonempty realised packet support and nonvanishing;
* the exact rigid-rank-one or rank-two-escalation outcome.

The existing strong symmetric-minimal theorem already proves all packet
fields.  The only work here is to preserve them through the three local
branches of the zero-slope geometric dispatcher.

The resulting well-founded theorem is

`canonicalGeometricRestart_reachesLosslessSmithFrontier`.

Thus the remaining local theorem no longer receives a numerical repair
state with its geometry erased.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Lossless local frontier
------------------------------------------------------------------------ -/

/-- The complete local Smith data retained at the end of the geometric
defect descent. -/
structure CanonicalSmithLosslessFrontier
    (D complexity : ℕ) where
  family : MvPolynomial (Fin 4) (Polynomial K)
  leftSection : Fin 4 → Polynomial K
  rightSection : Fin 4 → Polynomial K
  specialHomogeneous :
    (polynomialFamilySpecialFiber family).IsHomogeneous D
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family leftSection rightSection
  leftSpecial :
    polynomialSectionSpecialPoint leftSection =
      (fun _ => (0 : K))
  rightSpecial :
    polynomialSectionSpecialPoint rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  symmetricMinimal :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber family))
      0
      (fun _ => (0 : ℤ))
  subfaceNonempty :
    (canonicalSpecialFiberSmithSubface
      (polynomialFamilySpecialFiber family)).Nonempty
  persistentPacket :
    HasRankOnePersistentPacketSupport
      (0 : Fin 4) 1 2 D
      (canonicalSpecialFiberSmithPolynomial
        (polynomialFamilySpecialFiber family))
  packet_ne_zero :
    canonicalSpecialFiberSmithPolynomial
        (polynomialFamilySpecialFiber family) ≠ 0
  canonicalOutcome :
    HasSmithCanonicalRepairOutcome
      (0 : Fin 4) 1 2 D
      (canonicalSpecialFiberSmithPolynomial
        (polynomialFamilySpecialFiber family))
      complexity

/-- Proposition asserting existence of the full retained Smith-frontier data.

The rich frontier remains a structure in `Type`; theorem statements use
this proposition so logical connectives and existential elimination stay
inside `Prop`. -/
def HasCanonicalSmithLosslessFrontier
    (D complexity : ℕ) : Prop :=
  Nonempty
    (CanonicalSmithLosslessFrontier
      (K := K) D complexity)

/-- The exact canonical Smith packet retained by a lossless frontier. -/
noncomputable def CanonicalSmithLosslessFrontier.packet
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    MvPolynomial (Fin 4) K :=
  canonicalSpecialFiberSmithPolynomial
    (polynomialFamilySpecialFiber f.family)

/-- A lossless frontier really strengthens the former compact local
package. -/
theorem CanonicalSmithLosslessFrontier.toRepairOrTerminal
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity := by
  refine
    ⟨canonicalSpecialFiberSmithPolynomial
        (polynomialFamilySpecialFiber f.family), ?_⟩
  rcases f.canonicalOutcome with hrigid | hrepair
  · exact Or.inl hrigid
  · exact
      Or.inr
        ⟨rankTwoRepairState complexity,
          hrepair.2.1⟩

/-- The symmetric-minimal special-fibre theorem already contains every
field required by the lossless frontier. -/
theorem canonicalSymmetricMinimal_losslessFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D : ℕ}
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity := by
  have hprojected :
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P)).Nonempty := by
    rcases hminimal with ⟨e, he, _hle⟩
    exact ⟨e, he⟩
  have hspecial :=
    polynomialFamilyCollision_specialFiber_zero_axisZero
      P a b hcoll ha hb
  have hmin :=
    canonicalSpecialFiberSmith_minimum
      (polynomialFamilySpecialFiber P)
  have hattain :=
    canonicalSpecialFiberSmith_attainment
      (polynomialFamilySpecialFiber P)
      hprojected
  have hout :=
    homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair
      (K := K)
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      hhom hD hspecial
      0
      (fun _ => (0 : ℤ))
      hminimal hmin hattain
      complexity
  refine
    ⟨{ family := P
       leftSection := a
       rightSection := b
       specialHomogeneous := hhom
       exactCollision := hcoll
       leftSpecial := ha
       rightSpecial := hb
       symmetricMinimal := hminimal
       subfaceNonempty := ?_
       persistentPacket := ?_
       packet_ne_zero := ?_
       canonicalOutcome := ?_ }⟩
  · simpa [canonicalSpecialFiberSmithSubface] using hout.1
  · simpa [canonicalSpecialFiberSmithSubface,
      canonicalSpecialFiberSmithPolynomial] using hout.2.1
  · simpa [canonicalSpecialFiberSmithSubface,
      canonicalSpecialFiberSmithPolynomial] using hout.2.2.1
  · simpa [canonicalSpecialFiberSmithSubface,
      canonicalSpecialFiberSmithPolynomial] using hout.2.2.2

/-! -----------------------------------------------------------------------
  The three local Smith branches retain the full frontier
------------------------------------------------------------------------ -/

/-- Primitive zero-Smith source: the current family itself is the
lossless symmetric-minimal frontier. -/
theorem primitiveZeroSmithSource_losslessFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hprimitive : HasPrimitiveZeroSmithSource P)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity := by
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  have hhom :=
    polynomialFamilySpecialFiber_isHomogeneous
      P hP
  have hminimal :=
    primitiveZeroSmithSource_specialFiber_symmetricMinimal
      P hprimitive
  exact
    canonicalSymmetricMinimal_losslessFrontier
      P
      (zeroPolynomialSection (K := K))
      b hhom hD hcoll
      ha hb hminimal complexity

/-- Pure coefficient wall: retain the actual first-wall family and its two
integrally transformed marked sections. -/
theorem pureCoefficientWall_losslessFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hcoeff :
      alignedSmithGenuineFirstWall P a b hwall ∈
        alignedSmithCoefficientWalls P)
    (hnotA :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls a)
    (hnotB :
      alignedSmithGenuineFirstWall P a b hwall ∉
        alignedSmithSectionWalls b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity := by
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P a b hwall
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P a b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P a b hwall
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D := by
    dsimp [Q]
    exact
      genuineFirstWall_specialFiber_isHomogeneous
        P hP a b hwall
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q a' b' := by
    dsimp [Q, a', b']
    exact
      alignedSmithGenuineFirstWall_preservesExactCollision
        P a b hwall hcoll
  have hpoints :=
    pureCoefficientWall_specialPoints_canonical
      P a b hwall hnotA hnotB ha hb
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber Q))
        0
        (fun _ => (0 : ℤ)) := by
    dsimp [Q]
    exact
      genuineCoefficientWall_specialFiber_symmetricMinimal
        P a b hwall hcoeff
  exact
    canonicalSymmetricMinimal_losslessFrontier
      Q a' b' hhom hD hQcoll
      (by simpa [a'] using hpoints.1)
      (by simpa [b'] using hpoints.2)
      hminimal complexity

/-- No genuine wall: retain the actual primitive transformed family and
the transformed exact-collision sections. -/
theorem noWallPrimitiveSmithFamily_losslessFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity := by
  rcases
      noWallPrimitiveSmithFamily_canonicalCollision
        P a b Delta hdef hnone
        hcoll ha hb with
    ⟨a', b', hcoll', ha', hb'⟩
  have hhomFull :=
    noWallPrimitiveSmithFamily_isHomogeneous
      P hP a b Delta hdef hnone
  have hhom :=
    polynomialFamilySpecialFiber_isHomogeneous
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone)
      hhomFull
  have hminimal :=
    noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
      P a b Delta hdef hnone
  exact
    canonicalSymmetricMinimal_losslessFrontier
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone)
      a' b' hhom hD hcoll'
      ha' hb' hminimal complexity

/-! -----------------------------------------------------------------------
  Lossless geometric dispatcher
------------------------------------------------------------------------ -/

/-- The zero-section geometric dispatcher with no loss of local Smith
geometry.

The only nonlocal branch is the already-closed separated right section
wall. -/
theorem alignedSmith_zeroSection_geometricDispatcher_lossless
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
        (K := K) D complexity ∨
      HasSeparatedRightSmithSectionWall P b := by
  classical
  have ha :
      polynomialSectionSpecialPoint
          (zeroPolynomialSection (K := K)) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_zeroPolynomialSection
  by_cases hprimitive :
      HasPrimitiveZeroSmithSource P
  · exact
      Or.inl
        (primitiveZeroSmithSource_losslessFrontier
          P hP b hprimitive hD hcoll hb complexity)
  · by_cases hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b
    · let N :=
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall
      by_cases hcoeff :
          N ∈ alignedSmithCoefficientWalls P
      · by_cases hB :
          N ∈ alignedSmithSectionWalls b
        · have hcoupled :
            HasCoupledAlignedSmithWall
              P (zeroPolynomialSection (K := K)) b := by
            refine ⟨hwall, ?_, ?_⟩
            · simpa [N] using hcoeff
            · exact Or.inr (by simpa [N] using hB)
          exact
            False.elim
              (coupledAlignedSmithWall_impossible_of_noPrimitive
                P hP
                (zeroPolynomialSection (K := K))
                b hD hcoll
                ha hb hprimitive hcoupled)
        · have hnotA :
              N ∉ alignedSmithSectionWalls
                (zeroPolynomialSection (K := K)) :=
            not_mem_alignedSmithSectionWalls_zeroPolynomialSection
              (K := K) N
          exact
            Or.inl
              (pureCoefficientWall_losslessFrontier
                P hP
                (zeroPolynomialSection (K := K))
                b hwall
                (by simpa [N] using hcoeff)
                (by simpa [N] using hnotA)
                (by simpa [N] using hB)
                hD hcoll ha hb complexity)
      · have hcases :=
          alignedSmithGenuineFirstWall_cases
            P (zeroPolynomialSection (K := K)) b hwall
        have hB :
            N ∈ alignedSmithSectionWalls b := by
          rcases hcases with hc | hA | hB
          · exact
              False.elim
                (hcoeff (by simpa [N] using hc))
          · have hnotA :
                N ∉ alignedSmithSectionWalls
                  (zeroPolynomialSection (K := K)) :=
              not_mem_alignedSmithSectionWalls_zeroPolynomialSection
                (K := K) N
            exact
              False.elim
                (hnotA (by simpa [N] using hA))
          · simpa [N] using hB
        exact
          Or.inr
            ⟨hwall, hprimitive,
              by simpa [N] using hcoeff,
              by simpa [N] using hB⟩
    · exact
        Or.inl
          (noWallPrimitiveSmithFamily_losslessFrontier
            P hP
            (zeroPolynomialSection (K := K))
            b Delta hdef hwall
            hD hcoll ha hb complexity)

/-- Combine the lossless local dispatcher with the green separated-wall
scale theorem.

There are now exactly two outcomes: full local Smith geometry, or a
strictly smaller unramified determinant defect. -/
theorem alignedSmith_zeroSection_closedGeometricStep_lossless
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hD : 2 ≤ D)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (complexity : ℕ) :
    HasCanonicalSmithLosslessFrontier
        (K := K) D complexity ∨
      HasCanonicalStrictGeometricDefectRestart
        (K := K) D Delta := by
  rcases
      alignedSmith_zeroSection_geometricDispatcher_lossless
        P hP b hdef hD hcoll hb complexity with
    hlocal | hwall
  · exact Or.inl hlocal
  · exact
      Or.inr
        (separatedRightSmithWall_strictCanonicalGeometricRestart
          P hP b hwall hdef hcoll hb)

/-! -----------------------------------------------------------------------
  Full-state well-founded exhaustion to the lossless frontier
------------------------------------------------------------------------ -/

/-- One full canonical state either reaches the lossless Smith frontier or
has a genuine lower-defect canonical successor. -/
theorem canonicalGeometricState_closedStep_lossless
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    HasCanonicalSmithLosslessFrontier
        (K := K) D complexity ∨
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        t.defect < s.defect ∧
        GlobalRestartProgress s.toGlobal t.toGlobal := by
  rcases
      alignedSmith_zeroSection_closedGeometricStep_lossless
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

/-- Strong-induction auxiliary theorem for lossless local exhaustion. -/
theorem canonicalGeometricRestart_reachesLosslessSmithFrontier_aux
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (n : ℕ) :
    ∀ s : CanonicalGeometricRestartState (K := K) D,
      s.defect = n →
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        CanonicalGeometricReachable (K := K) D s t ∧
        HasCanonicalSmithLosslessFrontier
          (K := K) D complexity := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hs
      rcases
          canonicalGeometricState_closedStep_lossless
            (K := K) hD complexity s with
        hlocal | hnext
      · exact
          ⟨s,
            CanonicalGeometricReachable.refl s,
            hlocal⟩
      · rcases hnext with
          ⟨u, huDefect, huProgress⟩
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

/-- **Lossless global geometric exhaustion.**

Every canonical exact-collision state reaches a local Smith frontier which
retains the family, transformed marked sections, canonical Smith packet and
the actual rank-two escalation certificate when that branch occurs. -/
theorem canonicalGeometricRestart_reachesLosslessSmithFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable (K := K) D s t ∧
      HasCanonicalSmithLosslessFrontier
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesLosslessSmithFrontier_aux
      (K := K) hD complexity s.defect s rfl

/-- Entry-facing lossless exhaustion theorem. -/
theorem canonicalExactCollisionEntry_reachesLosslessSmithFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (e : CanonicalExactCollisionEntry (K := K) D)
    (repair : RepairState) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable
        (K := K) D (e.toRestartState repair) t ∧
      HasCanonicalSmithLosslessFrontier
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesLosslessSmithFrontier
      (K := K) hD complexity (e.toRestartState repair)

/-! -----------------------------------------------------------------------
  Sharpened final local interface
------------------------------------------------------------------------ -/

/-- The only local theorem still required by the generic JC2 assembly,
now stated on the full retained Smith geometry. -/
def CanonicalLosslessSmithFrontierExhaustionUnderJC2 : Prop :=
  ∀ hJC2 : HC4.PlanarJC2Injectivity K,
    ∀ D : ℕ,
      2 ≤ D →
      ∀ f : CanonicalSmithLosslessFrontier
          (K := K) D 0,
        False

/-- A complete reduction using the lossless frontier. -/
def HasCompleteLosslessCanonicalReductionToJC2
    (Counterexample : Prop) : Prop :=
  HasCanonicalExactCollisionEntryFrom
      (K := K) Counterexample ∧
    CanonicalLosslessSmithFrontierExhaustionUnderJC2
      (K := K)

/-- Generic final implication using the lossless Smith frontier.

All global geometric continuation has been discharged before the local
exhaustion hypothesis is used. -/
theorem noCounterexample_of_JC2_losslessCanonicalReduction
    [CharZero K]
    (Counterexample : Prop)
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hcomplete :
      HasCompleteLosslessCanonicalReductionToJC2
        (K := K) Counterexample) :
    ¬ Counterexample := by
  intro hcounter
  rcases hcomplete.1 hcounter with
    ⟨D, e, hD⟩
  rcases
      canonicalExactCollisionEntry_reachesLosslessSmithFrontier
        (K := K)
        hD
        0
        e
        (rankOneRepairState 0) with
    ⟨_t, _hreach, hfrontier⟩
  rcases hfrontier with ⟨f⟩
  exact
    hcomplete.2 hJC2 D hD f

/-- The proposition-level lossless frontier forgets to the former compact
local frontier. -/
theorem hasLosslessFrontier_supplies_compactFrontier
    {D complexity : ℕ}
    (h :
      HasCanonicalSmithLosslessFrontier
        (K := K) D complexity) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity := by
  rcases h with ⟨f⟩
  exact f.toRepairOrTerminal

/-- Every lossless complete reduction also supplies the former compact
frontier only at the final local point.

This theorem is useful for compatibility with existing downstream code. -/
theorem losslessFrontier_supplies_compactFrontier
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier
      (K := K) D complexity) :
    HasCanonicalSmithRepairOrTerminal
      (K := K) D complexity :=
  f.toRepairOrTerminal

end

end HC4.Valuation
