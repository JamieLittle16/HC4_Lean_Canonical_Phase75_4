import HC4.Valuation.LosslessSmithFrontier
import HC4.Valuation.AlignedSmithFirstStop
import HC4.Valuation.SmithFamilyHomogeneity
import Mathlib.Tactic

/-!
# Defect-retaining Smith departure frontier

The lossless Smith frontier from Phase 93.76 keeps the full local Smith
packet, but it intentionally did not record the exact Hessian determinant
defect of the transformed parameter family.

That number is required by the first-departure argument: it is the finite
clock against which a later Rees/parameter layer is judged preterminal or
determinant-closing.

This file retains that exact defect together with the full source homogeneity of
the actual polynomial family.  The latter is already present in the global
restart state and is needed to close the quadratic boundary without weakening
the collision to the special fibre.

It also extracts, from the finite family support, the least strictly
positive parameter order.  Thus a departure-ready frontier comes with:

* the complete lossless Smith geometry;
* an exact equality `det Hess = X^Delta`;
* a finite least positive family coefficient order whenever one exists.

The resulting selector is not yet identified with the first non-one-sided
Schur departure.  That identification is the remaining local geometric
theorem.  The important advance here is that its input now contains the
actual family and the exact determinant-closing clock, rather than a
numerical placeholder.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Rich frontier with exact determinant defect
------------------------------------------------------------------------ -/

/-- Lossless local Smith data together with the exact determinant defect of
its actual parameter family. -/
structure CanonicalSmithDepartureFrontier
    (D complexity : ℕ) where
  defect : ℕ
  lossless : CanonicalSmithLosslessFrontier (K := K) D complexity
  /-- Full source homogeneity of the retained polynomial family. -/
  homogeneous : lossless.family.IsHomogeneous D
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) lossless.family defect

/-- Proposition-level wrapper for the departure-ready frontier. -/
def HasCanonicalSmithDepartureFrontier
    (D complexity : ℕ) : Prop :=
  Nonempty
    (CanonicalSmithDepartureFrontier
      (K := K) D complexity)

@[simp] theorem CanonicalSmithDepartureFrontier_family
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) :
    f.lossless.family = f.lossless.family := rfl

/-- Forgetting the exact defect recovers the green Phase-93.76 frontier. -/
theorem CanonicalSmithDepartureFrontier.toLossless
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity :=
  ⟨f.lossless⟩

/-- Proposition-level forgetful map. -/
theorem hasDepartureFrontier_to_lossless
    {D complexity : ℕ}
    (h :
      HasCanonicalSmithDepartureFrontier
        (K := K) D complexity) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity := by
  rcases h with ⟨f⟩
  exact f.toLossless

/-! -----------------------------------------------------------------------
  Generic symmetric-minimal constructor with exact defect
------------------------------------------------------------------------ -/

/-- Build the full departure frontier directly from a symmetric-minimal
canonical exact-collision family whose Hessian defect is known exactly. -/
theorem canonicalSymmetricMinimal_departureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    {D Delta : ℕ}
    (hfull : P.IsHomogeneous D)
    (hhom :
      (polynomialFamilySpecialFiber P).IsHomogeneous D)
    (hD : 2 ≤ D)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
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
    HasCanonicalSmithDepartureFrontier
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
  let lossless :
      CanonicalSmithLosslessFrontier
        (K := K) D complexity :=
    { family := P
      leftSection := a
      rightSection := b
      specialHomogeneous := hhom
      exactCollision := hcoll
      leftSpecial := ha
      rightSpecial := hb
      symmetricMinimal := hminimal
      subfaceNonempty := by
        simpa [canonicalSpecialFiberSmithSubface] using hout.1
      persistentPacket := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.1
      packet_ne_zero := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.2.1
      canonicalOutcome := by
        simpa [canonicalSpecialFiberSmithSubface,
          canonicalSpecialFiberSmithPolynomial] using hout.2.2.2 }
  exact
    ⟨{ defect := Delta
       lossless := lossless
       homogeneous := by
         simpa [lossless] using hfull
       hessianDefect := by
         simpa [lossless] using hdef }⟩

/-! -----------------------------------------------------------------------
  Exact-defect versions of the three local branches
------------------------------------------------------------------------ -/

/-- Primitive zero-Smith source: no family transformation occurs, so the
frontier defect is exactly the incoming defect. -/
theorem primitiveZeroSmithSource_departureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
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
    HasCanonicalSmithDepartureFrontier
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
    canonicalSymmetricMinimal_departureFrontier
      P
      (zeroPolynomialSection (K := K))
      b hP hhom hD hdef hcoll
      ha hb hminimal complexity

/-- Pure coefficient first wall: the actual retained family is the
once-ramified first-wall family, whose exact defect is `20*Delta`. -/
theorem pureCoefficientWall_departureFrontier
    [CharZero K]
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (a b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
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
    HasCanonicalSmithDepartureFrontier
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
  have hQhom : Q.IsHomogeneous D := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWallFamily_isHomogeneous
        P hP a b hwall
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D := by
    dsimp [Q]
    exact
      genuineFirstWall_specialFiber_isHomogeneous
        P hP a b hwall
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q
        (alignedSmithRamificationIndex * Delta) := by
    dsimp [Q]
    exact
      alignedSmithGenuineFirstWall_preservesHessianDefect
        P a b hwall Delta hdef
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
    canonicalSymmetricMinimal_departureFrontier
      Q a' b' hQhom hhom hD hQdef hQcoll
      (by simpa [a'] using hpoints.1)
      (by simpa [b'] using hpoints.2)
      hminimal complexity

/-- No genuine wall: retain the exact defect proved for the primitive
one-shot normalised family. -/
theorem noWallPrimitiveSmithFamily_departureFrontier
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
    HasCanonicalSmithDepartureFrontier
      (K := K) D complexity := by
  rcases
      noWallPrimitiveSmithFamily_canonicalCollision
        P a b Delta hdef hnone
        hcoll ha hb with
    ⟨a', b', hcoll', ha', hb'⟩
  let Q :=
    noWallPrimitiveSmithFamily
      P a b Delta hdef hnone
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P a b Delta hdef hnone
  let m :=
    minimalZeroSmithParameterOrder P hne
  let Delta' :=
    alignedSmithRamificationIndex * Delta -
      4 * (alignedSmithRamificationIndex * m)
  have hhomFull :
      Q.IsHomogeneous D := by
    dsimp [Q]
    exact
      noWallPrimitiveSmithFamily_isHomogeneous
        P hP a b Delta hdef hnone
  have hhom :
      (polynomialFamilySpecialFiber Q).IsHomogeneous D :=
    polynomialFamilySpecialFiber_isHomogeneous
      Q hhomFull
  have hQdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Q Delta' := by
    dsimp [Q, Delta', hne, m]
    exact
      noWallPrimitiveSmithFamily_hasHessianDefect
        P a b Delta hdef hnone
  have hminimal :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber Q))
        0
        (fun _ => (0 : ℤ)) := by
    dsimp [Q]
    exact
      noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
        P a b Delta hdef hnone
  exact
    canonicalSymmetricMinimal_departureFrontier
      Q a' b' hhomFull hhom hD hQdef hcoll'
      ha' hb' hminimal complexity

/-! -----------------------------------------------------------------------
  Departure-ready dispatcher
------------------------------------------------------------------------ -/

/-- Lossless zero-section dispatcher retaining the exact determinant defect
of whichever local family is produced. -/
theorem alignedSmith_zeroSection_geometricDispatcher_departure
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
    HasCanonicalSmithDepartureFrontier
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
        (primitiveZeroSmithSource_departureFrontier
          P hP b hdef hprimitive hD hcoll hb complexity)
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
              (pureCoefficientWall_departureFrontier
                P hP
                (zeroPolynomialSection (K := K))
                b hdef hwall
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
          (noWallPrimitiveSmithFamily_departureFrontier
            P hP
            (zeroPolynomialSection (K := K))
            b Delta hdef hwall
            hD hcoll ha hb complexity)

/-- Closed geometric step at the departure-ready frontier. -/
theorem alignedSmith_zeroSection_closedGeometricStep_departure
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
    HasCanonicalSmithDepartureFrontier
        (K := K) D complexity ∨
      HasCanonicalStrictGeometricDefectRestart
        (K := K) D Delta := by
  rcases
      alignedSmith_zeroSection_geometricDispatcher_departure
        P hP b hdef hD hcoll hb complexity with
    hlocal | hwall
  · exact Or.inl hlocal
  · exact
      Or.inr
        (separatedRightSmithWall_strictCanonicalGeometricRestart
          P hP b hwall hdef hcoll hb)

/-! -----------------------------------------------------------------------
  Global defect induction to the departure-ready frontier
------------------------------------------------------------------------ -/

/-- One canonical state either reaches a departure-ready local frontier or
has a genuine lower-defect canonical successor. -/
theorem canonicalGeometricState_closedStep_departure
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    HasCanonicalSmithDepartureFrontier
        (K := K) D complexity ∨
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        t.defect < s.defect ∧
        GlobalRestartProgress s.toGlobal t.toGlobal := by
  rcases
      alignedSmith_zeroSection_closedGeometricStep_departure
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

/-- Strong-induction auxiliary theorem for departure-ready exhaustion. -/
theorem canonicalGeometricRestart_reachesDepartureFrontier_aux
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (n : ℕ) :
    ∀ s : CanonicalGeometricRestartState (K := K) D,
      s.defect = n →
      ∃ t : CanonicalGeometricRestartState (K := K) D,
        CanonicalGeometricReachable (K := K) D s t ∧
        HasCanonicalSmithDepartureFrontier
          (K := K) D complexity := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hs
      rcases
          canonicalGeometricState_closedStep_departure
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

/-- Every canonical exact-collision state reaches a lossless local Smith
frontier carrying its exact determinant defect. -/
theorem canonicalGeometricRestart_reachesDepartureFrontier
    [CharZero K]
    {D : ℕ}
    (hD : 2 ≤ D)
    (complexity : ℕ)
    (s : CanonicalGeometricRestartState (K := K) D) :
    ∃ t : CanonicalGeometricRestartState (K := K) D,
      CanonicalGeometricReachable (K := K) D s t ∧
      HasCanonicalSmithDepartureFrontier
        (K := K) D complexity := by
  exact
    canonicalGeometricRestart_reachesDepartureFrontier_aux
      (K := K) hD complexity s.defect s rfl

/-! -----------------------------------------------------------------------
  Finite first positive parameter layer
------------------------------------------------------------------------ -/

/-- Finite set of strictly positive exact parameter orders appearing among
the coefficients of a polynomial family. -/
noncomputable def familyPositiveParameterOrders
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset ℕ := by
  classical
  exact
    (P.support.image
      (fun d => smithFamilyCoefficientOrder P d)).filter
        (fun n => 0 < n)

/-- There is at least one genuinely later parameter layer. -/
def HasPositiveParameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  (familyPositiveParameterOrders P).Nonempty

/-- Least positive parameter order in a finite polynomial family. -/
noncomputable def firstPositiveParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveParameterLayer P) : ℕ :=
  (familyPositiveParameterOrders P).min' h

theorem firstPositiveParameterOrder_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveParameterLayer P) :
    firstPositiveParameterOrder P h ∈
      familyPositiveParameterOrders P := by
  unfold firstPositiveParameterOrder
  exact
    Finset.min'_mem
      (familyPositiveParameterOrders P) h

theorem firstPositiveParameterOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveParameterLayer P) :
    0 < firstPositiveParameterOrder P h := by
  have hmem :=
    firstPositiveParameterOrder_mem P h
  rw [familyPositiveParameterOrders] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- The least positive order is realised by an actual source coefficient. -/
theorem firstPositiveParameterOrder_realised
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveParameterLayer P) :
    ∃ d ∈ P.support,
      smithFamilyCoefficientOrder P d =
        firstPositiveParameterOrder P h := by
  classical
  have hmem :=
    firstPositiveParameterOrder_mem P h
  rw [familyPositiveParameterOrders] at hmem
  have himage :
      firstPositiveParameterOrder P h ∈
        P.support.image
          (fun d => smithFamilyCoefficientOrder P d) :=
    (Finset.mem_filter.mp hmem).1
  rcases Finset.mem_image.mp himage with
    ⟨d, hd, heq⟩
  exact ⟨d, hd, heq⟩

/-- Every other strictly positive family coefficient order is at least the
selected first order. -/
theorem firstPositiveParameterOrder_le
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveParameterLayer P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (hpos : 0 < smithFamilyCoefficientOrder P d) :
    firstPositiveParameterOrder P h ≤
      smithFamilyCoefficientOrder P d := by
  apply Finset.min'_le
  rw [familyPositiveParameterOrders]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨d, hd, rfl⟩, hpos⟩

/-- Exact finite dichotomy for the parameter-family clock. -/
theorem noPositiveParameterLayer_or_first
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (¬ HasPositiveParameterLayer P) ∨
      ∃ h : HasPositiveParameterLayer P,
        0 < firstPositiveParameterOrder P h ∧
        (∃ d ∈ P.support,
          smithFamilyCoefficientOrder P d =
            firstPositiveParameterOrder P h) := by
  classical
  by_cases h : HasPositiveParameterLayer P
  · right
    exact
      ⟨h,
        firstPositiveParameterOrder_pos P h,
        firstPositiveParameterOrder_realised P h⟩
  · exact Or.inl h

/-! -----------------------------------------------------------------------
  Preterminal-versus-closing clock
------------------------------------------------------------------------ -/

/-- Once a departure-ready frontier has a positive later parameter layer,
its first such layer is canonically either below the exact Hessian closing
order or at/after it. -/
theorem CanonicalSmithDepartureFrontier.firstLayer_preterminal_or_closing
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity)
    (h :
      HasPositiveParameterLayer f.lossless.family) :
    firstPositiveParameterOrder f.lossless.family h < f.defect ∨
      f.defect ≤
        firstPositiveParameterOrder f.lossless.family h := by
  exact lt_or_ge _ _

/-- Fully explicit finite-clock trichotomy.

This is the formal boundary needed by the next local theorem:
there is no later parameter layer, or the first one is preterminal, or the
first one has reached determinant closure. -/
theorem CanonicalSmithDepartureFrontier.parameterClock_trichotomy
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) :
    (¬ HasPositiveParameterLayer f.lossless.family) ∨
      (∃ h : HasPositiveParameterLayer f.lossless.family,
        firstPositiveParameterOrder f.lossless.family h < f.defect) ∨
      (∃ h : HasPositiveParameterLayer f.lossless.family,
        f.defect ≤
          firstPositiveParameterOrder f.lossless.family h) := by
  classical
  by_cases h :
      HasPositiveParameterLayer f.lossless.family
  · rcases
      f.firstLayer_preterminal_or_closing h with
      hpre | hclose
    · exact Or.inr (Or.inl ⟨h, hpre⟩)
    · exact Or.inr (Or.inr ⟨h, hclose⟩)
  · exact Or.inl h

/-! -----------------------------------------------------------------------
  Sharpened final local interface
------------------------------------------------------------------------ -/

/-- The remaining local exhaustion theorem, now stated on a frontier with
an exact determinant clock.

Unlike the Phase-93.76 interface, an implementation of this predicate does
not have to rediscover the transformed family's Hessian defect. -/
def CanonicalDepartureFrontierExhaustionUnderJC2 : Prop :=
  ∀ hJC2 : HC4.PlanarJC2Injectivity K,
    ∀ D : ℕ,
      2 ≤ D →
      ∀ f : CanonicalSmithDepartureFrontier
          (K := K) D 0,
        False

/-- The departure-ready frontier still forgets to every earlier local
interface. -/
theorem departureFrontier_supplies_losslessFrontier
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) :
    HasCanonicalSmithLosslessFrontier
      (K := K) D complexity :=
  f.toLossless

end

end HC4.Valuation
