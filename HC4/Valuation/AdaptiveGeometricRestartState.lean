import HC4.Valuation.ZeroGradientNormalization
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# Geometry retained by the degree-adaptive Smith wall

The homogeneous polynomial extracted from a mixed Smith wall is a local
classifier input, not a replacement for the parameter family carrying the
determinant clock.  This file records those two levels without asserting a
geometric successor that has not yet been constructed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Global pointed geometry retained while a local mixed-degree Smith wall
is classified.  No homogeneity assumption is made on the family or its
special fibre.  `sourceComplexity` is intentionally abstract: integration
must decide whether it is residual degree, endpoint multiplicity, or a
finite Newton refinement. -/
structure AdaptiveGeometricRestartState where
  defect : ℕ
  degreeCap : ℕ
  sourceComplexity : ℕ
  repair : RepairState
  family : MvPolynomial (Fin 4) (Polynomial K)
  movingSection : Fin 4 → Polynomial K
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K) family defect
  nonlinearDegreeBound :
    NonlinearDegreeBound degreeCap family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (fun _ => (0 : Polynomial K)) movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Change only the finite local repair coordinate, retaining the complete
determinant-clock family and pointed collision geometry definitionally. -/
def AdaptiveGeometricRestartState.withRepair
    (s : AdaptiveGeometricRestartState (K := K))
    (repair : RepairState) : AdaptiveGeometricRestartState (K := K) where
  defect := s.defect
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := repair
  family := s.family
  movingSection := s.movingSection
  hessianDefect := s.hessianDefect
  nonlinearDegreeBound := s.nonlinearDegreeBound
  exactCollision := s.exactCollision
  sectionSpecial := s.sectionSpecial

@[simp] theorem AdaptiveGeometricRestartState.withRepair_family
    (s : AdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepair repair).family = s.family := rfl

@[simp] theorem AdaptiveGeometricRestartState.withRepair_defect
    (s : AdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepair repair).defect = s.defect := rfl

@[simp] theorem AdaptiveGeometricRestartState.withRepair_movingSection
    (s : AdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepair repair).movingSection = s.movingSection := rfl

/-- The zero-jet-normalized special fibre on which the adaptive wall
classifier operates. -/
noncomputable def AdaptiveGeometricRestartState.normalizedSpecialFiber
    (s : AdaptiveGeometricRestartState (K := K)) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber (zeroJetNormalizedFamily s.family)

/-- Normalization preserves the exact determinant clock of the retained
global family. -/
theorem AdaptiveGeometricRestartState.normalized_hessianDefect
    (s : AdaptiveGeometricRestartState (K := K)) :
    HasPolynomialFamilyHessianDefect
      (K := K) (zeroJetNormalizedFamily s.family) s.defect :=
  polynomialFamilyHessianDefect_zeroJetNormalizedFamily
    s.family s.defect s.hessianDefect

/-- Normalization also preserves the global nonlinear source-degree cap. -/
theorem AdaptiveGeometricRestartState.normalized_nonlinearDegreeBound
    (s : AdaptiveGeometricRestartState (K := K)) :
    NonlinearDegreeBound s.degreeCap
      (zeroJetNormalizedFamily s.family) :=
  nonlinearDegreeBound_zeroJetNormalizedFamily
    s.family s.degreeCap s.nonlinearDegreeBound

/-- The retained pointed geometry supplies exactly the collision, zero
gradient, and zero value hypotheses of the mixed-degree wall theorem. -/
theorem AdaptiveGeometricRestartState.normalizedSpecialFiber_axisData
    (s : AdaptiveGeometricRestartState (K := K)) :
    HasExactGradientCollision s.normalizedSpecialFiber
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) ∧
      (∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i s.normalizedSpecialFiber) = 0) ∧
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        s.normalizedSpecialFiber = 0 := by
  simpa [AdaptiveGeometricRestartState.normalizedSpecialFiber] using
    zeroJetNormalizedSpecialFiber_axisData
      s.family s.movingSection s.exactCollision s.sectionSpecial

/-- Honest local outcome over a retained global family.  The blocker branch
contains algebraic residual data but is not called a successor.  The packet
branch has entered the old fixed-degree classifier, while the original
family and determinant clock remain available through the index `s`. -/
inductive AdaptiveWallOutcome
    (s : AdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (complexity : ℕ) : Prop
  | blocker
      (e : SmithSupportExponent)
      (he : e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 s.normalizedSpecialFiber)
      (hlevel : base e = level)
      (hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e ∨
        IsWLinearSmithPattern e)
      (hresidual :
        MixedDegreeSmithExponentOutcome s.normalizedSpecialFiber e)
  | fixedDegree
      (D : ℕ)
      (Q : MvPolynomial (Fin 4) K)
      (hne : Q ≠ 0)
      (hD : 2 ≤ D)
      (hhom : Q.IsHomogeneous D)
      (hcollision :
        HasExactGradientCollision Q
          (fun _ : Fin 4 => (0 : K))
          (coordinateAxisPoint (K := K) (0 : Fin 4)))
      (hhessian : HC4.Polynomial.hessianDeterminant Q = 0)
      (hrepair :
        HasSmithCanonicalRepairOutcome
          (0 : Fin 4) 1 2 D Q complexity)

/-- Geometry-carrying rank-two continuation produced by the adaptive wall.
The retained family is deliberately unchanged: rank promotion is local
classifier progress, while `Q` and `escalation` record the packet that the
next Rees/Schur extraction must expose from that same family. -/
structure AdaptiveRankTwoContinuation
    (s : AdaptiveGeometricRestartState (K := K))
    (D complexity : ℕ)
    (Q : MvPolynomial (Fin 4) K) : Prop where
  packet_ne_zero : Q ≠ 0
  degree_ge_two : 2 ≤ D
  homogeneous : Q.IsHomogeneous D
  exactCollision :
    HasExactGradientCollision Q
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  hessian_zero : HC4.Polynomial.hessianDeterminant Q = 0
  escalation : HasRankTwoPacketEscalation (0 : Fin 4) 1 2 D Q
  repairProgress :
    RepairProgress s.repair (rankTwoRepairState complexity)

/-- Provenance-strengthened rank-two continuation.  It relates the packet
to an explicit quadratic Smith subface of the retained normalized special
fibre, preventing an unrelated homogeneous packet from being paired with
the correct global family. -/
structure AdaptiveRankTwoFamilyContinuation
    (s : AdaptiveGeometricRestartState (K := K))
    (D complexity : ℕ)
    (Q : MvPolynomial (Fin 4) K)
    extends AdaptiveRankTwoContinuation s D complexity Q where
  subface : Finset SmithSupportExponent
  integralWall : IntegralAdaptiveSurvivingSmithWall s.normalizedSpecialFiber
  subface_eq_balanced : subface =
    smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 s.normalizedSpecialFiber)
      integralWall.level integralWall.base
  quadratic :
    ∀ e ∈ subface,
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)
  packetProvenance :
    IsMinimalLongitudinalSmithPacket
      subface s.normalizedSpecialFiber D Q
  persistentPacket :
    HasRankOnePersistentPacketSupport (0 : Fin 4) 1 2 D Q

/-- The additional actual-family datum required by matrix packet isolation.
The exposure family carries its own exact determinant clock and has the
complete quadratic Smith subface—not merely `Q`—as special fibre. -/
structure AdaptiveRankTwoMatrixExposure
    (s : AdaptiveGeometricRestartState (K := K))
    (D complexity : ℕ)
    (Q : MvPolynomial (Fin 4) K)
    (c : AdaptiveRankTwoFamilyContinuation s D complexity Q) where
  family : MvPolynomial (Fin 4) (Polynomial K)
  defect : ℕ
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K) family defect
  specialFiber_eq :
    polynomialFamilySpecialFiber family =
      smithSubfacePolynomial (1 : Fin 4) 2 3
        c.subface s.normalizedSpecialFiber

/-- Upgrade a rank-two continuation once its explicit subface provenance is
available. -/
def AdaptiveRankTwoContinuation.withFamilyProvenance
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (h : AdaptiveRankTwoContinuation s D complexity Q)
    (wall : IntegralAdaptiveSurvivingSmithWall s.normalizedSpecialFiber)
    (T : Finset SmithSupportExponent)
    (hT : T = smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 s.normalizedSpecialFiber)
      wall.level wall.base)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hprov :
      IsMinimalLongitudinalSmithPacket
        T s.normalizedSpecialFiber D Q) :
    AdaptiveRankTwoFamilyContinuation s D complexity Q where
  toAdaptiveRankTwoContinuation := h
  subface := T
  integralWall := wall
  subface_eq_balanced := hT
  quadratic := hquad
  packetProvenance := hprov
  persistentPacket := by
    have hsupported : IsSupportedOnSmithSubface (1 : Fin 4) 2 3 T Q := by
      intro d hd
      rw [hprov.packet_eq, coeff_smithSubfaceDegreeComponent] at hd
      split at hd
      · exact (show
          smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
            HC4.Polynomial.ordinaryDegree4 d = D from ‹_›).1
      · exact (hd rfl).elim
    exact rankOnePersistentPacketSupport_of_smithQuadraticSubface
      (0 : Fin 4) 1 2 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by intro t; fin_cases t <;> simp)
      hprov.packet_homogeneous T hsupported hquad

/-- The successor represented by a rank-two continuation.  It preserves all
global geometry and changes only the local repair coordinate. -/
def AdaptiveRankTwoContinuation.successor
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (_h : AdaptiveRankTwoContinuation s D complexity Q) :
    AdaptiveGeometricRestartState (K := K) :=
  s.withRepair (rankTwoRepairState complexity)

/-- Split the fixed-degree canonical outcome without losing the retained
family.  The rigid branch remains static packet data; the rank-two branch is
upgraded from bare numerical progress to `AdaptiveRankTwoContinuation`. -/
theorem fixedDegreeRepair_rigid_or_rankTwoContinuation
    (s : AdaptiveGeometricRestartState (K := K))
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hne : Q ≠ 0)
    (hD : 2 ≤ D)
    (hhom : Q.IsHomogeneous D)
    (hcollision :
      HasExactGradientCollision Q
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)))
    (hhessian : HC4.Polynomial.hessianDeterminant Q = 0)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hout :
      HasSmithCanonicalRepairOutcome
        (0 : Fin 4) 1 2 D Q complexity) :
    HasRigidRankOnePacket (0 : Fin 4) 1 2 D Q ∨
      AdaptiveRankTwoContinuation s D complexity Q := by
  rcases hout with hrigid | ⟨hesc, hprogress, _hmeasure⟩
  · exact Or.inl hrigid
  · right
    refine
      { packet_ne_zero := hne
        degree_ge_two := hD
        homogeneous := hhom
        exactCollision := hcollision
        hessian_zero := hhessian
        escalation := hesc
        repairProgress := ?_ }
    simpa [hsrepair] using hprogress

/-- Global-family entry into the completed mixed-degree/fixed-degree local
classifier.  This theorem retains provenance but makes no unsupported claim
that either algebraic local outcome has already produced a new family. -/
theorem AdaptiveGeometricRestartState.classifyNormalizedSpecialWall
    [CharZero K]
    (s : AdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber)
        level base)
    (hmin :
      ∀ e ∈ smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        base e = level)
    (complexity : ℕ) :
    AdaptiveWallOutcome s base level complexity := by
  rcases s.normalizedSpecialFiber_axisData with
    ⟨hcoll, hzero, hvalue⟩
  rcases minimalSmithLevel_blockerOutcome_or_fixedDegreeRepair
      s.normalizedSpecialFiber base level
      hcoll hzero hvalue hpole hmin hattain complexity with
    ⟨e, he, hlevel, hpattern, hresidual⟩ |
      ⟨D, Q, hne, hD, hhom, hQcoll, hQhessian, hrepair⟩
  · exact AdaptiveWallOutcome.blocker
      e he hlevel hpattern hresidual
  · exact AdaptiveWallOutcome.fixedDegree
      D Q hne hD hhom hQcoll hQhessian hrepair

/-- Geometry-bearing entry to the adaptive wall split.  Unlike the abstract
classifier above, this theorem requires an integral realization of the
scalar wall and retains it in the surviving output, ready for the adaptive
Smith exposure construction. -/
theorem AdaptiveGeometricRestartState.classifyIntegralNormalizedSpecialWall
    [CharZero K]
    (s : AdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hreal :
      HasIntegralAdaptiveSmithWallWeight s.normalizedSpecialFiber base)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber)
        level base)
    (hmin :
      ∀ e ∈ smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport
          (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        base e = level) :
    (∃ e ∈ smithProjectedSupport
        (1 : Fin 4) 2 3 s.normalizedSpecialFiber,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome s.normalizedSpecialFiber e) ∨
      Nonempty
        (IntegralAdaptiveSurvivingSmithWall
          s.normalizedSpecialFiber) := by
  rcases s.normalizedSpecialFiber_axisData with ⟨hcoll, hzero, hvalue⟩
  exact adaptiveWall_blocker_or_integralSurvivingWall
    s.normalizedSpecialFiber base level hreal hmin hattain hpole
    hcoll hzero hvalue

end

end HC4.Valuation
