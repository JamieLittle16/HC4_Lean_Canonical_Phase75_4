import HC4.Valuation.CommonParameterFactorRestart
import HC4.Newton.RestartClassification
import Mathlib.Tactic

/-!
# Symmetric Smith minimality is enough

The canonical Smith refinement in the current restart proof uses only one
explicit separator:

    k = l = 1.

Its integral direction is

    theta = (2,2),

and its Phase 93.7 denominator is the fixed integer

    D = 10.

Therefore the local Smith classifier does not need the stronger predicate

    IsPoleMinimalAgainstSmithSeparators S m base

quantifying over every `(k,l)`.  It only needs failure of strict improvement
for the single symmetric separator.

This file introduces that exact weaker predicate and reconstructs the whole
canonical Smith repair conclusion from it.

Consequences:

* the pole-minimal branch needs only the fixed `(2,2)` direction;
* the complementary branch is a strict improvement for this same direction;
* denominator clearing for the entire canonical Smith branch can therefore
  be performed by one fixed ramification `tau -> s^10`;
* no changing ramification scale is needed during the global restart.

The actual exact-axis collision, first-wall grade classification, canonical
subface construction, rank-one packet, and finite repair mechanisms are all
reused from the already-green Smith files.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]
variable {σ : Type*} [DecidableEq σ]

/-! ## The one separator actually used by canonical Smith refinement -/

/-- Minimality only against the canonical symmetric Smith separator
`(k,l) = (1,1)`. -/
def IsSymmetricSmithPoleMinimal
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ) : Prop :=
  ∃ e ∈ S,
    smithIntegralSeparatorTilt 1 1 base e ≤
      smithRescaledOldMinimum 1 1 m

/-- The complementary condition: the symmetric separator strictly improves
every supported rescaled value. -/
def HasStrictSymmetricSmithImprovement
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ) : Prop :=
  ∀ e ∈ S,
    smithRescaledOldMinimum 1 1 m <
      smithIntegralSeparatorTilt 1 1 base e

/-- Exact dichotomy for the single canonical Smith separator. -/
theorem symmetricSmithPoleMinimal_or_strictImprovement
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ) :
    IsSymmetricSmithPoleMinimal S m base ∨
      HasStrictSymmetricSmithImprovement S m base := by
  classical
  by_cases hmin :
      IsSymmetricSmithPoleMinimal S m base
  · exact Or.inl hmin
  · right
    intro e heS
    by_contra hnotStrict
    apply hmin
    refine ⟨e, heS, ?_⟩
    omega

/-- Full pole-minimality implies the weaker symmetric condition. -/
theorem symmetricSmithPoleMinimal_of_poleMinimal
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsPoleMinimalAgainstSmithSeparators S m base) :
    IsSymmetricSmithPoleMinimal S m base := by
  exact hpole 1 1

/-! ## Fixed denominator facts -/

/-- The canonical symmetric separator is the integral direction `(2,2)`. -/
theorem smithExtremeSeparator_one_one :
    smithExtremeSeparator 1 1 =
      ((2 : ℤ), (2 : ℤ)) := by
  norm_num [smithExtremeSeparator]

/-- Its universal Smith bound is exactly `4`. -/
theorem smithExtremeSeparatorBound_one_one :
    smithExtremeSeparatorBound 1 1 = 4 := by
  norm_num [smithExtremeSeparatorBound]

/-- **The only ramification denominator needed by the canonical Smith
refinement is `10`.** -/
theorem smithSeparatorRamificationIndex_one_one :
    HC4.Valuation.smithSeparatorRamificationIndex 1 1 = 10 := by
  norm_num [HC4.Valuation.smithSeparatorRamificationIndex,
    finiteTiltDenominator,
    smithExtremeSeparatorBound]

/-! ## Symmetric minimality supplies the old-face witness -/

/-- Under symmetric minimality, some old-minimum exponent has nonpositive
symmetric Smith derivative.

This is the exact one-separator analogue of
`poleMinimal_exists_nonpositive_face_grade`. -/
theorem symmetricSmithPoleMinimal_exists_nonpositive_face_grade
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m) :
    ∃ e ∈ S,
      base e = m ∧
      smithSeparatorDelta 1 1 e ≤ 0 := by
  by_contra hnone
  have hpositive :
      ∀ e ∈ S,
        base e = m →
          (1 : ℤ) ≤ smithSeparatorDelta 1 1 e := by
    intro e heS hemin
    have hnotLe :
        ¬ smithSeparatorDelta 1 1 e ≤ 0 := by
      intro hle
      apply hnone
      exact ⟨e, heS, hemin, hle⟩
    omega
  have himprove :=
    smithFiniteSupportIntegralTilt_strictly_raises_minimum
      S 1 1 m base hmin hpositive
  rcases hpole with
    ⟨e, heS, hnotImprove⟩
  have hstrict := himprove e heS
  omega

/-- Symmetric minimality alone forces the canonical balanced subface to be
nonempty. -/
theorem symmetricSmithPoleMinimal_smithSymmetricBalancedSubface_nonempty
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base) :
    (smithSymmetricBalancedSubface S m base).Nonempty := by
  rcases
      symmetricSmithPoleMinimal_exists_nonpositive_face_grade
        S m base hpole hmin hattain with
    ⟨e, heS, hemin, hdeltaLe⟩
  have hdeltaNonneg :
      0 ≤ smithSeparatorDelta 1 1 e :=
    smithSeparatorDelta_one_one_nonnegative_of_generalShape
      e (hshape e heS hemin)
  have hdeltaZero :
      smithSeparatorDelta 1 1 e = 0 := by
    omega
  exact
    ⟨e,
      (mem_smithSymmetricBalancedSubface).2
        ⟨heS, hemin, hdeltaZero⟩⟩

/-- The full symmetric quadratic refinement needs only the one-separator
minimality predicate. -/
theorem symmetricSmithPoleMinimal_symmetricRefinement_quadratic
    (S : Finset SmithSupportExponent)
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal S m base)
    (hmin :
      ∀ e ∈ S, m ≤ base e)
    (hattain :
      ∃ e ∈ S, base e = m)
    (hshape :
      HasGeneralSurvivingSmithFaceShape S m base)
    (hnoW :
      ∀ e ∈ S,
        base e = m →
          ¬ IsWLinearSmithPattern e) :
    (smithSymmetricBalancedSubface S m base).Nonempty ∧
      ∀ e ∈ smithSymmetricBalancedSubface S m base,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
  constructor
  · exact
      symmetricSmithPoleMinimal_smithSymmetricBalancedSubface_nonempty
        S m base hpole hmin hattain hshape
  · intro e he
    have htarget :
        IsSymmetricSmithTargetGrade e.grade :=
      smithSymmetricBalancedSubface_targetGrade
        S m base hshape e he
    have heData :=
      (mem_smithSymmetricBalancedSubface).1 he
    exact
      symmetricTargetGrade_exponent_cases_of_noWLinear
        e htarget (hnoW e heData.1 heData.2.1)

/-! ## Exact-axis collision: same canonical packet under weak minimality -/

/-- **Canonical Smith repair from symmetric minimality alone.**

This is the one-separator replacement for
`homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_canonicalRepair`.

All downstream packet and repair conclusions are unchanged. -/
theorem homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    T.Nonempty ∧
      HasRankOnePersistentPacketSupport x y z D G ∧
      G ≠ 0 ∧
      HasSmithCanonicalRepairOutcome
        x y z D G complexity := by
  dsimp
  let S :=
    smithProjectedSupport y z w F
  let T :=
    smithSymmetricBalancedSubface S m base
  let G :=
    smithSubfacePolynomial y z w T F
  have hinputs :=
    homogeneous_exactAxisCollision_smithRefinementInputs
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base
  have hrefine :=
    symmetricSmithPoleMinimal_symmetricRefinement_quadratic
      S m base hpole hmin hattain
      hinputs.1 hinputs.2
  have hhomG :
      G.IsHomogeneous D := by
    dsimp [G, T]
    exact
      smithSubfacePolynomial_isHomogeneous
        y z w
        (smithSymmetricBalancedSubface S m base)
        hhom
  have hsuppG :
      IsSupportedOnSmithSubface
        y z w T G := by
    dsimp [G]
    exact
      smithSubfacePolynomial_supported
        y z w T F
  have hpacket :
      HasRankOnePersistentPacketSupport
        x y z D G :=
    rankOnePersistentPacketSupport_of_smithQuadraticSubface
      x y z w hxy hxz hxw hyz hyw hzw
      hchart hhomG T hsuppG hrefine.2
  have hreal :
      IsSmithSubfaceRealisedInPolynomial
        y z w T F := by
    dsimp [T, S]
    exact
      smithSymmetricBalancedSubface_realisedInPolynomial
        y z w F m base
  have hGne :
      G ≠ 0 := by
    dsimp [G]
    exact
      smithSubfacePolynomial_ne_zero_of_nonempty_realised
        y z w T F hrefine.1 hreal
  refine
    ⟨hrefine.1, hpacket, hGne, ?_⟩
  rcases
      rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        hxy hxz hyz hpacket hGne with
    hrigid | hrepair
  · exact Or.inl hrigid
  · right
    exact
      ⟨hrepair.1, hrepair.2,
        repairState_measure_lt_of_progress
          hrepair.2⟩

/-- Restart-facing wrapper: symmetric minimality already gives the same
terminal-or-repair interface used by the local restart classifier. -/
theorem smithFirstWall_hasRepairOrTerminal_symmetricMinimal
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (x y z w : σ)
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hxw : x ≠ w)
    (hyz : y ≠ z)
    (hyw : y ≠ w)
    (hzw : z ≠ w)
    (hchart : IsFourCoordinateChart x y z w)
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (m : ℤ)
    (base : SmithSupportExponent → ℤ)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport y z w F) m base)
    (hmin :
      ∀ e ∈ smithProjectedSupport y z w F,
        m ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport y z w F,
        base e = m)
    (complexity : ℕ) :
    let T :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport y z w F) m base
    let G :=
      smithSubfacePolynomial y z w T F
    HasRepairOrTerminal
      (HasRigidRankOnePacket x y z D G)
      (rankOneRepairState complexity) := by
  dsimp
  have hout :=
    homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair
      x y z w hxy hxz hxw hyz hyw hzw hchart
      hhom hD hcoll m base hpole hmin hattain
      complexity
  rcases hout.2.2.2 with
    hterminal | hrepair
  · exact Or.inl hterminal
  · exact
      Or.inr
        ⟨rankTwoRepairState complexity,
          hrepair.2.1⟩

end

end HC4.Newton
