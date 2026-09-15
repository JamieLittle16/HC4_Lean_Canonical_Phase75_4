import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# A18.4.99: complete layered rank-three geometry of a saturated opening

The sound rank frontier is now finite.

* If the opening special Hessian already has an honest active `2 x 2` chart,
  A18.4.88 supplies complete rank-three geometry.
* Otherwise the special Hessian is genuinely rank one.  The first scalar
  Schur clock selects the first transverse `3 x 3` layer.
  - a nondegenerate first tail or a tail with a nonzero `2 x 2` minor supplies
    the two remaining directions at once;
  - if that tail is still rank one, A18.4.98 selects a second scalar pivot.
    The resulting exact zero-Schur binary clock has a nonzero first normalised
    layer, supplying the third independent repair direction.

Thus a zero-gradient kernel-free saturated opening never needs a semantic
rank-two relabel.  After at most two scalar Schur stages it carries explicit
layered rank-three geometry.  Only then do we attach the finite
`rankOne -> rankThree` repair transition.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Direct finite repair step used only after the complete three-direction
geometry has been retained. -/
theorem rankOne_to_rankThree_repairProgress
    (complexity : ℕ) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankThreeRepairState complexity) := by
  right
  constructor
  · rfl
  · change 1 < 3
    omega

namespace AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry

/-- Saturated opening keeps the source repair coordinate until a geometric
promotion is explicitly attached. -/
theorem opening_repair_eq_source
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source) :
    G.opening.repair = source.repair := by
  rw [G.opening_eq]
  exact source.saturatedKernelOpeningState_repair
    G.kernel G.kernel_ne G.active G.slope_pos

end AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry

/-- Complete rank-three evidence for one saturated opening.  The constructors
record exactly which finite Schur stage supplied the missing directions. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | activeChart
      (firstContact : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source)
      (chart : AdaptiveAlignedSmithCanonicalExactActiveFourBlock firstContact.opening)
      (rankThree : AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry chart complexity)
  | firstTailFull
      (rankOne : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)
      (clock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock rankOne)
      (residual_zero : clock.clock.residualDefect = 0)
      (det_ne_zero : clock.tailConstantBlock.determinantCore ≠ 0)
  | firstTailRankTwo
      (rankOne : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)
      (clock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock rankOne)
      (residual_pos : 0 < clock.clock.residualDefect)
      (witness : clock.tailConstantBlock.HasTwoByTwoMinorWitness)
  | secondScalarLayer
      (rankOne : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)
      (firstClock : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock rankOne)
      (firstResidual_pos : 0 < firstClock.clock.residualDefect)
      (firstTail_rankOne : firstClock.tailConstantBlock.AllTwoByTwoMinorsZero)
      (secondClock : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarClock firstClock)
      (secondLayer_nonzero : secondClock.clock.tailSeries.ConstantBlockNonzero)

namespace AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry

/-- Actual post-opening state on which every constructor's layered geometry is
proved. -/
noncomputable def opening
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (E : AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
      source complexity) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  cases E with
  | activeChart firstContact chart rankThree =>
      exact firstContact.opening
  | firstTailFull rankOne clock residual_zero det_ne_zero =>
      exact rankOne.firstContact.opening
  | firstTailRankTwo rankOne clock residual_pos witness =>
      exact rankOne.firstContact.opening
  | secondScalarLayer rankOne firstClock firstResidual_pos firstTail_rankOne
      secondClock secondLayer_nonzero =>
      exact rankOne.firstContact.opening

/-- The selected opening has not silently changed the repair coordinate. -/
theorem opening_repair_eq_source
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (E : AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
      source complexity) :
    E.opening.repair = source.repair := by
  cases E with
  | activeChart firstContact chart rankThree =>
      exact firstContact.opening_repair_eq_source
  | firstTailFull rankOne clock residual_zero det_ne_zero =>
      exact rankOne.firstContact.opening_repair_eq_source
  | firstTailRankTwo rankOne clock residual_pos witness =>
      exact rankOne.firstContact.opening_repair_eq_source
  | secondScalarLayer rankOne firstClock firstResidual_pos firstTail_rankOne
      secondClock secondLayer_nonzero =>
      exact rankOne.firstContact.opening_repair_eq_source

end AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry

/-- **Finite layered exhaustion of a kernel-free saturated opening.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_layeredRankThree_of_gradientAtZero
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
        source complexity) := by
  rcases source.kernelFreeOpening_completeGeometry_of_gradientAtZero
      kernel hkernel hactive hfree hgrad with ⟨F⟩
  cases F.rankFrontier complexity with
  | rankThree firstContact chart geometry =>
      exact ⟨.activeChart firstContact chart geometry⟩
  | rankOne R =>
      rcases R.scalarSchurClock with ⟨D⟩
      cases D.firstTailRankFrontier with
      | fullRank hres0 hdet =>
          exact ⟨.firstTailFull R D hres0 hdet⟩
      | rankTwo hres hwitness =>
          exact ⟨.firstTailRankTwo R D hres hwitness⟩
      | rankOne hres hall =>
          rcases D.secondScalarClock_of_rankOne hres hall with ⟨S⟩
          exact ⟨.secondScalarLayer R D hres hall S S.clock.tail_constantBlock_nonzero⟩

/-- Global progress packet attached only after the complete layered rank-three
certificate has been constructed. -/
structure AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankThreeProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
    source complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = geometry.opening.withRepairOnly (rankThreeRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target geometry.opening
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Attach the rank-three repair state to the actual opening family. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankThreeProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningLayeredRankThreeGeometry
      source complexity) :
    AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankThreeProgress
      RR source complexity := by
  let target := G.opening.withRepairOnly (rankThreeRepairState complexity)
  have hopenRepair : G.opening.repair = rankOneRepairState complexity :=
    G.opening_repair_eq_source.trans hsrepair
  have hrepair :
      RepairProgress G.opening.repair (rankThreeRepairState complexity) := by
    simpa [hopenRepair] using rankOne_to_rankThree_repairProgress complexity
  have hpresented : CertifiedSameScaleEpisodeProgress RR target G.opening := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [show target.repair = rankThreeRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankThree_repairProgress complexity)
  exact {
    geometry := G
    target := target
    target_eq := rfl
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-- **Sound complete saturated-kernel exit.**
A zero-gradient kernel-free first contact always yields geometry-backed global
rank-three progress; no semantic rank-two promotion or rational recursion
remains. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_globalRankThree_of_gradientAtZero
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankThreeProgress
        RR source complexity) := by
  rcases source.kernelFreeOpening_layeredRankThree_of_gradientAtZero
      complexity kernel hkernel hactive hfree hgrad with ⟨G⟩
  exact ⟨
    AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankThreeProgress.ofGeometry
      RR complexity hsrepair G
  ⟩

end

end HC4.Valuation
