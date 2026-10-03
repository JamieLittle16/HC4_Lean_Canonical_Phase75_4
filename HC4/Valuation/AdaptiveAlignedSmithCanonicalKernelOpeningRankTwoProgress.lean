import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactState
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# A18.4.45: nonlinear first contact gives geometry-backed rank-two progress

The nonlinear branch of A18.4.44 is stronger than a rational defect spend.
Before the opening the chosen genuine transverse coordinate is absent from the
special fibre; after the canonical saturated opening the same coordinate has a
nonzero diagonal Hessian entry.  This is a literal new transverse Hessian
direction on the actual post-opening family.

At a canonical rank-one source this retained geometry licenses the finite
rank-one -> rank-two repair promotion on that actual opening state.  The
opening itself may be ramified and is not called progress.  The composite is
globally strict solely because the finite repair measure decreases, exactly as
in the earlier pointed/rank-two geometric macros.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Geometry proving that a saturated kernel opening has created a genuinely
new transverse Hessian direction.

`source_free` records absence of the coordinate before the opening;
`post_hessian_ne` records nonzero second derivative afterwards.  The actual
opening state is retained rather than reconstructed from a numerical clock. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningRankTwoGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  kernel : Fin 4
  kernel_ne : kernel ≠ (0 : Fin 4)
  active : IsActiveKernelCoordinate kernel source.family
  source_free :
    ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
      d kernel = 0
  slope_pos : 0 < saturatedKernelSlope kernel source.family active
  opening : ScaleAwareAdaptiveGeometricRestartState (K := K)
  opening_eq :
    opening = source.saturatedKernelOpeningState kernel kernel_ne active slope_pos
  exponent : Fin 4 →₀ ℕ
  exponent_mem :
    exponent ∈ (polynomialFamilySpecialFiber opening.family).support
  exponent_ge_two : 2 ≤ exponent kernel
  post_hessian_ne :
    MvPolynomial.pderiv kernel
      (MvPolynomial.pderiv kernel
        (polynomialFamilySpecialFiber opening.family)) ≠ 0

/-- Geometry-backed global rank-two macro for a nonlinear saturated opening. -/
structure AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalKernelOpeningRankTwoGeometry source
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = geometry.opening.withRepairOnly (rankTwoRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target geometry.opening
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Attach the finite rank promotion only after the actual opening family has
supplied the new transverse Hessian direction. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankTwoGeometry source) :
    AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
      RR source complexity := by
  let target := G.opening.withRepairOnly (rankTwoRepairState complexity)
  have hopenRepair : G.opening.repair = rankOneRepairState complexity := by
    rw [G.opening_eq]
    simpa using
      (source.saturatedKernelOpeningState_repair
        G.kernel G.kernel_ne G.active G.slope_pos).trans hsrepair
  have hrepair :
      RepairProgress G.opening.repair (rankTwoRepairState complexity) := by
    simpa [hopenRepair] using rankOne_to_rankTwo_repairProgress complexity
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
    rw [show target.repair = rankTwoRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    geometry := G
    target := target
    target_eq := rfl
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-- **Kernel-free opening termination package.**

At rank one, a kernel-free saturated opening has only two sound outcomes:

* it unramifies and yields literal same-scale strict progress; or
* it creates a new transverse Hessian direction on the actual ramified opening
  state, which immediately licenses a geometry-backed rank-two global macro.

No bare rational-spend alternative remains. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_sameScale_or_rankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target source) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
          RR source complexity) := by
  let hq : 0 < saturatedKernelSlope kernel source.family hactive :=
    saturatedKernelSlope_pos kernel source.family hactive hfree
  let opening :=
    source.saturatedKernelOpeningState kernel hkernel hactive hq
  have H := source.kernelFreeFirstContact_unramified_or_nonlinearOpening
    RR kernel hkernel hactive hfree
  dsimp only at H
  rcases H with hprogress | hnonlinear
  · exact Or.inl hprogress
  · rcases hnonlinear with ⟨d, hd, hd2, hHess⟩
    let G : AdaptiveAlignedSmithCanonicalKernelOpeningRankTwoGeometry source := {
      kernel := kernel
      kernel_ne := hkernel
      active := hactive
      source_free := hfree
      slope_pos := hq
      opening := opening
      opening_eq := rfl
      exponent := d
      exponent_mem := by simpa [opening, hq] using hd
      exponent_ge_two := hd2
      post_hessian_ne := by simpa [opening, hq] using hHess
    }
    exact Or.inr
      ⟨AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress.ofGeometry
        RR complexity hsrepair G⟩

end

end HC4.Valuation
