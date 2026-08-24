import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# A18.4.44: nonlinear saturated first contact is finite rank progress

A18.4.39 shows that a saturated opening of a previously-free transverse
coordinate has only two possibilities:

* a kernel-linear exposed monomial, which unramifies to literal same-scale
  strict progress; or
* an exposed monomial of kernel exponent at least two, hence a nonzero
  diagonal Hessian entry in the newly opened direction.

The second branch must not be erased into a bare cross-scale defect spend.
It is precisely a new independent Hessian activity event, so this file retains
that geometry on the actual ramified first-contact family and immediately
advances the finite repair rank from one to two.

The global macro key orders repair rank before raw defect.  Consequently the
composite

    ramified first contact + geometry-certified rank promotion

is strict independently of the new raw clock or parameter scale.  This is the
finite-rank consumption promised by A18.4.39 and removes the quotient-clock
obstruction without adding a new numerical induction coordinate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Geometry retained by the nonlinear half of saturated first contact.

`opened` is the actual denominator-cleared integral-kernel family, already
packaged as a canonical scale-aware state.  The source special fibre was free
of `kernel`, while the opened special fibre has a literal supported monomial
of exponent at least two and therefore a nonzero diagonal Hessian entry in
that direction. -/
structure AdaptiveAlignedSmithCanonicalKernelFirstContactRankTwoGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  kernel : Fin 4
  kernel_ne_longitudinal : kernel ≠ (0 : Fin 4)
  source_active : IsActiveKernelCoordinate kernel source.family
  source_specialFiber_free :
    ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
      d kernel = 0
  opened : ScaleAwareAdaptiveGeometricRestartState (K := K)
  ramification : ℕ
  ramification_pos : 0 < ramification
  slope : ℕ
  slope_pos : 0 < slope
  opened_scale : opened.scale = ramification * source.scale
  opened_rawDefect :
    opened.rawDefect = ramification * source.rawDefect - 2 * slope
  opened_repair : opened.repair = source.repair
  ramifiedSpend : CertifiedRamifiedRawDefectSpend opened source
  witness : Fin 4 →₀ ℕ
  witness_mem : witness ∈ (polynomialFamilySpecialFiber opened.family).support
  witness_kernel_ge_two : 2 ≤ witness kernel
  diagonalHessian_ne :
    MvPolynomial.pderiv kernel
      (MvPolynomial.pderiv kernel
        (polynomialFamilySpecialFiber opened.family)) ≠ 0

/-- The nonlinear first-contact geometry together with the justified finite
rank promotion.  The recursive target has exactly the opened polynomial
family, section and scale; only its repair rank is advanced. -/
structure AdaptiveAlignedSmithCanonicalGlobalKernelFirstContactRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalKernelFirstContactRankTwoGeometry source
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = geometry.opened.withRepairOnly (rankTwoRepairState complexity)
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Final first-contact outcome: either literal same-scale recursive progress,
or an actual ramified first-contact family carrying new transverse Hessian
activity and a geometry-certified rank-two promotion. -/
inductive AdaptiveAlignedSmithCanonicalKernelFirstContactGlobalOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | sameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : CertifiedSameScaleEpisodeProgress RR target source)
  | rankTwo
      (progress : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalKernelFirstContactRankTwoProgress
          RR source complexity))

/-- Package the denominator-cleared saturated opening itself as a canonical
scale-aware state for an arbitrary transverse coordinate. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let R := kernelSlopeDenominatorClearingRamification kernel s.family
  let q := saturatedKernelSlope kernel s.family hactive
  let Pram := parameterRamificationFamily (K := K) R s.family
  let bram := parameterRamificationSection (K := K) R s.movingSection
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel s.family hactive
  let Pnext := integralKernelBlowupFamily kernel q Pram hdiv
  let bnext := kernelBlowupSection kernel q bram

  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos kernel s.family
  have hqpos : 0 < q :=
    saturatedKernelSlope_pos kernel s.family hactive hfree

  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * s.rawDefect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R s.rawDefect s.family s.hessianDefect
  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (R * s.rawDefect - 2 * q) := by
    dsimp [Pnext]
    exact integralKernelBlowup_hasHessianDefect_sub
      kernel q (R * s.rawDefect) Pram hdiv hdefRam

  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R s.family s.nonlinearDegreeBound
  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext := by
    dsimp [Pnext]
    exact nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q kernel Pram hdegreeRam hdiv

  have hcollRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K))) bram := by
    dsimp [Pram, bram]
    exact polynomialFamilyExactGradientCollision_parameterRamification
      R s.family (zeroPolynomialSection (K := K)) s.movingSection
      s.exactCollision
  have hcollNextRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q Pram hdiv
      (parameterRamificationSection (K := K) R
        (zeroPolynomialSection (K := K))) bram hcollRam
  have hramZero :
      parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [parameterRamificationSection, zeroPolynomialSection]
  have hzeroBlow :
      kernelBlowupSection kernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    rw [hramZero]
    exact kernelBlowupSection_zeroPolynomialSection kernel q
  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    rw [hzeroBlow] at hcollNextRaw
    simpa [Pnext, bnext] using hcollNextRaw

  have hspecialRam :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos s.movingSection]
    exact s.sectionSpecial
  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      dsimp [bnext]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hqpos bram]
      simp [coordinateAxisPoint, hkernel]
    · dsimp [bnext]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q bram hi]
      exact congrFun hspecialRam i

  exact {
    rawDefect := R * s.rawDefect - 2 * q
    scale := R * s.scale
    scale_pos := Nat.mul_pos hRpos s.scale_pos
    degreeCap := s.degreeCap
    sourceComplexity := s.sourceComplexity
    repair := s.repair
    family := Pnext
    movingSection := bnext
    hessianDefect := hdefNext
    nonlinearDegreeBound := hdegreeNext
    exactCollision := hcollNext
    sectionSpecial := hspecialNext
  }

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    (s.saturatedKernelOpenedState kernel hkernel hactive hfree).scale =
      kernelSlopeDenominatorClearingRamification kernel s.family * s.scale := by
  rfl

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    (s.saturatedKernelOpenedState kernel hkernel hactive hfree).rawDefect =
      kernelSlopeDenominatorClearingRamification kernel s.family * s.rawDefect -
        2 * saturatedKernelSlope kernel s.family hactive := by
  rfl

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    (s.saturatedKernelOpenedState kernel hkernel hactive hfree).repair = s.repair := by
  rfl

/-- The opened state is the honest ramified raw-defect spend which the older
frontier remembered only propositionally. -/
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState_ramifiedSpend
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    CertifiedRamifiedRawDefectSpend
      (s.saturatedKernelOpenedState kernel hkernel hactive hfree) s := by
  let R := kernelSlopeDenominatorClearingRamification kernel s.family
  let q := saturatedKernelSlope kernel s.family hactive
  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos kernel s.family
  have hqpos : 0 < q :=
    saturatedKernelSlope_pos kernel s.family hactive hfree
  let Pram := parameterRamificationFamily (K := K) R s.family
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel s.family hactive
  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * s.rawDefect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R s.rawDefect s.family s.hessianDefect
  have hcost : 2 * q ≤ R * s.rawDefect := by
    dsimp [q, Pram, hdiv]
    exact two_mul_slope_le_of_integralKernelBlowup
      (K := K) kernel
      (saturatedKernelSlope kernel s.family hactive)
      (R * s.rawDefect)
      (parameterRamificationFamily (K := K) R s.family)
      (saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive)
      hdefRam
  refine {
    ramification := R
    ramification_pos := hRpos
    scale_eq := ?_
    raw_lt := ?_
  }
  · rfl
  · rw [s.saturatedKernelOpenedState_rawDefect]
    dsimp [R, q]
    omega

/-- **A18.4.44 first-contact rank consumption.**

At rank one, every saturated opening of a previously-free transverse kernel is
already globally well-founded:

* a kernel-linear contact is literal same-scale strict progress by A18.4.39;
* a nonlinear contact is packaged as the actual ramified opened state, its
  new diagonal Hessian activity is retained, and that state is promoted to
  rank two.  The finite repair decrease is the outermost component of the
  global macro key, so this composite move is strict independently of scale.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpening_globalOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    AdaptiveAlignedSmithCanonicalKernelFirstContactGlobalOutcome
      RR s complexity := by
  rcases s.saturatedKernelOpening_unramified_or_nonlinearHessian
      RR kernel hkernel hactive hfree with hsame | hnonlinear
  · rcases hsame with ⟨target, hprogress⟩
    exact .sameScale target hprogress
  · let opened := s.saturatedKernelOpenedState kernel hkernel hactive hfree
    let R := kernelSlopeDenominatorClearingRamification kernel s.family
    let q := saturatedKernelSlope kernel s.family hactive
    have hRpos : 0 < R :=
      kernelSlopeDenominatorClearingRamification_pos kernel s.family
    have hqpos : 0 < q :=
      saturatedKernelSlope_pos kernel s.family hactive hfree
    rcases hnonlinear with ⟨d, hd, hd2, hdiag⟩
    have hdOpened :
        d ∈ (polynomialFamilySpecialFiber opened.family).support := by
      simpa [opened, ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState,
        R, q] using hd
    have hdiagOpened :
        MvPolynomial.pderiv kernel
          (MvPolynomial.pderiv kernel
            (polynomialFamilySpecialFiber opened.family)) ≠ 0 := by
      simpa [opened, ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpenedState,
        R, q] using hdiag
    let G : AdaptiveAlignedSmithCanonicalKernelFirstContactRankTwoGeometry s := {
      kernel := kernel
      kernel_ne_longitudinal := hkernel
      source_active := hactive
      source_specialFiber_free := hfree
      opened := opened
      ramification := R
      ramification_pos := hRpos
      slope := q
      slope_pos := hqpos
      opened_scale := by rfl
      opened_rawDefect := by rfl
      opened_repair := by rfl
      ramifiedSpend := s.saturatedKernelOpenedState_ramifiedSpend
        kernel hkernel hactive hfree
      witness := d
      witness_mem := hdOpened
      witness_kernel_ge_two := hd2
      diagonalHessian_ne := hdiagOpened
    }
    let target := opened.withRepairOnly (rankTwoRepairState complexity)
    have hrepair : RepairProgress s.repair (rankTwoRepairState complexity) := by
      simpa [hsrepair] using rankOne_to_rankTwo_repairProgress complexity
    have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
      unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
      apply Prod.Lex.left
      simpa [target, opened,
        ScaleAwareAdaptiveGeometricRestartState.withRepairOnly] using
        repairState_measure_lt_of_progress hrepair
    exact .rankTwo ⟨{
      geometry := G
      target := target
      target_eq := rfl
      globalProgress := hglobal
    }⟩

end

end HC4.Valuation
