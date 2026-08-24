import HC4.Valuation.AdaptiveAlignedSmithCanonicalUniformRamification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalAllTransverseRationalKernelDispatcher
import Mathlib.Tactic

/-!
# Absolute-scale upgrade for saturated rational-kernel exits

The all-transverse rational-kernel normalisation is geometrically correct, but
its original progress certificate compares the kernel-blowup target with a
locally re-ramified copy of the aligned endpoint.  For the final outer macro we
need the same spend measured against the actual incoming scale-aware state.

The only numerical provenance required from the aligned-Smith macro is the
clock bound

    blocker.defect ≤ alignedSmithRamificationIndex * incoming.rawDefect.

The aligned macro has literal ramification factor
`alignedSmithRamificationIndex = 20`; coefficient-wall endpoints have equality,
while the no-wall primitive endpoint subtracts a nonnegative common parameter
factor and hence satisfies the inequality.

Once this bound is retained, a denominator-clearing factor `R` followed by a
positive saturated kernel blow-up has target clock

    R * blocker.defect - 2*q

at absolute scale

    (R * alignedSmithRamificationIndex) * incoming.scale.

Since `q > 0`, this is strictly below

    (R * alignedSmithRamificationIndex) * incoming.rawDefect.

Thus the exit is a `CertifiedRamifiedRawDefectSpend` from the actual incoming
state, and hence strictly lowers its represented `ScaledDefect`.

This file does not yet reconstruct the clock bound from the compact blocker
object; it packages that one missing piece explicitly so the next provenance
patch can carry it out of the aligned endpoint constructor without touching the
kernel geometry again.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The exact outer-clock provenance needed to interpret a canonical blocker
at the absolute parameter scale of the incoming adaptive state. -/
structure AdaptiveAlignedSmithBlockerClockProvenance
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  blocker : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap
  defect_le :
    blocker.aligned.endpoint.defect ≤
      alignedSmithRamificationIndex * s.rawDefect

namespace AdaptiveAlignedSmithBlockerClockProvenance

/-- Propositional inhabitation wrapper for the data-bearing ramified-spend
certificate.  `CertifiedRamifiedRawDefectSpend` lives in `Type` because it
retains the ramification factor; dispatcher alternatives need a `Prop`. -/
def HasCertifiedRamifiedRawDefectSpend
    (target source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop :=
  Nonempty (CertifiedRamifiedRawDefectSpend target source)

/-- A propositionally packaged ramified spend still yields the strict scaled
defect inequality carried by its underlying certificate. -/
theorem HasCertifiedRamifiedRawDefectSpend.scaledDefect_lt
    {target source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HasCertifiedRamifiedRawDefectSpend target source) :
    target.scaledDefect < source.scaledDefect := by
  change Nonempty (CertifiedRamifiedRawDefectSpend target source) at h
  rcases h with ⟨hcert⟩
  exact hcert.scaledDefect_lt

/-- A positive saturated rational slope on any non-longitudinal coordinate is
an honest scale-changing defect spend from the actual incoming state once the
aligned endpoint clock bound is retained. -/
theorem exists_certifiedRamifiedRawDefectSpend_of_positiveRecenteredSaturatedKernelSlope
    (P : AdaptiveAlignedSmithBlockerClockProvenance (K := K) s)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel
        P.blocker.aligned.endpoint.rightRecenteredFamily)
    (hq :
      0 < saturatedKernelSlope kernel
        P.blocker.aligned.endpoint.rightRecenteredFamily hactive) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedRawDefectSpend target s := by
  let B := P.blocker
  let E := B.aligned.endpoint
  let P₀ := E.rightRecenteredFamily
  let r₀ := E.rightRecenteredRightSection
  let R := kernelSlopeDenominatorClearingRamification kernel P₀
  let q := saturatedKernelSlope kernel P₀ hactive
  let Pram := parameterRamificationFamily (K := K) R P₀
  let rram := parameterRamificationSection (K := K) R r₀
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel P₀ hactive
  let P₁ := integralKernelBlowupFamily kernel q Pram hdiv
  let r₁ := kernelBlowupSection kernel q rram
  let P₂ := polynomialFamilyTranslationHom (K := K) r₁ P₁
  let b₂ := polynomialSectionDifference r₁ (zeroPolynomialSection (K := K))

  have hRpos : 0 < R := by
    dsimp [R, P₀]
    exact kernelSlopeDenominatorClearingRamification_pos
      kernel E.rightRecenteredFamily
  have hqpos : 0 < q := by
    simpa [q, P₀, B, E] using hq

  have hdef₀ :
      HasPolynomialFamilyHessianDefect (K := K) P₀ E.defect := by
    simpa [P₀] using E.rightRecenteredFamily_hessianDefect
  have hdefRam :
      HasPolynomialFamilyHessianDefect (K := K) Pram (R * E.defect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R E.defect P₀ hdef₀
  have hdef₁ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₁ (R * E.defect - 2 * q) := by
    dsimp [P₁]
    exact integralKernelBlowup_hasHessianDefect_sub
      kernel q (R * E.defect) Pram hdiv hdefRam
  have hdef₂ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₂ (R * E.defect - 2 * q) := by
    dsimp [P₂]
    exact polynomialFamilyTranslationHom_preservesHessianDefect
      (K := K) r₁ P₁ hdef₁

  have hdegree₀ : NonlinearDegreeBound s.degreeCap P₀ := by
    simpa [P₀, E, B] using E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R P₀ hdegree₀
  have hdegree₁ : NonlinearDegreeBound s.degreeCap P₁ := by
    dsimp [P₁]
    exact nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q kernel Pram hdegreeRam hdiv
  have hdegree₂ : NonlinearDegreeBound s.degreeCap P₂ := by
    dsimp [P₂]
    exact nonlinearDegreeBound_polynomialFamilyTranslationHom
      s.degreeCap r₁ P₁ hdegree₁

  have hcoll₀ :
      HasPolynomialFamilyExactGradientCollision
        P₀ (zeroPolynomialSection (K := K)) r₀ := by
    simpa [P₀, r₀, E, B] using E.rightRecenteredFamily_exactCollision
  have hcollRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)))
        rram := by
    dsimp [Pram, rram]
    exact polynomialFamilyExactGradientCollision_parameterRamification
      R P₀ (zeroPolynomialSection (K := K)) r₀ hcoll₀
  have hcoll₁raw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q Pram hdiv
      (parameterRamificationSection (K := K) R
        (zeroPolynomialSection (K := K)))
      rram hcollRam
  have hramZero :
      parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [parameterRamificationSection, zeroPolynomialSection]
  have hzeroSection :
      kernelBlowupSection kernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    rw [hramZero]
    exact kernelBlowupSection_zeroPolynomialSection kernel q
  have hcoll₁ :
      HasPolynomialFamilyExactGradientCollision
        P₁ (zeroPolynomialSection (K := K)) r₁ := by
    rw [hzeroSection] at hcoll₁raw
    simpa [P₁, r₁] using hcoll₁raw
  have hswap :
      HasPolynomialFamilyExactGradientCollision
        P₁ r₁ (zeroPolynomialSection (K := K)) := by
    intro i
    exact (hcoll₁ i).symm
  have hcoll₂ :
      HasPolynomialFamilyExactGradientCollision
        P₂ (zeroPolynomialSection (K := K)) b₂ := by
    simpa [P₂, b₂] using
      (polynomialFamilyExactGradientCollision_recenter
        (K := K) P₁ r₁ (zeroPolynomialSection (K := K)) hswap)

  have hrramSpecial :
      polynomialSectionSpecialPoint rram =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    dsimp [rram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos r₀]
    simpa [r₀, E, B] using E.rightRecenteredRightSection_specialPoint
  have hr₁special :
      polynomialSectionSpecialPoint r₁ =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hqpos rram]
      simp [coordinateAxisPoint, hkernel]
    · dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q rram hi]
      exact congrFun hrramSpecial i
  have hb₂special :
      polynomialSectionSpecialPoint b₂ =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [b₂]
    rw [polynomialSectionSpecialPoint_difference, hr₁special]
    funext i
    simp [zeroPolynomialSection, polynomialSectionSpecialPoint]

  have hcost : 2 * q ≤ R * E.defect := by
    exact two_mul_slope_le_of_integralKernelBlowup
      kernel q (R * E.defect) Pram hdiv hdefRam
  have hclock : R * E.defect - 2 * q < R * E.defect := by
    omega

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * E.defect - 2 * q
      scale := (R * alignedSmithRamificationIndex) * s.scale
      scale_pos := Nat.mul_pos
        (Nat.mul_pos hRpos alignedSmithRamificationIndex_pos) s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P₂
      movingSection := b₂
      hessianDefect := hdef₂
      nonlinearDegreeBound := hdegree₂
      exactCollision := hcoll₂
      sectionSpecial := hb₂special }

  have hboundR :
      R * E.defect ≤
        R * (alignedSmithRamificationIndex * s.rawDefect) := by
    exact Nat.mul_le_mul_left R (by simpa [B, E] using P.defect_le)
  have hraw :
      R * E.defect - 2 * q <
        (R * alignedSmithRamificationIndex) * s.rawDefect := by
    calc
      R * E.defect - 2 * q < R * E.defect := hclock
      _ ≤ R * (alignedSmithRamificationIndex * s.rawDefect) := hboundR
      _ = (R * alignedSmithRamificationIndex) * s.rawDefect := by
        ac_rfl

  refine ⟨target, ?_⟩
  change Nonempty (CertifiedRamifiedRawDefectSpend target s)
  exact ⟨
    { ramification := R * alignedSmithRamificationIndex
      ramification_pos := Nat.mul_pos hRpos alignedSmithRamificationIndex_pos
      scale_eq := by rfl
      raw_lt := by simpa [target] using hraw }
  ⟩

/-- Scale-sound one-coordinate rational-kernel normalisation.  A positive
saturated slope now exits directly from the incoming state; otherwise the
honest recentered family has slope zero in that coordinate. -/
theorem certifiedRamifiedSpend_or_recenteredZeroRationalSlope
    (P : AdaptiveAlignedSmithBlockerClockProvenance (K := K) s)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedRawDefectSpend target s) ∨
      AdaptiveRecenteredKernelZeroRationalSlopeObstruction P.blocker kernel := by
  let hactive :
      IsActiveKernelCoordinate kernel
        P.blocker.aligned.endpoint.rightRecenteredFamily :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel P.blocker.aligned.endpoint.rightRecenteredFamily
      P.blocker.aligned.endpoint.defect
      P.blocker.aligned.endpoint.rightRecenteredFamily_hessianDefect
  let q := saturatedKernelSlope kernel
    P.blocker.aligned.endpoint.rightRecenteredFamily hactive
  by_cases hzero : q = 0
  · right
    refine ⟨hactive, ?_⟩
    simpa [q, hactive] using hzero
  · left
    have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    apply P.exists_certifiedRamifiedRawDefectSpend_of_positiveRecenteredSaturatedKernelSlope
      kernel hkernel hactive
    simpa [q, hactive] using hpos

/-- Run the scale-sound rational-kernel normalisation in all three transverse
coordinates.  Any positive rational slope is now an absolute-scale spend from
`s`; the only residual source normal form has saturated slope zero in all
three transverse directions. -/
theorem certifiedRamifiedSpend_or_allTransverseZeroRationalSlope
    (P : AdaptiveAlignedSmithBlockerClockProvenance (K := K) s) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedRawDefectSpend target s) ∨
      AdaptiveRecenteredAllTransverseZeroRationalSlope P.blocker := by
  rcases P.certifiedRamifiedSpend_or_recenteredZeroRationalSlope
      (1 : Fin 4) (by decide) with hstrict | h₁
  · exact Or.inl hstrict
  rcases P.certifiedRamifiedSpend_or_recenteredZeroRationalSlope
      (2 : Fin 4) (by decide) with hstrict | h₂
  · exact Or.inl hstrict
  rcases P.certifiedRamifiedSpend_or_recenteredZeroRationalSlope
      (3 : Fin 4) (by decide) with hstrict | h₃
  · exact Or.inl hstrict
  exact Or.inr ⟨h₁, h₂, h₃⟩

end AdaptiveAlignedSmithBlockerClockProvenance

end

end HC4.Valuation
