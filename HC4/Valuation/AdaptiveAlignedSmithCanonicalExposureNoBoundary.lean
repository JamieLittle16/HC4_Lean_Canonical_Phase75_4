import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalAlignedBoundaryAbsorber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedSurvivingClosure
import Mathlib.Tactic

/-!
# A18.4.37: the canonical surviving exposure cannot create a section boundary

The final neutral presentation left by A18.4.36 is an exposure boundary.  The
canonical surviving wall has much stronger arithmetic than the generic
exposure interface records:

* its combined source level is exactly `4`;
* its source weights are `(0,2,2,4)`, hence every transverse weight is at most
  `4`;
* every admissible exposure ramification satisfies `4 < R` by the
  `positiveLayerSeparated` field;
* before exposure, every transverse marked-section coordinate has zero
  constant coefficient because the state is pointed at `e₀`.

Thus a transverse section coordinate is divisible by `X`; after ramification
it is divisible by `X^R`.  Pulling it back through a source weight at most `4`
leaves at least one factor of `X`.  Consequently every transverse coordinate
of the exposed right section still has zero special value.

So the `AdaptiveSmithExposureSectionBoundary` constructor is unreachable for
the *canonical* surviving wall.  This removes the last neutral presentation
without adding a termination measure or a new geometric hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- If a ramified section coordinate starts with zero constant coefficient and
its divided source weight is strictly smaller than the ramification index,
then the integral pullback still has zero constant coefficient. -/
theorem integralAdaptiveSmithSection_constantCoeff_zero_of_weight_lt_ramification
    (R : ℕ)
    (W : Fin 4 → ℕ)
    (a : Fin 4 → Polynomial K)
    (hdiv : HasIntegralAdaptiveSmithSection W
      (parameterRamificationSection (K := K) R a))
    (i : Fin 4)
    (ha0 : Polynomial.constantCoeff (a i) = 0)
    (hlt : W i < R) :
    Polynomial.constantCoeff
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) R a) hdiv i) = 0 := by
  have hXdvd : Polynomial.X ∣ a i :=
    Polynomial.X_dvd_iff.mpr ha0
  have hXdvd1 : Polynomial.X ^ 1 ∣ a i := by
    simpa using hXdvd
  have hram :
      Polynomial.X ^ R ∣
        parameterRamificationSection (K := K) R a i := by
    change Polynomial.X ^ R ∣ parameterRamificationHom (K := K) R (a i)
    simpa using parameterRamification_pow_dvd
      (K := K) R 1 (a i) hXdvd1
  have hramCoeff :
      (parameterRamificationSection (K := K) R a i).coeff (W i) = 0 := by
    rw [Polynomial.X_pow_dvd_iff] at hram
    exact hram (W i) hlt
  have hinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq
      W (parameterRamificationSection (K := K) R a) hdiv) i
  have hcoeff := congrArg
    (fun p : Polynomial K => p.coeff (W i)) hinflate
  change
    (Polynomial.X ^ W i *
      integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) R a) hdiv i).coeff (W i) =
      (parameterRamificationSection (K := K) R a i).coeff (W i) at hcoeff
  rw [Polynomial.coeff_X_pow_mul'] at hcoeff
  rw [hramCoeff] at hcoeff
  simpa using hcoeff

/-- Each canonical surviving-wall source weight is at most the common level
`4`. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.combinedSourceWeight_le_four
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (i : Fin 4) :
    W.wall.realization.combinedSourceWeight i ≤ 4 := by
  rw [W.wall_eq]
  change W.original.wall.realization.combinedSourceWeight i ≤ 4
  fin_cases i <;>
    simp [HasIntegralAdaptiveSmithWallWeight.combinedSourceWeight,
      W.original.wall_transverseWeight_eq_zero]

/-- Every canonical exposure ramification is strictly larger than `4`.
This uses only the ramification certificate, not the particular oversized
constructor used to produce it. -/
theorem AdaptiveSurvivingWallExposureData.canonicalRamification_gt_four
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall) :
    4 < d.ramification.R := by
  have hmZ : (d.commonLevel : ℤ) = 4 := by
    calc
      (d.commonLevel : ℤ) =
          W.wall.realization.combinedSourceLevel W.wall.level :=
        d.commonLevel_eq
      _ = 4 := W.combinedSourceLevel_eq_four s
  have hm : d.commonLevel = 4 := by
    exact_mod_cast hmZ
  have hsep := d.ramification.positiveLayerSeparated
    1 (by omega) (0 : Fin 4 →₀ ℕ)
  have hsep' : d.commonLevel < d.ramification.R := by
    simpa [Finsupp.weight_apply] using hsep
  omega

/-- Every transverse coordinate of the exposed right section still has zero
special value. -/
theorem AdaptiveSurvivingWallExposureData.canonicalRightSpecial_transverse_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (i : Fin 4)
    (hi : i ≠ (0 : Fin 4)) :
    polynomialSectionSpecialPoint d.rightSection i = 0 := by
  let a := W.original.aligned.toAdaptiveState s
  let weights := W.wall.realization.combinedSourceWeight
  let bram := parameterRamificationSection (K := K) d.ramification.R a.movingSection
  have hspecial :
      ∀ j, weights j = 0 ∨ Polynomial.constantCoeff (a.movingSection j) = 0 := by
    intro j
    by_cases hj : j = (0 : Fin 4)
    · left
      subst j
      exact W.wall.realization.combinedSourceWeight_zero
    · right
      have hjsp := congrFun a.sectionSpecial j
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hj] using hjsp
  let hdiv : HasIntegralAdaptiveSmithSection weights bram :=
    parameterRamificationSection_hasIntegralAdaptiveSmithSection
      d.ramification.R weights d.ramification.sectionWeightsCovered
      a.movingSection hspecial
  have hai0 : Polynomial.constantCoeff (a.movingSection i) = 0 := by
    have hisp := congrFun a.sectionSpecial i
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using hisp
  have hweight : weights i < d.ramification.R := by
    have hle : weights i ≤ 4 := W.combinedSourceWeight_le_four s i
    have hR : 4 < d.ramification.R := d.canonicalRamification_gt_four W
    omega
  have hz := integralAdaptiveSmithSection_constantCoeff_zero_of_weight_lt_ramification
    (K := K) d.ramification.R weights a.movingSection hdiv i hai0 hweight
  change Polynomial.constantCoeff (d.rightSection i) = 0
  simpa [AdaptiveSurvivingWallExposureData.rightSection,
    a, weights, bram, hspecial, hdiv] using hz

/-- **Canonical exposure stays pointed.** -/
theorem AdaptiveSurvivingWallExposureData.canonicalRightSpecial_eq_axis
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall) :
    polynomialSectionSpecialPoint d.rightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  by_cases hi : i = (0 : Fin 4)
  · subst i
    simpa [coordinateAxisPoint] using d.rightSpecial_zero
  · have hz := d.canonicalRightSpecial_transverse_zero W i hi
    simpa [coordinateAxisPoint, hi] using hz

/-- The generic section-boundary alternative of exposure geometry is
impossible on a canonical surviving wall. -/
theorem AdaptiveSurvivingWallExposureData.noCanonicalSectionBoundary
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall) :
    ¬ Nonempty (AdaptiveSmithExposureSectionBoundary d) := by
  intro hboundary
  rcases hboundary with ⟨B⟩
  have haxis := congrFun (d.canonicalRightSpecial_eq_axis W) B.coordinate
  have hz : polynomialSectionSpecialPoint d.rightSection B.coordinate = 0 := by
    simpa [coordinateAxisPoint, B.coordinate_ne_zero] using haxis
  exact B.special_ne_zero hz

end

end HC4.Valuation
