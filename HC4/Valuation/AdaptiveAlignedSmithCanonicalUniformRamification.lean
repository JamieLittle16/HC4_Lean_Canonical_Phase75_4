import HC4.Valuation.AdaptiveAlignedSmithCanonicalSoundEpisodeInterface
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoFixedScaleProgress
import HC4.Valuation.ScaledDefect
import Mathlib.Tactic

/-!
# Uniform degree-bounded ramification and absolute scale accounting

The final adaptive assembly must not forget the parameter scale when one
ramification is performed on top of another.  This file supplies two pieces
of bookkeeping which are independent of the remaining stationary geometry.

First, `NonlinearDegreeBound degreeCap` gives a uniform bound on *every*
source-coordinate exponent occurring in the family: affine/quadratic terms
are bounded by `2`, while nonlinear terms are bounded by `degreeCap`.
Consequently every positive denominator `d i` which can occur in a rational
kernel slope divides the single number

    (max 2 degreeCap)!.

Thus denominator clearing is degree-bounded; it is not an unbounded search
through new prime denominators.

Second, pure parameter ramification of an already scale-aware state is
recorded at the **absolute** scale `R * s.scale`, not at the local scale `R`.
The represented scaled Hessian defect is unchanged under this rebase.  A
strict raw-clock spend after that rebase therefore gives an honest strict
cross-multiplication decrease of the represented rational defect.

No well-foundedness claim for arbitrary rational scales is made here.  The
point is to remove the scale-loss bug and isolate the remaining termination
argument on a degree-bounded ramification monoid.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## A universal denominator depending only on the degree cap -/

/-- Every source coordinate occurring in a degree-bounded family is bounded
by `max 2 degreeCap`.  The `2` covers the affine/quadratic part which is
intentionally outside `NonlinearDegreeBound`. -/
theorem support_coordinate_le_max_two_degreeCap
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (degreeCap : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support)
    (i : Fin 4) :
    d i ≤ max 2 degreeCap := by
  by_cases hnonlinear : 3 ≤ HC4.Polynomial.ordinaryDegree4 d
  · have hcap : HC4.Polynomial.ordinaryDegree4 d ≤ degreeCap :=
      hdegree d hd hnonlinear
    exact le_trans (coordinate_le_ordinaryDegree4 d i)
      (le_trans hcap (Nat.le_max_right 2 degreeCap))
  · have hsmall : HC4.Polynomial.ordinaryDegree4 d ≤ 2 := by omega
    exact le_trans (coordinate_le_ordinaryDegree4 d i)
      (le_trans hsmall (Nat.le_max_left 2 degreeCap))

/-- One canonical denominator which clears every possible positive source
coordinate exponent allowed by `degreeCap`. -/
def canonicalDegreeRamification (degreeCap : ℕ) : ℕ :=
  (max 2 degreeCap).factorial

@[simp]
theorem canonicalDegreeRamification_pos (degreeCap : ℕ) :
    0 < canonicalDegreeRamification degreeCap := by
  simpa [canonicalDegreeRamification] using
    Nat.factorial_pos (max 2 degreeCap)

/-- Every positive coordinate exponent in the support divides the universal
degree ramification. -/
theorem support_coordinate_dvd_canonicalDegreeRamification
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (degreeCap : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support)
    (i : Fin 4)
    (hdi : 0 < d i) :
    d i ∣ canonicalDegreeRamification degreeCap := by
  unfold canonicalDegreeRamification
  exact Nat.dvd_factorial hdi
    (support_coordinate_le_max_two_degreeCap
      P degreeCap hdegree d hd i)

/-- In particular, every positive denominator occurring in an active kernel
support is cleared by the same degree-only ramification. -/
theorem activeKernelSupport_coordinate_dvd_canonicalDegreeRamification
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (degreeCap : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (kernel : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ activeKernelSupport kernel P) :
    d kernel ∣ canonicalDegreeRamification degreeCap := by
  have hdP : d ∈ P.support := (Finset.mem_filter.mp hd).1
  have hdpos : 0 < d kernel := (Finset.mem_filter.mp hd).2
  exact support_coordinate_dvd_canonicalDegreeRamification
    P degreeCap hdegree d hdP kernel hdpos

/-! ## Absolute-scale ramification of a scale-aware state -/

/-- The scaled-defect pair represented by a scale-aware adaptive state. -/
def ScaleAwareAdaptiveGeometricRestartState.scaledDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : ScaledDefect :=
  ⟨s.rawDefect, s.scale, s.scale_pos⟩

/-- Pure parameter ramification of an already scale-aware state.

The crucial point is that the new absolute scale is `R * s.scale`; recording
only `R` would lose provenance when this operation is nested. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let Pram := parameterRamificationFamily (K := K) R s.family
  let bram := parameterRamificationSection (K := K) R s.movingSection

  have hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * s.rawDefect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R s.rawDefect s.family s.hessianDefect

  have hdegree : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R s.family s.nonlinearDegreeBound

  have hcollisionRaw :=
    polynomialFamilyExactGradientCollision_parameterRamification
      R s.family (zeroPolynomialSection (K := K))
      s.movingSection s.exactCollision

  have hzero :
      parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [zeroPolynomialSection, parameterRamificationSection,
      parameterRamificationHom]

  have hcollision :
      HasPolynomialFamilyExactGradientCollision
        Pram (zeroPolynomialSection (K := K)) bram := by
    rw [hzero] at hcollisionRaw
    simpa [Pram, bram] using hcollisionRaw

  have hspecial :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hR s.movingSection]
    exact s.sectionSpecial

  exact
    { rawDefect := R * s.rawDefect
      scale := R * s.scale
      scale_pos := Nat.mul_pos hR s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Pram
      movingSection := bram
      hessianDefect := hdef
      nonlinearDegreeBound := hdegree
      exactCollision := hcollision
      sectionSpecial := hspecial }

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ) (hR : 0 < R) :
    (s.parameterRamifiedState R hR).rawDefect = R * s.rawDefect := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ) (hR : 0 < R) :
    (s.parameterRamifiedState R hR).scale = R * s.scale := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_degreeCap
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ) (hR : 0 < R) :
    (s.parameterRamifiedState R hR).degreeCap = s.degreeCap := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_sourceComplexity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ) (hR : 0 < R) :
    (s.parameterRamifiedState R hR).sourceComplexity = s.sourceComplexity := rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ) (hR : 0 < R) :
    (s.parameterRamifiedState R hR).repair = s.repair := rfl

/-- Pure ramification changes the presentation but represents exactly the same
scaled Hessian defect. -/
theorem ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_equivalent
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R) :
    ScaledDefect.Equivalent
      (s.parameterRamifiedState R hR).scaledDefect
      s.scaledDefect := by
  unfold ScaledDefect.Equivalent
  simp only [ScaleAwareAdaptiveGeometricRestartState.scaledDefect,
    ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_rawDefect,
    ScaleAwareAdaptiveGeometricRestartState.parameterRamifiedState_scale]
  ac_rfl

/-- A strict raw-clock spend performed after a pure ramification is a genuine
strict decrease of the represented scaled defect from the *pre-ramified*
state.  This is cross-scale arithmetic, not yet a well-foundedness claim. -/
theorem ScaleAwareAdaptiveGeometricRestartState.scaledDefect_lt_of_ramified_raw_lt
    (s t : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R)
    (hscale : t.scale = R * s.scale)
    (hraw : t.rawDefect < R * s.rawDefect) :
    t.scaledDefect < s.scaledDefect := by
  change t.rawDefect * s.scale < s.rawDefect * t.scale
  rw [hscale]
  have hmul :
      t.rawDefect * s.scale < (R * s.rawDefect) * s.scale :=
    (Nat.mul_lt_mul_right s.scale_pos).2 hraw
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- Certificate for a strict clock spend after an explicit pure ramification
rebase.  Unlike the old loose `reentry`, it retains the exact factor and the
absolute-scale equation. -/
structure CertifiedRamifiedRawDefectSpend
    (t s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type where
  ramification : ℕ
  ramification_pos : 0 < ramification
  scale_eq : t.scale = ramification * s.scale
  raw_lt : t.rawDefect < ramification * s.rawDefect

/-- Every certified ramified spend strictly lowers the represented scaled
defect by cross multiplication. -/
theorem CertifiedRamifiedRawDefectSpend.scaledDefect_lt
    {t s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : CertifiedRamifiedRawDefectSpend t s) :
    t.scaledDefect < s.scaledDefect := by
  exact s.scaledDefect_lt_of_ramified_raw_lt
    t h.ramification h.ramification_pos h.scale_eq h.raw_lt

end

end HC4.Valuation
