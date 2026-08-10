import HC4.Valuation.RigidClosingRecenteredFirstKernelAssembly
import HC4.Valuation.CanonicalSmithDefectExposure
import HC4.Valuation.ExactKernelDefectDrop
import HC4.Valuation.ZeroSlopeSmithDispatcher
import Mathlib.Tactic

/-!
# Elimination of the rigid zero-common-kernel-slope branch

Phase 75.19 reduced every rigid closing to rank-two progress, a concrete
strict kernel restart, or the single exceptional possibility that the
canonical common source coordinate `3` is active but admits no positive
integral kernel slope.

This file removes that final exceptional branch.

The defect-preserving aligned Smith exposure already contains one full
parameter factor for every power of source coordinate `3`.  For a source
monomial `d`, the exposure coefficient has residual parameter exponent

    r(d) = 2 d_1 + 2 d_2 + 4 d_3 + 20 v(d) - 4.

If `r(d) < d_3`, nonnegativity of the aligned exposure forces the unique
arithmetic pattern

    d_1 = d_2 = 0,  d_3 = 1,  v(d) = 0.

But `v(d)=0` means that the monomial survives on the original special fibre,
and this is exactly the forbidden `w`-linear Smith pattern.  Homogeneity and
the exact collision `0 ~ e0` rule it out.

Kernel divisibility is then transported through the canonical affine
recentering.  Hence slope `1` is always admissible in the common coordinate
`3`, contradicting the zero-maximal-slope branch.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Kernel divisibility and affine translation -/

/-- Every honest kernel inflation visibly satisfies its coefficientwise
kernel divisibility condition. -/
theorem kernelInflateHom_hasIntegralKernelCoefficientDivisibility
    (kernel : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    HasIntegralKernelCoefficientDivisibility
      kernel slope
      (kernelInflateHom (K := K) kernel slope Q) := by
  intro d hd
  refine ⟨MvPolynomial.coeff d Q, ?_⟩
  exact coeff_kernelInflateHom kernel slope Q d

/-- The generator identity behind translation/inflation commutation. -/
theorem polynomialFamilyTranslationHom_kernelInflateHom_X
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (i : Fin 4) :
    polynomialFamilyTranslationHom (K := K) a
        (kernelInflateHom (K := K) kernel slope (MvPolynomial.X i)) =
      kernelInflateHom (K := K) kernel slope
        (polynomialFamilyTranslationHom (K := K)
          (kernelBlowupSection kernel slope a) (MvPolynomial.X i)) := by
  by_cases hi : i = kernel
  · subst i
    simp [polynomialFamilyTranslationHom_X,
      polynomialFamilyTranslationVariable,
      kernelInflateHom, kernelInflateVariable,
      kernelInflateDerivativeCoefficient,
      kernelBlowupSection]
    ring
  · simp [polynomialFamilyTranslationHom_X,
      polynomialFamilyTranslationVariable,
      kernelInflateHom, kernelInflateVariable,
      kernelInflateDerivativeCoefficient,
      kernelBlowupSection, hi]

/-- Kernel inflation commutes with affine source translation after the
translation section is transformed by the same diagonal kernel factor. -/
theorem polynomialFamilyTranslationHom_kernelInflateHom
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilyTranslationHom (K := K) a
        (kernelInflateHom (K := K) kernel slope Q) =
      kernelInflateHom (K := K) kernel slope
        (polynomialFamilyTranslationHom (K := K)
          (kernelBlowupSection kernel slope a) Q) := by
  apply MvPolynomial.induction_on Q
  · intro c
    simp [kernelInflateHom_C]
  · intro p q hp hq
    simpa only [map_add] using
      congrArg₂
        (fun x y : MvPolynomial (Fin 4) (Polynomial K) => x + y)
        hp hq
  · intro p i hp
    have hx :=
      polynomialFamilyTranslationHom_kernelInflateHom_X
        (K := K) kernel slope a i
    simpa only [map_mul] using
      congrArg₂
        (fun x y : MvPolynomial (Fin 4) (Polynomial K) => x * y)
        hp hx

/-- Coefficientwise kernel integrality survives an arbitrary affine source
translation. -/
theorem polynomialFamilyTranslationHom_preservesKernelDivisibility
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility kernel slope P) :
    HasIntegralKernelCoefficientDivisibility
      kernel slope
      (polynomialFamilyTranslationHom (K := K) a P) := by
  let Q := integralKernelBlowupFamily kernel slope P hdiv
  have hinflate :
      kernelInflateHom (K := K) kernel slope Q = P := by
    dsimp [Q]
    exact kernelInflate_integralKernelBlowupFamily_eq
      kernel slope P hdiv
  have hcomm :=
    polynomialFamilyTranslationHom_kernelInflateHom
      (K := K) kernel slope a Q
  have heq :
      polynomialFamilyTranslationHom (K := K) a P =
        kernelInflateHom (K := K) kernel slope
          (polynomialFamilyTranslationHom (K := K)
            (kernelBlowupSection kernel slope a) Q) := by
    rw [← hinflate]
    exact hcomm
  rw [heq]
  exact
    kernelInflateHom_hasIntegralKernelCoefficientDivisibility
      kernel slope
      (polynomialFamilyTranslationHom (K := K)
        (kernelBlowupSection kernel slope a) Q)

/-! ## One unit of coordinate-3 margin in the aligned Smith exposure -/

/-- The aligned Smith residual exponent contains at least one parameter
power for every source `w = x3` exponent.  The only numerical countercase is
the special-fibre `w`-linear pattern, already forbidden by exact collision. -/
theorem CanonicalSmithLosslessFrontier.oneStepResidualExponent_ge_three
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    (hD : 2 ≤ D)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ f.family.support) :
    d (3 : Fin 4) ≤
      canonicalOneStepSmithResidualExponent f.family d := by
  have hlegal := f.oneStepSmith_coefficient_nonnegative d hd
  have hclock := smithSeparatorDelta_projection_eq_raw_sub_four d
  have hle :
      4 ≤ smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder f.family d := by
    unfold alignedSmithCoefficientValue at hlegal
    rw [hclock] at hlegal
    norm_num [alignedSmithRamificationIndex] at hlegal ⊢
    omega
  by_contra hnot
  have hlt :
      canonicalOneStepSmithResidualExponent f.family d < d 3 :=
    Nat.lt_of_not_ge hnot
  have hle' :
      4 ≤
        2 * d 1 + 2 * d 2 + 4 * d 3 +
          20 * smithFamilyCoefficientOrder f.family d := by
    simpa [smithConformalRawExponent, alignedSmithRamificationIndex,
      add_assoc, add_left_comm, add_comm] using hle
  have hlt' :
      (2 * d 1 + 2 * d 2 + 4 * d 3 +
          20 * smithFamilyCoefficientOrder f.family d - 4) < d 3 := by
    simpa [canonicalOneStepSmithResidualExponent,
      smithConformalRawExponent, alignedSmithRamificationIndex,
      add_assoc, add_left_comm, add_comm] using hlt
  have hb : d (1 : Fin 4) = 0 := by omega
  have hc : d (2 : Fin 4) = 0 := by omega
  have hw : d (3 : Fin 4) = 1 := by omega
  have hv : smithFamilyCoefficientOrder f.family d = 0 := by omega
  have hdSpecial :
      d ∈ (polynomialFamilySpecialFiber f.family).support :=
    (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
      f.family hd).1 hv
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber f.family) := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hdSpecial, rfl⟩
  have hspecial :
      HasExactGradientCollision
        (polynomialFamilySpecialFiber f.family)
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
    have h :=
      polynomialFamilyExactGradientCollision_specialFiber
        f.family f.leftSection f.rightSection f.exactCollision
    rw [f.leftSpecial, f.rightSpecial] at h
    exact h
  have hnoW :=
    homogeneous_exactAxisCollision_projectedSupport_noWLinear
      (K := K)
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      f.specialHomogeneous hD hspecial
      (smithSupportExponentOf (1 : Fin 4) 2 3 d) hproj
  have hpat :
      IsWLinearSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
    exact ⟨hb, hc, hw⟩
  exact hnoW hpat

/-- Consequently the entire defect-preserving Smith exposure admits the
integral coordinate-3 kernel slope `1`. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposure_threeSlopeOne
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    HasIntegralKernelCoefficientDivisibility
      (3 : Fin 4) 1 f.defectSmithExposureFamily := by
  intro d hdExposure
  have hdRam :
      d ∈
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex f.family).support := by
    unfold CanonicalSmithLosslessFrontier.defectSmithExposureFamily at hdExposure
    exact
      support_integralSmithConformalFamily_subset
        2 2
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex f.family)
        f.oneStepSmith_integralCoefficients
        hdExposure
  have hd : d ∈ f.family.support := by
    exact
      (MvPolynomial.support_map_subset
        (parameterRamificationHom
          (K := K) alignedSmithRamificationIndex)
        f.family) hdRam
  have hmargin := f.oneStepResidualExponent_ge_three hD hd
  rw [f.defectSmithExposure_coefficient hd]
  unfold kernelCoefficientTauPower
  simp only [one_mul]
  have hpow :
      (Polynomial.X ^ d (3 : Fin 4) : Polynomial K) ∣
        Polynomial.X ^
          canonicalOneStepSmithResidualExponent f.family d :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (d (3 : Fin 4))
      (canonicalOneStepSmithResidualExponent f.family d)
      hmargin
  rcases hpow with ⟨c, hc⟩
  refine
    ⟨c *
        parameterRamificationHom
          (K := K) alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d f.family)
            (MvPolynomial.mem_support_iff.mp hd)), ?_⟩
  rw [hc]
  ring

/-! ## Canonical recentering cannot have zero maximal common-kernel slope -/

namespace CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData

variable [CharZero K]
variable {D complexity : ℕ}
variable {f : CanonicalSmithDepartureFrontier (K := K) D complexity}

/-- The canonical recentered rigid source always has integral common-kernel
slope `1`. -/
theorem commonKernelSlopeOne
    (S : f.RigidClosingRecenteredSourceData)
    (hD : 2 ≤ D) :
    HasIntegralKernelCoefficientDivisibility
      rigidClosingCommonKernel 1 S.family := by
  have hExposure :
      HasIntegralKernelCoefficientDivisibility
        (3 : Fin 4) 1 f.defectSmithExposureFamily :=
    f.lossless.defectSmithExposure_threeSlopeOne hD
  have hTranslated :
      HasIntegralKernelCoefficientDivisibility
        (3 : Fin 4) 1 S.original.recenteredFamily := by
    unfold CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData.recenteredFamily
    exact
      polynomialFamilyTranslationHom_preservesKernelDivisibility
        (K := K)
        (3 : Fin 4) 1
        f.defectSmithExposureLeftSection
        f.defectSmithExposureFamily
        hExposure
  rw [S.family_eq_recentered]
  simpa [rigidClosingCommonKernel] using hTranslated

/-- The formerly exceptional zero-maximal-slope branch is impossible. -/
theorem zeroCommonKernelSlopeObstruction_impossible
    (S : f.RigidClosingRecenteredSourceData)
    (hD : 2 ≤ D)
    (hzero : S.HasRigidClosingZeroCommonKernelSlopeObstruction) :
    False := by
  rcases hzero with ⟨_hactive, _hmax, hnone⟩
  exact hnone ⟨1, by decide, S.commonKernelSlopeOne hD⟩

end CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData

/-! ## Final rigid frontier after zero-slope elimination -/

/-- After Phase 75.20 there is only one genuine source-level closing output:
a concrete strict polynomial-family kernel restart. -/
def HasRigidClosingStrictRestartResolution
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop :=
  ∃ S : f.RigidClosingRecenteredSourceData,
    S.HasRigidClosingStrictKernelRestart

/-- Eliminate the zero-slope disjunct from the Phase 75.19 resolution. -/
theorem HasRigidClosingRestartOrZeroSlopeResolution.toStrictRestartResolution
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (hD : 2 ≤ D)
    (h : HasRigidClosingRestartOrZeroSlopeResolution f) :
    HasRigidClosingStrictRestartResolution f := by
  rcases h with ⟨S, hzero | hrestart⟩
  · exact (S.zeroCommonKernelSlopeObstruction_impossible hD hzero).elim
  · exact ⟨S, hrestart⟩

/-- **Phase 75.20 rigid frontier.**
Every canonical rigid departure frontier now gives either immediate
rank-two repair progress or a concrete strict polynomial-family restart. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_recenteredStrictRestart
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidClosingStrictRestartResolution f := by
  rcases
      f.rankTwoProgress_or_recenteredRestartOrZeroSlopeResolution hD with
    hprogress | hresolution
  · exact Or.inl hprogress
  · exact Or.inr (hresolution.toStrictRestartResolution hD)

end

end HC4.Valuation
