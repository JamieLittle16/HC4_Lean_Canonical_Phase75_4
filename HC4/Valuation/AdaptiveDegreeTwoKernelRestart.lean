import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.CanonicalSmithDefectExposure
import HC4.Valuation.ExactKernelDefectDrop
import HC4.Valuation.ScaledDefect
import HC4.Valuation.AdaptiveGeometricRestartState
import HC4.Valuation.IntegralKernelSlopeExtraction
import HC4.Valuation.AdaptiveCoefficientOrder

/-!
# The unmarked kernel gate at adaptive degree two

When the special fibre is independent of the fourth source coordinate, every
coefficient involving that coordinate has positive parameter order.  After a
sufficiently large ramification this supplies exactly the coefficientwise
divisibility required for a unit inverse kernel blow-up in that coordinate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A quadratic Smith subface is independent of the unmarked coordinate
`3`.  This is the support theorem used by the degree-two dispatcher; callers
do not need to provide `hfree` separately once their special fibre is
identified with this subface. -/
theorem quadraticSmithSubface_free_three
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∀ d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support,
      d (3 : Fin 4) = 0 := by
  intro d hd
  have hdT :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T :=
    smithSubfacePolynomial_supported (1 : Fin 4) 2 3 T F d
      (MvPolynomial.mem_support_iff.mp hd)
  have hshape := hquad _ hdT
  simp only [smithSupportExponentOf] at hshape
  rcases hshape with hshape | hshape | hshape <;> omega

/-- Every coordinate exponent is bounded by the explicit ordinary degree. -/
theorem coordinate_le_ordinaryDegree4
    (d : Fin 4 →₀ ℕ)
    (i : Fin 4) :
    d i ≤ HC4.Polynomial.ordinaryDegree4 d := by
  fin_cases i <;>
    simp [HC4.Polynomial.ordinaryDegree4] <;>
    omega

/-- If the special fibre is independent of the unmarked coordinate `3`, then
every source coefficient involving that coordinate is divisible by the
parameter. -/
theorem unmarkedCoefficient_X_dvd_of_specialFiber_free
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d (3 : Fin 4) = 0) :
    HasParameterCoefficientDivisibility
      (fun d => if d (3 : Fin 4) = 0 then 0 else 1) P := by
  intro d hd
  by_cases hd3 : d (3 : Fin 4) = 0
  · simp [hd3]
  · have hconst :
        Polynomial.constantCoeff (MvPolynomial.coeff d P) = 0 := by
      by_contra hne
      have hdspecial :
          d ∈ (polynomialFamilySpecialFiber P).support := by
        rw [MvPolynomial.mem_support_iff,
          coeff_polynomialFamilySpecialFiber]
        exact hne
      exact hd3 (hfree d hdspecial)
    simpa [hd3] using (Polynomial.X_dvd_iff.mpr hconst)

/-- **Degree-two unmarked-kernel integrality gate.**

Suppose the special fibre is independent of `x₃`, and the family has a
nonlinear source-degree ceiling `degreeCap`.  If the parameter is ramified by
an index strictly larger than both `2` and `degreeCap`, then the ramified
family admits the unit integral kernel blow-up in coordinate `3`.

The explicit lower bound by `2` covers the affine and quadratic source terms,
which are deliberately outside `NonlinearDegreeBound`. -/
theorem parameterRamification_has_unmarkedKernelDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (degreeCap M : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d (3 : Fin 4) = 0)
    (hM : max 2 degreeCap < M) :
    HasIntegralKernelCoefficientDivisibility
      (3 : Fin 4) 1
      (parameterRamificationFamily (K := K) M P) := by
  have hbase :=
    unmarkedCoefficient_X_dvd_of_specialFiber_free
      (K := K) P hfree
  have hram :=
    parameterRamificationFamily_coefficientDivisibility
      (K := K) M
      (fun d => if d (3 : Fin 4) = 0 then 0 else 1)
      P hbase
  intro d hd
  have hdP : d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom (K := K) M) P) hd
  have hd3M : d (3 : Fin 4) ≤ M := by
    by_cases hnonlinear : 3 ≤ HC4.Polynomial.ordinaryDegree4 d
    · have hcap := hdegree d hdP hnonlinear
      exact le_trans (coordinate_le_ordinaryDegree4 d (3 : Fin 4))
        (le_trans hcap (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right 2 degreeCap) hM)))
    · have hsmall : HC4.Polynomial.ordinaryDegree4 d ≤ 2 := by omega
      exact le_trans (coordinate_le_ordinaryDegree4 d (3 : Fin 4))
        (le_trans hsmall (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left 2 degreeCap) hM)))
  by_cases hd3 : d (3 : Fin 4) = 0
  · simp [kernelCoefficientTauPower, hd3]
  · have hramDiv := hram d hd
    simp only [hd3, if_false, mul_one] at hramDiv
    unfold kernelCoefficientTauPower
    apply dvd_trans (b := Polynomial.X ^ M)
    · refine ⟨Polynomial.X ^ (M - d (3 : Fin 4)), ?_⟩
      rw [← pow_add]
      congr 1
      omega
    · simpa using hramDiv

/-! ## Denominator clearing for the saturated first kernel slope -/

/-- A deliberately non-minimal common denominator for all rational kernel
slopes `ord(coeff d) / d(kernel)` occurring in the finite source support.
Using `max 1` keeps the product positive while ignoring zero kernel degrees. -/
noncomputable def kernelSlopeDenominatorClearingRamification
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : ℕ :=
  ∏ d ∈ P.support, max 1 (d kernel)

theorem kernelSlopeDenominatorClearingRamification_pos
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    0 < kernelSlopeDenominatorClearingRamification kernel P := by
  classical
  unfold kernelSlopeDenominatorClearingRamification
  apply Finset.prod_pos
  intro d hd
  omega

/-- Every positive kernel exponent in the support divides the chosen common
ramification index.  Thus all coefficient-order/kernel-degree ratios become
integral after this ramification. -/
theorem kernelExponent_dvd_denominatorClearingRamification
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support)
    (hdpos : 0 < d kernel) :
    d kernel ∣ kernelSlopeDenominatorClearingRamification kernel P := by
  classical
  have hfactor :
      max 1 (d kernel) ∣
        ∏ e ∈ P.support, max 1 (e kernel) :=
    Finset.dvd_prod_of_mem (fun e => max 1 (e kernel)) hd
  have hmax : max 1 (d kernel) = d kernel :=
    Nat.max_eq_right hdpos
  simpa [kernelSlopeDenominatorClearingRamification, hmax] using hfactor

/-- Supported monomials with positive degree in the chosen kernel
coordinate. -/
noncomputable def activeKernelSupport
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset (Fin 4 →₀ ℕ) :=
  P.support.filter (fun d => 0 < d kernel)

theorem activeKernelSupport_nonempty
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    (activeKernelSupport kernel P).Nonempty := by
  rcases hactive with ⟨d, hd, hdpos⟩
  exact ⟨d, by simp [activeKernelSupport, hd, hdpos]⟩

/-- Exact parameter order of every active coefficient is positive when the
special fibre is kernel-free. -/
theorem adaptiveSourceCoefficientParameterOrder_pos_of_specialFiber_free
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d kernel = 0)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ activeKernelSupport kernel P) :
    0 < adaptiveSourceCoefficientParameterOrder P d := by
  have hdP : d ∈ P.support := by
    exact (Finset.mem_filter.mp hd).1
  have hdpos : 0 < d kernel := by
    exact (Finset.mem_filter.mp hd).2
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdP
  have hconst :
      Polynomial.constantCoeff (MvPolynomial.coeff d P) = 0 := by
    by_contra hne
    have hdSpecial : d ∈ (polynomialFamilySpecialFiber P).support := by
      rw [MvPolynomial.mem_support_iff,
        coeff_polynomialFamilySpecialFiber]
      exact hne
    exact (Nat.ne_of_gt hdpos) (hfree d hdSpecial)
  have hXd : (Polynomial.X : Polynomial K) ∣ MvPolynomial.coeff d P :=
    Polynomial.X_dvd_iff.mpr hconst
  unfold adaptiveSourceCoefficientParameterOrder
  rw [dif_neg hcoeffne]
  have hle := polynomial_X_pow_dvd_le_parameterOrder
    (MvPolynomial.coeff d P) hcoeffne 1 (by simpa using hXd)
  omega

/-- Integer slope of one active coefficient after denominator-clearing
ramification. -/
noncomputable def denominatorClearedCoefficientSlope
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ :=
  kernelSlopeDenominatorClearingRamification kernel P *
      adaptiveSourceCoefficientParameterOrder P d / d kernel

/-- The saturated first-contact slope is the finite minimum of the exact
denominator-cleared active coefficient slopes. -/
noncomputable def saturatedKernelSlope
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) : ℕ :=
  ((activeKernelSupport kernel P).image
      (denominatorClearedCoefficientSlope kernel P)).min'
    ((activeKernelSupport_nonempty kernel P hactive).image
      (denominatorClearedCoefficientSlope kernel P))

theorem denominatorClearedCoefficientSlope_pos
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d kernel = 0)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ activeKernelSupport kernel P) :
    0 < denominatorClearedCoefficientSlope kernel P d := by
  have hdP : d ∈ P.support := by
    exact (Finset.mem_filter.mp hd).1
  have hdpos : 0 < d kernel := by
    exact (Finset.mem_filter.mp hd).2
  have horder := adaptiveSourceCoefficientParameterOrder_pos_of_specialFiber_free
    kernel P hfree d hd
  have hdvd := kernelExponent_dvd_denominatorClearingRamification
    kernel P d hdP hdpos
  have hRpos := kernelSlopeDenominatorClearingRamification_pos kernel P
  have hdleR : d kernel ≤
      kernelSlopeDenominatorClearingRamification kernel P :=
    Nat.le_of_dvd hRpos hdvd
  have hRle :
      kernelSlopeDenominatorClearingRamification kernel P ≤
        kernelSlopeDenominatorClearingRamification kernel P *
          adaptiveSourceCoefficientParameterOrder P d := by
    simpa using Nat.mul_le_mul_left
      (kernelSlopeDenominatorClearingRamification kernel P) horder
  unfold denominatorClearedCoefficientSlope
  exact Nat.div_pos (le_trans hdleR hRle) hdpos

/-- The saturated slope is attained by an actual active source monomial. -/
theorem exists_mem_activeKernelSupport_slope_eq_saturated
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    ∃ d ∈ activeKernelSupport kernel P,
      denominatorClearedCoefficientSlope kernel P d =
        saturatedKernelSlope kernel P hactive := by
  classical
  let S := activeKernelSupport kernel P
  let f := denominatorClearedCoefficientSlope kernel P
  have hS : S.Nonempty := activeKernelSupport_nonempty kernel P hactive
  have hmem : (S.image f).min' (hS.image f) ∈ S.image f :=
    Finset.min'_mem (S.image f) (hS.image f)
  rcases Finset.mem_image.mp hmem with ⟨d, hd, hmin⟩
  exact ⟨d, hd, hmin⟩

theorem saturatedKernelSlope_pos
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d kernel = 0) :
    0 < saturatedKernelSlope kernel P hactive := by
  rcases exists_mem_activeKernelSupport_slope_eq_saturated
      kernel P hactive with ⟨d, hd, heq⟩
  rw [← heq]
  exact denominatorClearedCoefficientSlope_pos kernel P hfree d hd

/-- The finite-minimum slope is coefficientwise integral after the common
denominator-clearing ramification. -/
theorem saturatedKernelSlope_divisibility_afterRamification
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    HasIntegralKernelCoefficientDivisibility
      kernel (saturatedKernelSlope kernel P hactive)
      (parameterRamificationFamily (K := K)
        (kernelSlopeDenominatorClearingRamification kernel P) P) := by
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  have horderDiv :
      HasParameterCoefficientDivisibility
        (adaptiveSourceCoefficientParameterOrder P) P := by
    intro d hd
    have hne := MvPolynomial.mem_support_iff.mp hd
    unfold adaptiveSourceCoefficientParameterOrder
    rw [dif_neg hne]
    exact polynomialParameterOrder_dvd _ hne
  have hram := parameterRamificationFamily_coefficientDivisibility
    (K := K) R (adaptiveSourceCoefficientParameterOrder P) P horderDiv
  intro d hdRam
  have hdP : d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom (K := K) R) P) hdRam
  by_cases hd0 : d kernel = 0
  · simp [kernelCoefficientTauPower, hd0]
  · have hdActive : d ∈ activeKernelSupport kernel P := by
      simp [activeKernelSupport, hdP, Nat.pos_of_ne_zero hd0]
    have hqle : q ≤ denominatorClearedCoefficientSlope kernel P d := by
      exact Finset.min'_le
        ((activeKernelSupport kernel P).image
          (denominatorClearedCoefficientSlope kernel P))
        (denominatorClearedCoefficientSlope kernel P d)
        (Finset.mem_image.mpr ⟨d, hdActive, rfl⟩)
    have hexp :
        q * d kernel ≤ R * adaptiveSourceCoefficientParameterOrder P d := by
      have hmul := Nat.mul_le_mul_right (d kernel) hqle
      unfold denominatorClearedCoefficientSlope at hmul
      exact le_trans hmul (Nat.div_mul_le_self _ _)
    have hpow :
        (Polynomial.X ^ (q * d kernel) : Polynomial K) ∣
          Polynomial.X ^ (R * adaptiveSourceCoefficientParameterOrder P d) :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) _ _ hexp
    unfold kernelCoefficientTauPower
    exact dvd_trans hpow (hram d hdRam)

set_option maxHeartbeats 800000 in
/-- **Saturated first contact is visible in the new special fibre.**

After denominator clearing, blowing up by the finite-minimum slope exposes
an actual monomial of positive kernel degree at parameter order zero.  This
is the discrete geometric progress that the under-spent unit restart lacked.
-/
theorem specialFiber_saturatedKernelBlowup_active
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    let R := kernelSlopeDenominatorClearingRamification kernel P
    let q := saturatedKernelSlope kernel P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) kernel P hactive
    ∃ d ∈ (polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)).support,
      0 < d kernel := by
  dsimp only
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  let Pram := parameterRamificationFamily (K := K) R P
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel P hactive
  rcases exists_mem_activeKernelSupport_slope_eq_saturated
      kernel P hactive with ⟨d, hdActive, hslope⟩
  have hdP : d ∈ P.support := by
    exact (Finset.mem_filter.mp hdActive).1
  have hdpos : 0 < d kernel := by
    exact (Finset.mem_filter.mp hdActive).2
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdP
  let nu := adaptiveSourceCoefficientParameterOrder P d
  have hnu :
      nu = polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
    simp [nu, adaptiveSourceCoefficientParameterOrder, hcoeffne]
  let primitive := polynomialParameterPrimitivePart
    (MvPolynomial.coeff d P) hcoeffne
  have hfactorOriginal :
      MvPolynomial.coeff d P = Polynomial.X ^ nu * primitive := by
    rw [hnu]
    exact polynomialParameterPrimitivePart_spec _ hcoeffne
  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos kernel P
  have hdvdR : d kernel ∣ R :=
    kernelExponent_dvd_denominatorClearingRamification
      kernel P d hdP hdpos
  have hdvdRnu : d kernel ∣ R * nu :=
    dvd_mul_of_dvd_left hdvdR nu
  have hqd : q * d kernel = R * nu := by
    calc
      q * d kernel =
          denominatorClearedCoefficientSlope kernel P d * d kernel := by
            rw [hslope]
      _ = (R * nu / d kernel) * d kernel := by
            rfl
      _ = R * nu := Nat.div_mul_cancel hdvdRnu
  have hdRam : d ∈ Pram.support := by
    apply MvPolynomial.mem_support_iff.mpr
    unfold Pram parameterRamificationFamily
    rw [MvPolynomial.coeff_map]
    apply parameterRamificationHom_ne_zero_of_pos R hRpos
    exact hcoeffne
  have hcoeffRam :
      MvPolynomial.coeff d Pram =
        Polynomial.X ^ (R * nu) *
          parameterRamificationHom (K := K) R primitive := by
    unfold Pram parameterRamificationFamily
    rw [MvPolynomial.coeff_map, hfactorOriginal, map_mul,
      parameterRamificationHom_X_pow]
  have hfactorBlow := kernelCoefficientQuotient_spec_of_mem
    kernel q Pram hdiv hdRam
  have hquotient :
      kernelCoefficientQuotient kernel q Pram hdiv d =
        parameterRamificationHom (K := K) R primitive := by
    apply mul_left_cancel₀
      (pow_ne_zero (q * d kernel) Polynomial.X_ne_zero)
    calc
      Polynomial.X ^ (q * d kernel) *
          kernelCoefficientQuotient kernel q Pram hdiv d =
        MvPolynomial.coeff d Pram := hfactorBlow.symm
      _ = Polynomial.X ^ (R * nu) *
          parameterRamificationHom (K := K) R primitive := hcoeffRam
      _ = Polynomial.X ^ (q * d kernel) *
          parameterRamificationHom (K := K) R primitive := by rw [hqd]
  have hprimitiveConst : Polynomial.constantCoeff primitive ≠ 0 := by
    unfold primitive
    exact polynomialParameterPrimitivePart_constantCoeff_ne_zero _ hcoeffne
  have hquotientConst :
      Polynomial.constantCoeff
          (kernelCoefficientQuotient kernel q Pram hdiv d) ≠ 0 := by
    rw [hquotient, constantCoeff_parameterRamificationHom R hRpos]
    exact hprimitiveConst
  refine ⟨d, ?_, hdpos⟩
  rw [MvPolynomial.mem_support_iff,
    coeff_polynomialFamilySpecialFiber,
    coeff_integralKernelBlowupFamily]
  rw [if_pos hdRam]
  exact hquotientConst

/-- The integral gate immediately yields the geometric collision and the
exact ramified kernel-defect clock.  The normalized natural-valued clock is
strictly smaller than the incoming defect.

This theorem deliberately packages the *same* ramification index `M` in all
three conclusions. -/
theorem adaptiveDegreeTwo_unmarkedKernelRestartData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (degreeCap M Delta : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d (3 : Fin 4) = 0)
    (hM : max 2 degreeCap < M)
    (hcollision :
      HasPolynomialFamilyExactGradientCollision P a b)
    (hdefect :
      HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    let Pram := parameterRamificationFamily (K := K) M P
    let aram := parameterRamificationSection (K := K) M a
    let bram := parameterRamificationSection (K := K) M b
    ∃ hdiv :
        HasIntegralKernelCoefficientDivisibility
          (3 : Fin 4) 1 Pram,
      HasPolynomialFamilyExactGradientCollision
        (integralKernelBlowupFamily (3 : Fin 4) 1 Pram hdiv)
        (kernelBlowupSection (3 : Fin 4) 1 aram)
        (kernelBlowupSection (3 : Fin 4) 1 bram) ∧
      HasPolynomialFamilyHessianDefect
        (K := K)
        (integralKernelBlowupFamily (3 : Fin 4) 1 Pram hdiv)
        (M * Delta - 2) ∧
      (M * Delta - 2) / M < Delta := by
  dsimp only
  let hdiv :
      HasIntegralKernelCoefficientDivisibility
        (3 : Fin 4) 1
        (parameterRamificationFamily (K := K) M P) :=
    parameterRamification_has_unmarkedKernelDivisibility
      (K := K) P degreeCap M hdegree hfree hM
  refine ⟨hdiv, ?_, ?_, ?_⟩
  · apply polynomialFamilyExactGradientCollision_integralKernelBlowup
    exact polynomialFamilyExactGradientCollision_parameterRamification
      M P a b hcollision
  · apply integralKernelBlowup_hasHessianDefect_sub
    exact parameterRamificationFamily_hasHessianDefect M Delta P hdefect
  · have hramDefect :
        HasPolynomialFamilyHessianDefect
          (K := K)
          (parameterRamificationFamily (K := K) M P)
          (M * Delta) :=
      parameterRamificationFamily_hasHessianDefect M Delta P hdefect
    have hcost : 2 ≤ M * Delta :=
      two_mul_slope_le_of_integralKernelBlowup
        (K := K) (3 : Fin 4) 1 (M * Delta)
        (parameterRamificationFamily (K := K) M P) hdiv hramDefect
    exact ScaledDefect.normalizedNat_ramified_sub_lt
      Delta M 2 (by omega) (by omega) hcost

/-! ## Scale-aware geometric successor -/

/-- Geometry-carrying adaptive state whose determinant order is recorded in
the parameter in which it is actually measured.  Its induction coordinate is
the natural quotient `rawDefect / scale`.

This deliberately coexists with the legacy unramified state while the global
dispatcher is migrated branch by branch. -/
structure ScaleAwareAdaptiveGeometricRestartState where
  rawDefect : ℕ
  scale : ℕ
  scale_pos : 0 < scale
  degreeCap : ℕ
  sourceComplexity : ℕ
  repair : RepairState
  family : MvPolynomial (Fin 4) (Polynomial K)
  movingSection : Fin 4 → Polynomial K
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K) family rawDefect
  nonlinearDegreeBound :
    NonlinearDegreeBound degreeCap family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (fun _ => (0 : Polynomial K)) movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Discrete outer induction coordinate of a scale-aware adaptive state. -/
def ScaleAwareAdaptiveGeometricRestartState.normalizedDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : ℕ :=
  s.rawDefect / s.scale

/-- Regard a legacy adaptive state as measured on the unramified scale. -/
def AdaptiveGeometricRestartState.toScaleAware
    (s : AdaptiveGeometricRestartState (K := K)) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := s.defect
  scale := 1
  scale_pos := by omega
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := s.repair
  family := s.family
  movingSection := s.movingSection
  hessianDefect := s.hessianDefect
  nonlinearDegreeBound := s.nonlinearDegreeBound
  exactCollision := s.exactCollision
  sectionSpecial := s.sectionSpecial

@[simp] theorem AdaptiveGeometricRestartState.toScaleAware_normalizedDefect
    (s : AdaptiveGeometricRestartState (K := K)) :
    s.toScaleAware.normalizedDefect = s.defect := by
  simp [AdaptiveGeometricRestartState.toScaleAware,
    ScaleAwareAdaptiveGeometricRestartState.normalizedDefect]

/-- Ramification by a positive index preserves the special point of a moving
polynomial section. -/
theorem polynomialSectionSpecialPoint_parameterRamificationSection
    (M : ℕ)
    (hM : 0 < M)
    (a : Fin 4 → Polynomial K) :
    polynomialSectionSpecialPoint
        (parameterRamificationSection (K := K) M a) =
      polynomialSectionSpecialPoint a := by
  funext i
  rw [show polynomialSectionSpecialPoint
      (parameterRamificationSection (K := K) M a) i =
        ((a i).comp (Polynomial.X ^ M)).coeff 0 by rfl]
  change ((a i).comp (Polynomial.X ^ M)).coeff 0 = (a i).coeff 0
  rw [Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, ← Polynomial.coeff_zero_eq_eval_zero]
  simp [hM.ne'.symm, ← Polynomial.coeff_zero_eq_eval_zero]

/-- **Adaptive degree-two strict successor.**

An unramified adaptive state whose special fibre is independent of the
unmarked coordinate `3` has a genuine scale-aware geometric successor.  The
successor retains the canonical marked pair, its exact raw clock is
`M * defect - 2` on scale `M`, and its normalized defect is strictly smaller.
-/
theorem AdaptiveGeometricRestartState.degreeTwoStrictSuccessor
    (s : AdaptiveGeometricRestartState (K := K))
    (M : ℕ)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d (3 : Fin 4) = 0)
    (hM : max 2 s.degreeCap < M) :
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = M * s.defect - 2 ∧
      t.scale = M ∧
      t.normalizedDefect < s.toScaleAware.normalizedDefect := by
  rcases adaptiveDegreeTwo_unmarkedKernelRestartData
      (K := K) s.family (fun _ => (0 : Polynomial K)) s.movingSection
      s.degreeCap M s.defect s.nonlinearDegreeBound hfree hM
      s.exactCollision s.hessianDefect with
    ⟨hdiv, hcollision, hdefect, hdrop⟩
  let Pram := parameterRamificationFamily (K := K) M s.family
  let aram := parameterRamificationSection (K := K) M
    (fun _ : Fin 4 => (0 : Polynomial K))
  let bram := parameterRamificationSection (K := K) M s.movingSection
  let Pnext := integralKernelBlowupFamily (3 : Fin 4) 1 Pram hdiv
  let bnext := kernelBlowupSection (3 : Fin 4) 1 bram
  have hMpos : 0 < M := by omega
  have haram : aram = (fun _ : Fin 4 => (0 : Polynomial K)) := by
    funext i
    simp [aram, parameterRamificationSection,
      parameterRamificationHom]
  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (fun _ : Fin 4 => (0 : Polynomial K)) bnext := by
    have hzeroBlow :
        kernelBlowupSection (3 : Fin 4) 1
            (parameterRamificationSection (K := K) M
              (fun _ : Fin 4 => (0 : Polynomial K))) =
          (fun _ : Fin 4 => (0 : Polynomial K)) := by
      funext i
      simp [kernelBlowupSection, parameterRamificationSection,
        parameterRamificationHom]
    rw [hzeroBlow] at hcollision
    simpa [Pnext, bnext, Pram, bram] using hcollision
  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram :=
    nonlinearDegreeBound_parameterRamification
      s.degreeCap M s.family s.nonlinearDegreeBound
  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext :=
    nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap 1 (3 : Fin 4) Pram hdegreeRam hdiv
  have hspecialRam :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      M hMpos s.movingSection]
    exact s.sectionSpecial
  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    by_cases hi : i = (3 : Fin 4)
    · subst i
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        (3 : Fin 4) (by omega) bram]
      simp [coordinateAxisPoint]
    · rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        (3 : Fin 4) 1 bram hi]
      exact congrFun hspecialRam i
  let t : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := M * s.defect - 2
      scale := M
      scale_pos := hMpos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefect
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollNext
      sectionSpecial := hspecialNext }
  refine ⟨t, rfl, rfl, ?_⟩
  dsimp [t, ScaleAwareAdaptiveGeometricRestartState.normalizedDefect,
    AdaptiveGeometricRestartState.toScaleAware]
  simpa using hdrop

/-- Dispatcher-facing degree-two restart.  Exact identification of the
special fibre with a quadratic Smith subface discharges the unmarked-kernel
support hypothesis internally. -/
theorem AdaptiveGeometricRestartState.degreeTwoStrictSuccessor_of_quadraticSmithSubface
    (s : AdaptiveGeometricRestartState (K := K))
    (M : ℕ)
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hspecial :
      polynomialFamilySpecialFiber s.family =
        smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hM : max 2 s.degreeCap < M) :
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = M * s.defect - 2 ∧
      t.scale = M ∧
      t.normalizedDefect < s.toScaleAware.normalizedDefect := by
  apply s.degreeTwoStrictSuccessor M
  · rw [hspecial]
    exact quadraticSmithSubface_free_three T F hquad
  · exact hM

/-- **Saturated adaptive degree-two first-contact stage.**

The denominator-cleared exact first kernel slope produces a genuine
geometry-carrying state whose special fibre has acquired `x₃`-support.  This
is a structural first-contact transition, so no quotient-clock decrease is
asserted or needed here. -/
theorem AdaptiveGeometricRestartState.degreeTwoSaturatedKernelStage
    (s : AdaptiveGeometricRestartState (K := K))
    (hactive : IsActiveKernelCoordinate (3 : Fin 4) s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d (3 : Fin 4) = 0) :
    let R := kernelSlopeDenominatorClearingRamification
      (3 : Fin 4) s.family
    let q := saturatedKernelSlope (3 : Fin 4) s.family hactive
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = R * s.defect - 2 * q ∧
      t.scale = R ∧
      0 < q ∧
      (∃ d ∈ (polynomialFamilySpecialFiber t.family).support,
        0 < d (3 : Fin 4)) := by
  dsimp only
  let R := kernelSlopeDenominatorClearingRamification
    (3 : Fin 4) s.family
  let q := saturatedKernelSlope (3 : Fin 4) s.family hactive
  let Pram := parameterRamificationFamily (K := K) R s.family
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) (3 : Fin 4) s.family hactive
  let Pnext := integralKernelBlowupFamily (3 : Fin 4) q Pram hdiv
  let bram := parameterRamificationSection (K := K) R s.movingSection
  let bnext := kernelBlowupSection (3 : Fin 4) q bram
  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos (3 : Fin 4) s.family
  have hqpos : 0 < q :=
    saturatedKernelSlope_pos (3 : Fin 4) s.family hactive hfree
  have hcollisionRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (fun _ : Fin 4 => (0 : Polynomial K))) bram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      R s.family (fun _ => (0 : Polynomial K)) s.movingSection
      s.exactCollision
  have hcollisionNextRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      (3 : Fin 4) q Pram hdiv
      (parameterRamificationSection (K := K) R
        (fun _ : Fin 4 => (0 : Polynomial K))) bram hcollisionRam
  have hzeroSection :
      kernelBlowupSection (3 : Fin 4) q
          (parameterRamificationSection (K := K) R
            (fun _ : Fin 4 => (0 : Polynomial K))) =
        (fun _ : Fin 4 => (0 : Polynomial K)) := by
    funext i
    simp [kernelBlowupSection, parameterRamificationSection,
      parameterRamificationHom]
  have hcollisionNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (fun _ : Fin 4 => (0 : Polynomial K)) bnext := by
    rw [hzeroSection] at hcollisionNextRaw
    simpa [Pnext, bnext] using hcollisionNextRaw
  have hdefRam :
      HasPolynomialFamilyHessianDefect (K := K) Pram (R * s.defect) :=
    parameterRamificationFamily_hasHessianDefect
      R s.defect s.family s.hessianDefect
  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (R * s.defect - 2 * q) :=
    integralKernelBlowup_hasHessianDefect_sub
      (3 : Fin 4) q (R * s.defect) Pram hdiv hdefRam
  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram :=
    nonlinearDegreeBound_parameterRamification
      s.degreeCap R s.family s.nonlinearDegreeBound
  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext :=
    nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q (3 : Fin 4) Pram hdegreeRam hdiv
  have hspecialRam :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos s.movingSection]
    exact s.sectionSpecial
  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    by_cases hi : i = (3 : Fin 4)
    · subst i
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        (3 : Fin 4) hqpos bram]
      simp [coordinateAxisPoint]
    · rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        (3 : Fin 4) q bram hi]
      exact congrFun hspecialRam i
  have hactiveNext :
      ∃ d ∈ (polynomialFamilySpecialFiber Pnext).support,
        0 < d (3 : Fin 4) := by
    simpa [Pnext, Pram, R, q, hdiv] using
      specialFiber_saturatedKernelBlowup_active
        (K := K) (3 : Fin 4) s.family hactive
  let t : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * s.defect - 2 * q
      scale := R
      scale_pos := hRpos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefNext
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollisionNext
      sectionSpecial := hspecialNext }
  exact ⟨t, rfl, rfl, hqpos, hactiveNext⟩

/-! ## Composition audit for the quotient clock -/

/-- A second ramified unit restart does **not** strictly decrease `Nat.div`
in complete generality.  This concrete equality is a regression test against
using `rawDefect / scale` as the final global measure without an additional
invariant. -/
theorem normalizedDefect_secondUnitRestart_counterexample :
    (3 * 3 - 2) / (3 * 2) = 3 / 2 := by
  decide

/-- Consequently, positivity and integrality of the second restart alone do
not imply strict quotient-clock descent. -/
theorem not_forall_secondUnitRestart_normalizedDefect_lt :
    ¬ (∀ raw scale M : ℕ,
      0 < scale →
      0 < M →
      2 ≤ M * raw →
      (M * raw - 2) / (M * scale) < raw / scale) := by
  intro h
  have hbad := h 3 2 3 (by omega) (by omega) (by omega)
  norm_num at hbad

/-- Exact divisibility of the incoming raw clock by its scale is a sufficient
condition for a subsequent positive ramified spend to decrease the quotient
clock.  The first degree-two successor generally does not preserve this
condition, which pinpoints the remaining global-state design problem. -/
theorem normalizedDefect_secondRestart_lt_of_exactScale
    (defect scale M cost : ℕ)
    (hscale : 0 < scale)
    (hM : 0 < M)
    (hcost : 0 < cost)
    (hle : cost ≤ (M * scale) * defect) :
    (M * (scale * defect) - cost) / (M * scale) <
      (scale * defect) / scale := by
  have hleft := ScaledDefect.normalizedNat_ramified_sub_lt
    defect (M * scale) cost (Nat.mul_pos hM hscale) hcost hle
  rw [← Nat.mul_assoc M scale defect,
    Nat.mul_div_right defect hscale]
  exact hleft

end

end HC4.Valuation
