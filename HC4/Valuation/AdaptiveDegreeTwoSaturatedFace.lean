import HC4.Valuation.AdaptiveDegreeTwoKernelRestart
import HC4.Valuation.CanonicalAdaptiveSmithWall

/-!
# Exact face of the saturated adaptive degree-two kernel stage
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Removing an `X`-power from an exact parameter-order factorisation leaves
a primitive quotient exactly when the removed power is the whole order. -/
theorem constantCoeff_ne_zero_of_exact_X_power_quotient_iff
    (a b : ℕ) (u v : Polynomial K) (hba : b ≤ a)
    (hu : Polynomial.constantCoeff u ≠ 0)
    (hfactor : Polynomial.X ^ b * v = Polynomial.X ^ a * u) :
    Polynomial.constantCoeff v ≠ 0 ↔ b = a := by
  have hv : v = Polynomial.X ^ (a - b) * u := by
    apply mul_left_cancel₀ (pow_ne_zero b Polynomial.X_ne_zero)
    calc
      Polynomial.X ^ b * v = Polynomial.X ^ a * u := hfactor
      _ = Polynomial.X ^ b * (Polynomial.X ^ (a - b) * u) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
  rw [hv]
  constructor
  · intro hconst
    by_contra hne
    have hab : 0 < a - b := Nat.sub_pos_of_lt (lt_of_le_of_ne hba hne)
    apply hconst
    change (Polynomial.X ^ (a - b) * u).coeff 0 = 0
    rw [← Polynomial.X_dvd_iff]
    simpa using dvd_mul_of_dvd_left
      (polynomial_X_pow_dvd_X_pow_of_le (K := K) 1 (a - b) hab) u
  · intro hEq
    subst a
    simpa using hu

/-- A source monomial survives in the saturated special fibre exactly when
its ramified exact coefficient order lies on the first kernel-contact wall. -/
theorem mem_specialFiber_saturatedKernelBlowup_iff
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (d : Fin 4 →₀ ℕ) :
    let R := kernelSlopeDenominatorClearingRamification kernel P
    let q := saturatedKernelSlope kernel P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) kernel P hactive
    d ∈ (polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)).support ↔
      d ∈ P.support ∧
        q * d kernel =
          R * adaptiveSourceCoefficientParameterOrder P d := by
  dsimp only
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  let Pram := parameterRamificationFamily (K := K) R P
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel P hactive
  by_cases hdP : d ∈ P.support
  · have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hdP
    let nu := adaptiveSourceCoefficientParameterOrder P d
    have hnu : nu = polynomialParameterOrder
        (MvPolynomial.coeff d P) hcoeffne := by
      simp [nu, adaptiveSourceCoefficientParameterOrder, hcoeffne]
    let primitive := polynomialParameterPrimitivePart
      (MvPolynomial.coeff d P) hcoeffne
    have hfactorOriginal :
        MvPolynomial.coeff d P = Polynomial.X ^ nu * primitive := by
      rw [hnu]
      exact polynomialParameterPrimitivePart_spec _ hcoeffne
    have hRpos : 0 < R :=
      kernelSlopeDenominatorClearingRamification_pos kernel P
    have hdRam : d ∈ Pram.support := by
      apply MvPolynomial.mem_support_iff.mpr
      unfold Pram parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      exact parameterRamificationHom_ne_zero_of_pos R hRpos hcoeffne
    have hcoeffRam : MvPolynomial.coeff d Pram =
        Polynomial.X ^ (R * nu) *
          parameterRamificationHom (K := K) R primitive := by
      unfold Pram parameterRamificationFamily
      rw [MvPolynomial.coeff_map, hfactorOriginal, map_mul,
        parameterRamificationHom_X_pow]
    have hba : q * d kernel ≤ R * nu := by
      by_cases hd0 : d kernel = 0
      · simp [hd0]
      · have hdActive : d ∈ activeKernelSupport kernel P :=
          Finset.mem_filter.mpr ⟨hdP, Nat.pos_of_ne_zero hd0⟩
        have hqle : q ≤ denominatorClearedCoefficientSlope kernel P d :=
          Finset.min'_le
            ((activeKernelSupport kernel P).image
              (denominatorClearedCoefficientSlope kernel P))
            (denominatorClearedCoefficientSlope kernel P d)
            (Finset.mem_image.mpr ⟨d, hdActive, rfl⟩)
        have hmul := Nat.mul_le_mul_right (d kernel) hqle
        unfold denominatorClearedCoefficientSlope at hmul
        exact le_trans hmul (Nat.div_mul_le_self _ _)
    have hfactorBlow := kernelCoefficientQuotient_spec_of_mem
      kernel q Pram hdiv hdRam
    have hprimitiveConst : Polynomial.constantCoeff
        (parameterRamificationHom (K := K) R primitive) ≠ 0 := by
      rw [constantCoeff_parameterRamificationHom R hRpos]
      exact polynomialParameterPrimitivePart_constantCoeff_ne_zero _ hcoeffne
    have hconstant : Polynomial.constantCoeff
          (kernelCoefficientQuotient kernel q Pram hdiv d) ≠ 0 ↔
        q * d kernel = R * nu := by
      apply constantCoeff_ne_zero_of_exact_X_power_quotient_iff
        (a := R * nu) (b := q * d kernel)
        (u := parameterRamificationHom (K := K) R primitive)
        (v := kernelCoefficientQuotient kernel q Pram hdiv d)
        hba hprimitiveConst
      exact hfactorBlow.symm.trans hcoeffRam
    rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber,
      coeff_integralKernelBlowupFamily, if_pos hdRam]
    simpa [hdP, nu] using hconstant
  · have hdRam : d ∉ Pram.support := by
      intro hd
      exact hdP ((MvPolynomial.support_map_subset
        (parameterRamificationHom (K := K) R) P) hd)
    rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber,
      coeff_integralKernelBlowupFamily, if_neg hdRam]
    simp [hdP]

/-- Exact coefficient formula for the saturated first-contact face.  A source
coefficient contributes its primitive constant coefficient precisely on the
attained wall `q * d(kernel) = R * ν_d`; every other coefficient vanishes. -/
theorem coeff_specialFiber_saturatedKernelBlowup
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (d : Fin 4 →₀ ℕ) :
    let R := kernelSlopeDenominatorClearingRamification kernel P
    let q := saturatedKernelSlope kernel P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) kernel P hactive
    MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily kernel q Pram hdiv)) =
      if hd : d ∈ P.support then
        if q * d kernel =
            R * adaptiveSourceCoefficientParameterOrder P d then
          Polynomial.constantCoeff
            (adaptiveSourceCoefficientPrimitivePart P d)
        else 0
      else 0 := by
  dsimp only
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  let Pram := parameterRamificationFamily (K := K) R P
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel P hactive
  by_cases hdP : d ∈ P.support
  · have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hdP
    let nu := adaptiveSourceCoefficientParameterOrder P d
    let primitive := adaptiveSourceCoefficientPrimitivePart P d
    have hfactorOriginal :
        MvPolynomial.coeff d P = Polynomial.X ^ nu * primitive := by
      exact adaptiveSourceCoefficient_exactFactorization P hdP
    have hRpos : 0 < R :=
      kernelSlopeDenominatorClearingRamification_pos kernel P
    have hdRam : d ∈ Pram.support := by
      apply MvPolynomial.mem_support_iff.mpr
      unfold Pram parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      exact parameterRamificationHom_ne_zero_of_pos R hRpos hcoeffne
    have hcoeffRam : MvPolynomial.coeff d Pram =
        Polynomial.X ^ (R * nu) *
          parameterRamificationHom (K := K) R primitive := by
      unfold Pram parameterRamificationFamily
      rw [MvPolynomial.coeff_map, hfactorOriginal, map_mul,
        parameterRamificationHom_X_pow]
    have hba : q * d kernel ≤ R * nu := by
      by_cases hd0 : d kernel = 0
      · simp [hd0]
      · have hdActive : d ∈ activeKernelSupport kernel P :=
          Finset.mem_filter.mpr ⟨hdP, Nat.pos_of_ne_zero hd0⟩
        have hqle : q ≤ denominatorClearedCoefficientSlope kernel P d :=
          Finset.min'_le
            ((activeKernelSupport kernel P).image
              (denominatorClearedCoefficientSlope kernel P))
            (denominatorClearedCoefficientSlope kernel P d)
            (Finset.mem_image.mpr ⟨d, hdActive, rfl⟩)
        have hmul := Nat.mul_le_mul_right (d kernel) hqle
        unfold denominatorClearedCoefficientSlope at hmul
        exact le_trans hmul (Nat.div_mul_le_self _ _)
    have hfactorBlow := kernelCoefficientQuotient_spec_of_mem
      kernel q Pram hdiv hdRam
    rw [coeff_polynomialFamilySpecialFiber,
      coeff_integralKernelBlowupFamily, if_pos hdRam, dif_pos hdP]
    by_cases hcontact : q * d kernel = R * nu
    · rw [if_pos hcontact]
      have hv : kernelCoefficientQuotient kernel q Pram hdiv d =
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
              parameterRamificationHom (K := K) R primitive := by rw [hcontact]
      rw [hv, constantCoeff_parameterRamificationHom R hRpos]
    · rw [if_neg hcontact]
      have hlt : q * d kernel < R * nu := lt_of_le_of_ne hba hcontact
      have hdvd : Polynomial.X ∣
          kernelCoefficientQuotient kernel q Pram hdiv d := by
        have hpow : Polynomial.X ^ (R * nu - q * d kernel) ∣
            kernelCoefficientQuotient kernel q Pram hdiv d := by
          refine ⟨parameterRamificationHom (K := K) R primitive, ?_⟩
          apply mul_left_cancel₀
            (pow_ne_zero (q * d kernel) Polynomial.X_ne_zero)
          calc
            Polynomial.X ^ (q * d kernel) *
                kernelCoefficientQuotient kernel q Pram hdiv d =
                MvPolynomial.coeff d Pram := hfactorBlow.symm
            _ = Polynomial.X ^ (R * nu) *
                parameterRamificationHom (K := K) R primitive := hcoeffRam
            _ = Polynomial.X ^ (q * d kernel) *
                (Polynomial.X ^ (R * nu - q * d kernel) *
                  parameterRamificationHom (K := K) R primitive) := by
                    rw [← mul_assoc, ← pow_add]
                    congr 2
                    omega
        have hXpow : Polynomial.X ∣
            (Polynomial.X : Polynomial K) ^ (R * nu - q * d kernel) := by
          refine ⟨Polynomial.X ^ (R * nu - q * d kernel - 1), ?_⟩
          rw [← pow_succ']
          congr 1
          omega
        exact dvd_trans hXpow hpow
      change (kernelCoefficientQuotient kernel q Pram hdiv d).coeff 0 = 0
      exact Polynomial.X_dvd_iff.mp hdvd
  · have hdRam : d ∉ Pram.support := by
      intro hd
      exact hdP ((MvPolynomial.support_map_subset
        (parameterRamificationHom (K := K) R) P) hd)
    simp only [dif_neg hdP]
    rw [coeff_polynomialFamilySpecialFiber,
      coeff_integralKernelBlowupFamily, if_neg hdRam]
    rfl

/-- The explicit associated-graded polynomial on the saturated kernel wall. -/
noncomputable def saturatedKernelFirstContactFace
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    MvPolynomial (Fin 4) K :=
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  ∑ d ∈ P.support.filter fun d =>
      q * d kernel = R * adaptiveSourceCoefficientParameterOrder P d,
    MvPolynomial.monomial d
      (Polynomial.constantCoeff
        (adaptiveSourceCoefficientPrimitivePart P d))

/-- The saturated blow-up special fibre is exactly the explicit first-contact
face, including its primitive leading coefficients. -/
theorem specialFiber_saturatedKernelBlowup_eq_firstContactFace
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    let R := kernelSlopeDenominatorClearingRamification kernel P
    let q := saturatedKernelSlope kernel P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) kernel P hactive
    polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv) =
      saturatedKernelFirstContactFace kernel P hactive := by
  dsimp only
  ext d
  rw [coeff_specialFiber_saturatedKernelBlowup kernel P hactive d]
  classical
  by_cases hdP : d ∈ P.support
  · by_cases hcontact :
        saturatedKernelSlope kernel P hactive * d kernel =
          kernelSlopeDenominatorClearingRamification kernel P *
            adaptiveSourceCoefficientParameterOrder P d
    · simp [saturatedKernelFirstContactFace, hdP, hcontact,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    · simp [saturatedKernelFirstContactFace, hdP, hcontact,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  · simp [saturatedKernelFirstContactFace, hdP,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

/-- Saturated first contact is visible to the ordinary Smith classifier: its
projected support contains a point with positive third transverse exponent.
Consequently the transformed special fibre cannot still be supported on the
old quadratic Smith face, whose third transverse exponent is identically
zero. -/
theorem exists_projectedSupport_third_pos_saturatedKernelBlowup
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate (3 : Fin 4) P) :
    let R := kernelSlopeDenominatorClearingRamification (3 : Fin 4) P
    let q := saturatedKernelSlope (3 : Fin 4) P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) P hactive
    let Fnext := polynomialFamilySpecialFiber
      (integralKernelBlowupFamily (3 : Fin 4) q Pram hdiv)
    ∃ e ∈ HC4.Newton.smithProjectedSupport (1 : Fin 4) 2 3 Fnext,
      0 < e.d := by
  dsimp only
  let R := kernelSlopeDenominatorClearingRamification (3 : Fin 4) P
  let q := saturatedKernelSlope (3 : Fin 4) P hactive
  let Pram := parameterRamificationFamily (K := K) R P
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) (3 : Fin 4) P hactive
  let Fnext := polynomialFamilySpecialFiber
    (integralKernelBlowupFamily (3 : Fin 4) q Pram hdiv)
  rcases specialFiber_saturatedKernelBlowup_active
      (K := K) (3 : Fin 4) P hactive with ⟨d, hd, hd3⟩
  refine ⟨HC4.Newton.smithSupportExponentOf (1 : Fin 4) 2 3 d, ?_, ?_⟩
  · unfold HC4.Newton.smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  · simpa [HC4.Newton.smithSupportExponentOf_d] using hd3

/-- The saturated face cannot immediately reproduce the three-pattern
quadratic Smith stratum that triggered the degree-two transition. -/
theorem not_quadraticSmithPatterns_saturatedKernelBlowup
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate (3 : Fin 4) P) :
    let R := kernelSlopeDenominatorClearingRamification (3 : Fin 4) P
    let q := saturatedKernelSlope (3 : Fin 4) P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) P hactive
    let Fnext := polynomialFamilySpecialFiber
      (integralKernelBlowupFamily (3 : Fin 4) q Pram hdiv)
    ¬ (∀ e ∈ HC4.Newton.smithProjectedSupport (1 : Fin 4) 2 3 Fnext,
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) := by
  dsimp only
  intro hquad
  rcases exists_projectedSupport_third_pos_saturatedKernelBlowup
      (K := K) P hactive with ⟨e, he, hed⟩
  rcases hquad e he with h | h | h <;> omega

/-- The saturated degree-two face automatically re-enters the canonical
Smith dispatcher.  No new scalar wall is chosen by the caller: either the
constant-zero realizable wall is symmetrically minimal, or the fixed Smith
separator gives the existing strict-improvement branch. -/
theorem saturatedKernelBlowup_canonicalWall_or_strictImprovement
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate (3 : Fin 4) P) :
    let R := kernelSlopeDenominatorClearingRamification (3 : Fin 4) P
    let q := saturatedKernelSlope (3 : Fin 4) P hactive
    let Pram := parameterRamificationFamily (K := K) R P
    let hdiv := saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) P hactive
    let Fnext := polynomialFamilySpecialFiber
      (integralKernelBlowupFamily (3 : Fin 4) q Pram hdiv)
    CanonicalAdaptiveSmithWallData Fnext ∨
      HC4.Newton.HasStrictSymmetricSmithImprovement
        (HC4.Newton.smithProjectedSupport (1 : Fin 4) 2 3 Fnext)
        0 (fun _ => (0 : ℤ)) := by
  dsimp only
  apply canonicalAdaptiveSmithWall_or_strictImprovement
  rcases exists_projectedSupport_third_pos_saturatedKernelBlowup
      (K := K) P hactive with ⟨e, he, _hed⟩
  exact ⟨e, he⟩

end

end HC4.Valuation
