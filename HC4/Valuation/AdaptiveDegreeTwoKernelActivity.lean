import HC4.Valuation.AdaptiveDegreeTwoKernelRestart

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Coefficient formula for partial differentiation over an arbitrary
commutative semiring; unlike the legacy chart lemma, this applies to
polynomial-valued family coefficients. -/
theorem coeff_pderiv_commSemiring
    {R : Type*} [CommSemiring R]
    {σ : Type*} [DecidableEq σ]
    (i : σ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv i F) =
      MvPolynomial.coeff (m + Finsupp.single i 1) F *
        ((m i + 1 : ℕ) : R) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ, add_mul]
  | monomial n a =>
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : n = m + Finsupp.single i 1
      · simp [h]
      · simp only [h, if_false, zero_mul]
        by_cases hn : n i = 0
        · simp [hn]
        · apply if_neg
          have hle : Finsupp.single i 1 ≤ n := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr hn
          intro hsub
          apply h
          exact (tsub_eq_iff_eq_add_of_le hle).mp hsub

/-- Absence of active support in one coordinate kills its first derivative. -/
theorem pderiv_eq_zero_of_no_activeSupport
    (kernel : Fin 4) (P : MvPolynomial (Fin 4) (Polynomial K))
    (hnot : ¬ ∃ d ∈ P.support, 0 < d kernel) :
    MvPolynomial.pderiv kernel P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_pderiv_commSemiring]
  let dPlus : Fin 4 →₀ ℕ := d + Finsupp.single kernel 1
  have hdPlusApply : dPlus kernel = d kernel + 1 := by
    simp [dPlus]
  have hcoeff : MvPolynomial.coeff dPlus P = 0 := by
    by_contra hne
    apply hnot
    exact ⟨dPlus, MvPolynomial.mem_support_iff.mpr hne, by
      rw [hdPlusApply]
      omega⟩
  simpa [dPlus, hcoeff]

/-- A zero first derivative supplies a zero Hessian row. -/
theorem hessianDeterminant_eq_zero_of_pderiv_eq_zero
    (kernel : Fin 4) (P : MvPolynomial (Fin 4) (Polynomial K))
    (hderiv : MvPolynomial.pderiv kernel P = 0) :
    HC4.Polynomial.hessianDeterminant P = 0 := by
  unfold HC4.Polynomial.hessianDeterminant
  apply Matrix.det_eq_zero_of_row_eq_zero kernel
  intro j
  simp [HC4.Polynomial.hessian_apply, hderiv]

/-- A nonzero pure Hessian clock forces every source coordinate to occur. -/
theorem exists_kernelDependentSupport_of_hessianDefect
    (kernel : Fin 4) (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    ∃ d ∈ P.support, 0 < d kernel := by
  by_contra hnot
  have hderiv : MvPolynomial.pderiv kernel P = 0 :=
    pderiv_eq_zero_of_no_activeSupport kernel P hnot
  have hdetzero : HC4.Polynomial.hessianDeterminant P = 0 :=
    hessianDeterminant_eq_zero_of_pderiv_eq_zero kernel P hderiv
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdetzero] at hdef
  exact (MvPolynomial.C_ne_zero.mpr
    (pow_ne_zero Delta Polynomial.X_ne_zero)) hdef.symm

/-- Dispatcher-facing saturated stage.  Hessian activity and quadratic-face
kernel freeness are discharged internally. -/
theorem AdaptiveGeometricRestartState.degreeTwoSaturatedKernelStage_of_quadraticSmithSubface
    (s : AdaptiveGeometricRestartState (K := K))
    (T : Finset SmithSupportExponent) (F : MvPolynomial (Fin 4) K)
    (hspecial : polynomialFamilySpecialFiber s.family =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad : ∀ e ∈ T,
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    let hactive := exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) s.family s.defect s.hessianDefect
    let R := kernelSlopeDenominatorClearingRamification (3 : Fin 4) s.family
    let q := saturatedKernelSlope (3 : Fin 4) s.family hactive
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = R * s.defect - 2 * q ∧ t.scale = R ∧ 0 < q ∧
      (∃ d ∈ (polynomialFamilySpecialFiber t.family).support,
        0 < d (3 : Fin 4)) := by
  dsimp only
  let hactive := exists_kernelDependentSupport_of_hessianDefect
    (K := K) (3 : Fin 4) s.family s.defect s.hessianDefect
  apply s.degreeTwoSaturatedKernelStage hactive
  rw [hspecial]
  exact quadraticSmithSubface_free_three T F hquad

end


end HC4.Valuation
