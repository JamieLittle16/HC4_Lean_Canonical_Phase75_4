import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyTransverseEquation
import Mathlib.Tactic

/-!
# Identifying the cancelled first-key profiles with transverse derivatives

Stage 4B12 cancels the common longitudinal monomial from the maximal
homogeneous first-key kernel and leaves the exact coefficient-ring system

    mixedProfile_i * A + sum_j transverseHessianProfile_ij * B_j = 0.

This file identifies those coefficient profiles with the ordinary transverse
derivatives of the pure transverse source profile `H` in

    R = x₀^e H.

No new polynomial representation is introduced.  The proof uses only the
existing `finSuccEquiv_coeff_coeff` coefficient formula and HC4's existing
`coeff_pderiv_mixedDegree` derivative formula.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## `finSuccEquiv` coefficient compatibility with differentiation -/

/-- Taking a fixed longitudinal coefficient under `finSuccEquiv` commutes
exactly with differentiation in a transverse source variable. -/
theorem finSuccEquiv_coeff_pderiv_succ
    (F : MvPolynomial (Fin 4) K)
    (a : ℕ)
    (j : Fin 3) :
    (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.pderiv j.succ F)).coeff a =
      MvPolynomial.pderiv j ((MvPolynomial.finSuccEquiv K 3 F).coeff a) := by
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff m
    (MvPolynomial.pderiv j.succ F) a]
  rw [coeff_pderiv_mixedDegree (K := K) j.succ F (m.cons a)]
  rw [coeff_pderiv_mixedDegree (K := K) j
    ((MvPolynomial.finSuccEquiv K 3 F).coeff a) m]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff
    (m + Finsupp.single j 1) F a]
  have hexponent :
      m.cons a + Finsupp.single j.succ 1 =
        (m + Finsupp.single j 1).cons a := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · by_cases hjk : j = k
      · subst k
        simp
      · simp [hjk]
  rw [hexponent]
  simp

/-- If every monomial of `F` has longitudinal exponent `n`, then the
`(n-1)` coefficient of its longitudinal derivative is exactly `n` times the
`n` coefficient of `F`.  The `n=0` branch is included: then the derivative
is identically zero. -/
theorem finSuccEquiv_coeff_pderiv_zero_of_longitudinalExponent
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n) :
    (MvPolynomial.finSuccEquiv K 3
        (MvPolynomial.pderiv (0 : Fin 4) F)).coeff (n - 1) =
      MvPolynomial.C (n : K) *
        (MvPolynomial.finSuccEquiv K 3 F).coeff n := by
  by_cases hn : n = 0
  · subst n
    have hzero : MvPolynomial.pderiv (0 : Fin 4) F = 0 := by
      ext d
      simp only [MvPolynomial.coeff_zero]
      by_contra hd
      have hrel :=
        pderiv_zero_longitudinalExponent_succ F 0 hlong d hd
      omega
    rw [hzero]
    simp
  · ext m
    rw [MvPolynomial.finSuccEquiv_coeff_coeff m
      (MvPolynomial.pderiv (0 : Fin 4) F) (n - 1)]
    rw [coeff_pderiv_mixedDegree (K := K) (0 : Fin 4) F (m.cons (n - 1))]
    rw [MvPolynomial.coeff_C_mul]
    rw [MvPolynomial.finSuccEquiv_coeff_coeff m F n]
    have hexponent :
        m.cons (n - 1) + Finsupp.single (0 : Fin 4) 1 =
          m.cons n := by
      ext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp
        omega
      · simp
    rw [hexponent]
    have hpred : n - 1 + 1 = n := by omega
    simp [hpred, mul_comm]

/-! ## Identification of the B12 profiles -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The transverse-transverse B12 Hessian profile is literally the Hessian
of the pure transverse source profile `H`. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseHessianProfile_eq
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (i j : Fin 3) :
    D.transverseHessianProfile i j =
      HC4.Polynomial.hessian D.transverseSourceProfile i j := by
  simp only [FirstKeyCanonicalMaximalHomogeneousKernelData.transverseHessianProfile,
    FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile,
    HC4.Polynomial.hessian_apply]
  rw [finSuccEquiv_coeff_pderiv_succ]
  rw [finSuccEquiv_coeff_pderiv_succ]

/-- The mixed B12 Hessian profile is exactly

    e * ∂ᵢ H,

where `e` is the common longitudinal exponent of the maximal homogeneous
source slice. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.mixedProfile_eq
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (i : Fin 3) :
    D.mixedProfile i =
      MvPolynomial.C (D.sourceExponent : K) *
        MvPolynomial.pderiv i D.transverseSourceProfile := by
  let R := D.sliceData.sliceData.slice
  let e := D.sourceExponent
  have hRlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d R ≠ 0 → d (0 : Fin 4) = e := by
    intro d hd
    simpa [R, e, FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent]
      using D.sliceData.sliceData.slice_longitudinalExponent d hd
  have hiLong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d (MvPolynomial.pderiv i.succ R) ≠ 0 →
          d (0 : Fin 4) = e :=
    pderiv_succ_preserves_longitudinalExponent R e hRlong i
  change
    (MvPolynomial.finSuccEquiv K 3
      (MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv i.succ R))).coeff (e - 1) =
      MvPolynomial.C (e : K) *
        MvPolynomial.pderiv i
          ((MvPolynomial.finSuccEquiv K 3 R).coeff e)
  rw [finSuccEquiv_coeff_pderiv_zero_of_longitudinalExponent
    (MvPolynomial.pderiv i.succ R) e hiLong]
  rw [finSuccEquiv_coeff_pderiv_succ]

/-- **Stage 4B13 transverse derivative form.**

After the longitudinal cancellation of B12, the kernel equation is literally

    e * (∂ᵢ H) * A + sum_j (∂ᵢ∂ⱼ H) * B_j = 0

for each transverse row. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDerivativeEquation
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (i : Fin 3) :
    (MvPolynomial.C (D.sourceExponent : K) *
        MvPolynomial.pderiv i D.transverseSourceProfile) *
          F.longitudinalProfile +
        ∑ j : Fin 3,
          HC4.Polynomial.hessian D.transverseSourceProfile i j *
            F.transverseProfile j = 0 := by
  have h := D.transverseProfileEquation F i
  rw [D.mixedProfile_eq i] at h
  have hH :
      ∀ j : Fin 3,
        D.transverseHessianProfile i j =
          HC4.Polynomial.hessian D.transverseSourceProfile i j := by
    intro j
    exact D.transverseHessianProfile_eq i j
  simpa only [hH] using h

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
