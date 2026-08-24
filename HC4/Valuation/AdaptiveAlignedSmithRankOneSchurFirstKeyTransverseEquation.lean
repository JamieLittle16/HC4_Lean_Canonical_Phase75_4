import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLongitudinalCancellationInterface
import Mathlib.Tactic

/-!
# Cancelling the common longitudinal monomial in the first-key kernel

Stage 4B11 gives exact outer-polynomial factorizations under
`MvPolynomial.finSuccEquiv`:

    R      = X^e H,
    U_0    = X^(lambda+1) A,
    U_{j+1}= X^lambda B_j.

The B9 transverse Hessian rows therefore have one common outer power.  This
file performs that cancellation without introducing a second three-variable
polynomial model.  We keep the transverse profiles as the actual coefficients
of `finSuccEquiv` and prove the resulting equation directly in
`MvPolynomial (Fin 3) K`.

The only generic bookkeeping added here is the exact behaviour of a fixed
longitudinal support exponent under formal partial differentiation.  All
source-key, homogeneous-slice, kernel, and monomial-factor data are reused
from B3--B11.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Fixed longitudinal exponent under differentiation -/

/-- A transverse partial derivative preserves a fixed exponent in source
coordinate `0`. -/
theorem pderiv_succ_preserves_longitudinalExponent
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n)
    (j : Fin 3) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d (MvPolynomial.pderiv j.succ F) ≠ 0 →
        d (0 : Fin 4) = n := by
  intro d hd
  have hsource :
      MvPolynomial.coeff (d + Finsupp.single j.succ 1) F ≠ 0 := by
    intro hz
    have hcoeff := coeff_pderiv_mixedDegree j.succ F d
    rw [hz] at hcoeff
    simp only [zero_mul] at hcoeff
    exact hd hcoeff
  have h := hlong (d + Finsupp.single j.succ 1) hsource
  simpa using h

/-- A longitudinal partial derivative lowers a fixed positive longitudinal
exponent by exactly one; before positivity is used we record the safer
successor equation. -/
theorem pderiv_zero_longitudinalExponent_succ
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d (MvPolynomial.pderiv (0 : Fin 4) F) ≠ 0 →
        d (0 : Fin 4) + 1 = n := by
  intro d hd
  have hsource :
      MvPolynomial.coeff (d + Finsupp.single (0 : Fin 4) 1) F ≠ 0 := by
    intro hz
    have hcoeff := coeff_pderiv_mixedDegree (0 : Fin 4) F d
    rw [hz] at hcoeff
    simp only [zero_mul] at hcoeff
    exact hd hcoeff
  have h := hlong (d + Finsupp.single (0 : Fin 4) 1) hsource
  simpa using h

/-- A transverse-transverse Hessian entry of a fixed-longitudinal-exponent
source polynomial has the same longitudinal exponent. -/
theorem hessian_succ_succ_preserves_longitudinalExponent
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n)
    (i j : Fin 3) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d (HC4.Polynomial.hessian F i.succ j.succ) ≠ 0 →
        d (0 : Fin 4) = n := by
  have hi := pderiv_succ_preserves_longitudinalExponent F n hlong i
  simpa [HC4.Polynomial.hessian_apply] using
    (pderiv_succ_preserves_longitudinalExponent
      (MvPolynomial.pderiv i.succ F) n hi j)

/-- A mixed transverse/longitudinal Hessian entry satisfies the expected
one-step longitudinal exponent relation. -/
theorem hessian_succ_zero_longitudinalExponent_succ
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n)
    (i : Fin 3) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d (HC4.Polynomial.hessian F i.succ (0 : Fin 4)) ≠ 0 →
        d (0 : Fin 4) + 1 = n := by
  have hi := pderiv_succ_preserves_longitudinalExponent F n hlong i
  simpa [HC4.Polynomial.hessian_apply] using
    (pderiv_zero_longitudinalExponent_succ
      (MvPolynomial.pderiv i.succ F) n hi)

/-- Exact `finSuccEquiv` monomial factor of every transverse-transverse
Hessian entry. -/
theorem finSuccEquiv_hessian_succ_succ_eq_monomial
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n)
    (i j : Fin 3) :
    MvPolynomial.finSuccEquiv K 3
        (HC4.Polynomial.hessian F i.succ j.succ) =
      Polynomial.monomial n
        ((MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian F i.succ j.succ)).coeff n) := by
  exact finSuccEquiv_eq_monomial_of_longitudinalExponent
    (HC4.Polynomial.hessian F i.succ j.succ) n
    (hessian_succ_succ_preserves_longitudinalExponent F n hlong i j)

/-- Exact mixed-Hessian factor.  At longitudinal exponent zero the mixed
entry is identically zero; otherwise its exponent is `n-1`. -/
theorem finSuccEquiv_hessian_succ_zero_eq_monomial
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ)
    (hlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d F ≠ 0 → d (0 : Fin 4) = n)
    (i : Fin 3) :
    MvPolynomial.finSuccEquiv K 3
        (HC4.Polynomial.hessian F i.succ (0 : Fin 4)) =
      Polynomial.monomial (n - 1)
        ((MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian F i.succ (0 : Fin 4))).coeff (n - 1)) := by
  by_cases hn : n = 0
  · subst n
    have hzero : HC4.Polynomial.hessian F i.succ (0 : Fin 4) = 0 := by
      ext d
      simp only [MvPolynomial.coeff_zero]
      by_contra hd
      have hrel :=
        hessian_succ_zero_longitudinalExponent_succ F 0 hlong i d hd
      omega
    rw [hzero]
    simp
  · apply finSuccEquiv_eq_monomial_of_longitudinalExponent
    intro d hd
    have hrel :=
      hessian_succ_zero_longitudinalExponent_succ F n hlong i d hd
    omega

/-! ## The pure transverse coefficient equation -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Longitudinal exponent of the maximal homogeneous first-key slice. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) : ℕ :=
  D.sliceData.sliceData.ordinaryDegree -
    firstPositiveTransverseSourceDegree
      (polynomialFamilySpecialFiber C.family) L.hpos

/-- Pure transverse source profile `H` in `R = X^e H`. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice).coeff
    D.sourceExponent

/-- Pure transverse profile of the longitudinal kernel coordinate. -/
noncomputable def FirstKeyMaximalVectorLongitudinalFactorData.longitudinalProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (L.maximalHomogeneousVector (0 : Fin 4))).coeff (F.exponent + 1)

/-- Pure transverse profile of a transverse kernel coordinate. -/
noncomputable def FirstKeyMaximalVectorLongitudinalFactorData.transverseProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (j : Fin 3) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (L.maximalHomogeneousVector j.succ)).coeff F.exponent

/-- Pure transverse coefficient of the mixed source Hessian entry. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.mixedProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (i : Fin 3) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (HC4.Polynomial.hessian D.sliceData.sliceData.slice
      i.succ (0 : Fin 4))).coeff (D.sourceExponent - 1)

/-- Pure transverse coefficient matrix of the transverse-transverse Hessian. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.transverseHessianProfile
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (i j : Fin 3) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (HC4.Polynomial.hessian D.sliceData.sliceData.slice
      i.succ j.succ)).coeff D.sourceExponent

/-- **Stage 4B12 longitudinal cancellation.**

In the branch where a transverse coordinate of the canonical homogeneous
kernel survives, the three B9 Hessian rows descend exactly to a system over
the transverse coefficient ring.  No `x₀` remains:

    mixed_i * A + sum_j transverseHessian_ij * B_j = 0.

The mixed profile is automatically zero when the source exponent is zero. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseProfileEquation
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (i : Fin 3) :
    D.mixedProfile i * F.longitudinalProfile +
        ∑ j : Fin 3,
          D.transverseHessianProfile i j * F.transverseProfile j = 0 := by
  let R := D.sliceData.sliceData.slice
  let e := D.sourceExponent
  let lambda := F.exponent
  let U := L.maximalHomogeneousVector

  have hRlong :
      ∀ d : Fin 4 →₀ ℕ,
        MvPolynomial.coeff d R ≠ 0 → d (0 : Fin 4) = e := by
    intro d hd
    simpa [R, e, FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent]
      using D.sliceData.sliceData.slice_longitudinalExponent d hd

  have hrow :
      ∑ j : Fin 4,
        HC4.Polynomial.hessian R i.succ j * U j = 0 := by
    simpa [R, U, Matrix.mulVec, dotProduct] using D.transverseKernel i

  have hrowPoly :
      ∑ j : Fin 4,
          MvPolynomial.finSuccEquiv K 3 (HC4.Polynomial.hessian R i.succ j) *
            MvPolynomial.finSuccEquiv K 3 (U j) = 0 := by
    have hmap := congrArg (MvPolynomial.finSuccEquiv K 3) hrow
    simpa only [map_sum, map_mul, map_zero] using hmap

  have htransH :
      ∀ j : Fin 3,
        MvPolynomial.finSuccEquiv K 3
            (HC4.Polynomial.hessian R i.succ j.succ) =
          Polynomial.monomial e
            ((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) := by
    intro j
    exact finSuccEquiv_hessian_succ_succ_eq_monomial R e hRlong i j

  have hmixedH :
      MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian R i.succ (0 : Fin 4)) =
        Polynomial.monomial (e - 1)
          ((MvPolynomial.finSuccEquiv K 3
            (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) := by
    exact finSuccEquiv_hessian_succ_zero_eq_monomial R e hRlong i

  have hrowSplit := hrowPoly
  rw [Fin.sum_univ_succ] at hrowSplit
  rw [hmixedH, F.longitudinalFactor] at hrowSplit
  have htransSum :
      (∑ j : Fin 3,
          MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ) *
            MvPolynomial.finSuccEquiv K 3 (U j.succ)) =
        Polynomial.monomial (e + lambda)
          (∑ j : Fin 3,
            ((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
            ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda)) := by
    calc
      (∑ j : Fin 3,
          MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ) *
            MvPolynomial.finSuccEquiv K 3 (U j.succ)) =
          ∑ j : Fin 3,
            Polynomial.monomial e
                ((MvPolynomial.finSuccEquiv K 3
                  (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
              Polynomial.monomial lambda
                ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg₂ (fun P Q : Polynomial (MvPolynomial (Fin 3) K) => P * Q)
          (htransH j) (F.transverseFactor j)
      _ = ∑ j : Fin 3,
            Polynomial.monomial (e + lambda)
              (((MvPolynomial.finSuccEquiv K 3
                (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
               ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Polynomial.monomial_mul_monomial]
      _ = Polynomial.monomial (e + lambda)
          (∑ j : Fin 3,
            ((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
            ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda)) := by
        rw [map_sum]
  rw [htransSum] at hrowSplit

  by_cases he : e = 0
  · have hRlong0 :
        ∀ d : Fin 4 →₀ ℕ,
          MvPolynomial.coeff d R ≠ 0 → d (0 : Fin 4) = 0 := by
      intro d hd
      exact (hRlong d hd).trans he
    have hmixedZero :
        MvPolynomial.finSuccEquiv K 3
            (HC4.Polynomial.hessian R i.succ (0 : Fin 4)) = 0 := by
      have hzero : HC4.Polynomial.hessian R i.succ (0 : Fin 4) = 0 := by
        ext d
        simp only [MvPolynomial.coeff_zero]
        by_contra hd
        have hrel :=
          hessian_succ_zero_longitudinalExponent_succ R 0 hRlong0 i d hd
        omega
      rw [hzero]
      simp
    have hmixedCoeffZero :
        (MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1) = 0 := by
      rw [hmixedZero]
      simp
    rw [hmixedCoeffZero] at hrowSplit
    simp only [Polynomial.monomial_zero_right, zero_mul, zero_add] at hrowSplit
    have htransEq :
        (∑ j : Fin 3,
          ((MvPolynomial.finSuccEquiv K 3
            (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
          ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda)) = 0 := by
      exact (Polynomial.monomial_eq_zero_iff _ _).mp hrowSplit
    have hresult :
        ((MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) *
            ((MvPolynomial.finSuccEquiv K 3 (U (0 : Fin 4))).coeff
              (lambda + 1)) +
          ∑ j : Fin 3,
            ((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
            ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda) = 0 := by
      rw [hmixedCoeffZero, zero_mul, zero_add]
      exact htransEq
    simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.mixedProfile,
      FirstKeyCanonicalMaximalHomogeneousKernelData.transverseHessianProfile,
      FirstKeyMaximalVectorLongitudinalFactorData.longitudinalProfile,
      FirstKeyMaximalVectorLongitudinalFactorData.transverseProfile,
      R, U, e, lambda] using hresult
  · have hexp : (e - 1) + (lambda + 1) = e + lambda := by omega
    have hmixedMul :
        Polynomial.monomial (e - 1)
              ((MvPolynomial.finSuccEquiv K 3
                (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) *
            Polynomial.monomial (lambda + 1)
              ((MvPolynomial.finSuccEquiv K 3 (U (0 : Fin 4))).coeff
                (lambda + 1)) =
          Polynomial.monomial (e + lambda)
            (((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) *
             ((MvPolynomial.finSuccEquiv K 3 (U (0 : Fin 4))).coeff
                (lambda + 1))) := by
      rw [Polynomial.monomial_mul_monomial, hexp]
    rw [hmixedMul] at hrowSplit
    have hcombined :
        Polynomial.monomial (e + lambda)
          (((MvPolynomial.finSuccEquiv K 3
            (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) *
              ((MvPolynomial.finSuccEquiv K 3 (U (0 : Fin 4))).coeff
                (lambda + 1)) +
            ∑ j : Fin 3,
              ((MvPolynomial.finSuccEquiv K 3
                (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
              ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda)) = 0 := by
      rw [map_add]
      exact hrowSplit
    have hresult :
        ((MvPolynomial.finSuccEquiv K 3
          (HC4.Polynomial.hessian R i.succ (0 : Fin 4))).coeff (e - 1)) *
            ((MvPolynomial.finSuccEquiv K 3 (U (0 : Fin 4))).coeff
              (lambda + 1)) +
          ∑ j : Fin 3,
            ((MvPolynomial.finSuccEquiv K 3
              (HC4.Polynomial.hessian R i.succ j.succ)).coeff e) *
            ((MvPolynomial.finSuccEquiv K 3 (U j.succ)).coeff lambda) = 0 := by
      exact (Polynomial.monomial_eq_zero_iff _ _).mp hcombined
    simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.mixedProfile,
      FirstKeyCanonicalMaximalHomogeneousKernelData.transverseHessianProfile,
      FirstKeyMaximalVectorLongitudinalFactorData.longitudinalProfile,
      FirstKeyMaximalVectorLongitudinalFactorData.transverseProfile,
      R, U, e, lambda] using hresult

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
