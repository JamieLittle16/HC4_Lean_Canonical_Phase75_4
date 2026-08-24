import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyTransverseDerivativeProfile
import Mathlib.Tactic

/-!
# Euler-radial reduction of the first-key transverse kernel equation

Stage 4B13 gives, for the nonzero-transverse-coordinate branch of the
canonical maximal first-key kernel,

    e * (∂ᵢ H) * A + sum_j (∂ᵢ∂ⱼ H) * B_j = 0.

It is important not to over-classify this equation.  For a homogeneous
transverse form `H` there is always the Euler identity

    sum_j X_j * ∂ᵢ∂ⱼ H = (m-1) * ∂ᵢ H.

Consequently the B13 equation has a universal radial solution.  This file
isolates that mode exactly.  Define

    W_j = (m-1) B_j + e A X_j.

Then `Hess(H) * W = 0`.  Hence either `W = 0`, in which case the B13 kernel
is purely Euler-radial, or `W` is a genuine nonzero polynomial Hessian kernel
of the transverse homogeneous form `H`.

This is the correct next interface for the raw-Schur provenance argument:
the remaining Schur data must rule out the radial mode (or turn it into
certified repair) before a linear-power classification is invoked.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## Generic Euler correction -/

/-- Euler's identity differentiated once: for a homogeneous form of degree
`m`, the Hessian applied to the radial vector is `(m-1)` times the gradient. -/
theorem homogeneous_hessian_mul_X
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (i : Fin n) :
    (∑ j : Fin n,
        HC4.Polynomial.hessian H i j * MvPolynomial.X j) =
      MvPolynomial.C ((m - 1 : ℕ) : K) * MvPolynomial.pderiv i H := by
  have hfirst :
      (MvPolynomial.pderiv i H).IsHomogeneous (m - 1) := by
    simpa using hhom.pderiv
  have heuler := hfirst.sum_X_mul_pderiv
  simpa [HC4.Polynomial.hessian_apply, mul_comm] using heuler

/-- Euler-corrected transverse kernel vector associated to

    e * grad(H) * A + Hess(H) * B = 0.
-/
noncomputable def eulerCorrectedTransverseVector
    {n : ℕ}
    (e m : ℕ)
    (A : MvPolynomial (Fin n) K)
    (B : Fin n → MvPolynomial (Fin n) K) :
    Fin n → MvPolynomial (Fin n) K :=
  fun j =>
    MvPolynomial.C ((m - 1 : ℕ) : K) * B j +
      MvPolynomial.C (e : K) * A * MvPolynomial.X j

/-- The B13-type equation becomes an honest Hessian-kernel equation after
subtracting the universal Euler-radial mode. -/
theorem eulerCorrectedTransverseVector_kernel
    {n : ℕ}
    (H A : MvPolynomial (Fin n) K)
    (B : Fin n → MvPolynomial (Fin n) K)
    (e m : ℕ)
    (hhom : H.IsHomogeneous m)
    (heq :
      ∀ i : Fin n,
        (MvPolynomial.C (e : K) * MvPolynomial.pderiv i H) * A +
            ∑ j : Fin n,
              HC4.Polynomial.hessian H i j * B j = 0) :
    ∀ i : Fin n,
      ∑ j : Fin n,
        HC4.Polynomial.hessian H i j *
          eulerCorrectedTransverseVector e m A B j = 0 := by
  intro i
  have hB := heq i
  have hEuler := homogeneous_hessian_mul_X H m hhom i
  have hfactor :
      (∑ j : Fin n,
          HC4.Polynomial.hessian H i j *
            eulerCorrectedTransverseVector e m A B j) =
        MvPolynomial.C ((m - 1 : ℕ) : K) *
            (∑ j : Fin n, HC4.Polynomial.hessian H i j * B j) +
          (MvPolynomial.C (e : K) * A) *
            (∑ j : Fin n,
              HC4.Polynomial.hessian H i j * MvPolynomial.X j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [eulerCorrectedTransverseVector]
    ring
  rw [hfactor, hEuler]
  linear_combination
    MvPolynomial.C ((m - 1 : ℕ) : K) * hB

/-! ## Carrier specialisation -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The transverse degree selected by the first spatial key. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) : ℕ :=
  firstPositiveTransverseSourceDegree
    (polynomialFamilySpecialFiber C.family) L.hpos

/-- The pure transverse profile `H` in the maximal homogeneous slice
`R = x₀^e H` is genuinely homogeneous of the first positive transverse
degree `m`.  This uses Mathlib's existing `finSuccEquiv` homogeneous
coefficient theorem rather than a new support classification. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile_homogeneous
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    D.transverseSourceProfile.IsHomogeneous D.transverseDegree := by
  let m := D.transverseDegree
  let e := D.sourceExponent
  let N := D.sliceData.sliceData.ordinaryDegree
  let R := D.sliceData.sliceData.slice

  have hmle : m ≤ N := by
    rcases MvPolynomial.support_nonempty.mpr D.sliceData.sliceData.slice_ne_zero with
      ⟨d, hdmem⟩
    have hd : MvPolynomial.coeff d R ≠ 0 := by
      simpa [R] using MvPolynomial.mem_support_iff.mp hdmem
    have hdeg := (D.sliceData.sliceData.slice_source d (by simpa [R] using hd)).2
    have htrans := D.sliceData.sliceData.slice_exactTransverseDegree d
      (by simpa [R] using hd)
    unfold HC4.Polynomial.ordinaryDegree4 at hdeg
    unfold pureLongitudinalTransverseDegree at htrans
    dsimp [N, m, FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree]
    omega

  have hem : e + m = N := by
    dsimp [e, m, N]
    rw [FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent,
      FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree]
    exact Nat.sub_add_cancel hmle

  have hRhom : R.IsHomogeneous N := by
    simpa [R, N] using D.sliceData.sliceData.slice_homogeneous

  have hcoeff := hRhom.finSuccEquiv_coeff_isHomogeneous e m hem
  simpa [R, e, m, N,
    FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile]
    using hcoeff

/-- The transverse source profile is nonzero. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    D.transverseSourceProfile ≠ 0 := by
  intro hzero
  have hfac :
      MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice =
        Polynomial.monomial D.sourceExponent D.transverseSourceProfile := by
    simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent,
      FirstKeyCanonicalMaximalHomogeneousKernelData.transverseSourceProfile] using
      D.slice_finSuccEquiv_eq_monomial
  have himage :
      MvPolynomial.finSuccEquiv K 3 D.sliceData.sliceData.slice = 0 := by
    rw [hfac, hzero]
    exact Polynomial.monomial_zero_right _
  apply D.sliceData.sliceData.slice_ne_zero
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simpa using himage

/-- Euler-corrected kernel vector attached to the B13 transverse equation. -/
noncomputable def FirstKeyCanonicalMaximalHomogeneousKernelData.eulerCorrectedVector
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    Fin 3 → MvPolynomial (Fin 3) K :=
  eulerCorrectedTransverseVector
    D.sourceExponent D.transverseDegree
    F.longitudinalProfile F.transverseProfile

/-- The corrected vector is annihilated by the Hessian of the actual
transverse first-key profile. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.eulerCorrectedVector_kernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian D.transverseSourceProfile).mulVec
        (D.eulerCorrectedVector F) i = 0 := by
  intro i
  change
    ∑ j : Fin 3,
      HC4.Polynomial.hessian D.transverseSourceProfile i j *
        eulerCorrectedTransverseVector
          D.sourceExponent D.transverseDegree
          F.longitudinalProfile F.transverseProfile j = 0
  exact
    eulerCorrectedTransverseVector_kernel
      D.transverseSourceProfile F.longitudinalProfile F.transverseProfile
      D.sourceExponent D.transverseDegree
      D.transverseSourceProfile_homogeneous
      (D.transverseDerivativeEquation F) i

/-- A genuine non-radial transverse Hessian-kernel packet. -/
structure FirstKeyNonradialTransverseKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  vector : Fin 3 → MvPolynomial (Fin 3) K
  vector_ne_zero : vector ≠ 0
  kernel :
    ∀ i : Fin 3,
      (HC4.Polynomial.hessian D.transverseSourceProfile).mulVec vector i = 0

/-- **Stage 4B14 exact radial/non-radial fork.**

The B13 transverse equation has only two possibilities at this level:

* the Euler-corrected vector vanishes identically, i.e. the surviving kernel
  is purely radial; or
* the transverse homogeneous profile carries a genuine nonzero polynomial
  Hessian-kernel vector.

The first branch is exactly where the still-unused raw-Schur/first-actual
provenance must now enter. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_or_nonradialKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    D.eulerCorrectedVector F = 0 ∨
      Nonempty (C.FirstKeyNonradialTransverseKernelData D F) := by
  classical
  by_cases hzero : D.eulerCorrectedVector F = 0
  · exact Or.inl hzero
  · right
    exact ⟨{
      vector := D.eulerCorrectedVector F
      vector_ne_zero := hzero
      kernel := D.eulerCorrectedVector_kernel F
    }⟩

/-- Pointwise form of the radial branch. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_relation
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hrad : D.eulerCorrectedVector F = 0)
    (j : Fin 3) :
    MvPolynomial.C ((D.transverseDegree - 1 : ℕ) : K) *
          F.transverseProfile j +
        MvPolynomial.C (D.sourceExponent : K) *
          F.longitudinalProfile * MvPolynomial.X j = 0 := by
  have hj := congrFun hrad j
  simpa [FirstKeyCanonicalMaximalHomogeneousKernelData.eulerCorrectedVector,
    eulerCorrectedTransverseVector] using hj

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
