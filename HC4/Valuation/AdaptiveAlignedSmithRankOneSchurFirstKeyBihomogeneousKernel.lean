import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyMaximalHomogeneousKernel
import Mathlib.Tactic

/-!
# Bihomogeneous shape of the maximal first-key kernel vector

Stage 4B8 selects the polynomial kernel vector at the maximal *shifted*
transverse weight

    beta = max (wt(d) - wt(j)),

and Stage 4B9 then takes the maximal ordinary-homogeneous component of that
vector.

These two selections commute at the level of support: every surviving
monomial in the final vector has simultaneously

    ordinaryDegree(d) = E,
    wt(d) = beta + wt(j).

For the pure longitudinal/transverse weight, `wt(0)=0` and
`wt(1)=wt(2)=wt(3)=-1`.  Consequently:

* all three transverse vector coordinates have the same longitudinal
  exponent;
* the longitudinal coordinate has exactly one more power of `x₀` than every
  nonzero transverse coordinate.

This is the precise exponent shift required by the transverse Hessian rows of

    R = x₀^e H_m(x₁,x₂,x₃):

`R_{a0}` has one fewer `x₀` than `R_{ab}`, while the kernel coordinate `U₀`
has one more `x₀` than `U_b`.  Thus every term in a transverse kernel row has
the same longitudinal exponent.  The next stage can therefore cancel that
common monomial and work entirely in the transverse homogeneous profile.

No new kernel classification or factorisation machinery is introduced here;
this file records only the support consequence of the already-green B8/B9
initial-form choices.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero coefficient of the B9 ordinary-leading vector comes from the
previous vector and has exactly the selected common ordinary degree. -/
theorem ordinarySourceVectorLeading_coeff_source_and_degree
    (V : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d (ordinarySourceVectorLeading V hV j) ≠ 0) :
    MvPolynomial.coeff d (V j) ≠ 0 ∧
      HC4.Polynomial.ordinaryDegree4 d =
        ordinarySourceVectorTopDegree V hV := by
  have hd' := hd
  change
    MvPolynomial.coeff d
      (initialForm (fun _ : Fin 4 => (1 : ℤ))
        (ordinarySourceVectorTopDegree V hV : ℤ) (V j)) ≠ 0 at hd'
  rw [coeff_initialForm] at hd'
  by_cases hw :
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d =
        (ordinarySourceVectorTopDegree V hV : ℤ)
  · rw [if_pos hw] at hd'
    refine ⟨hd', ?_⟩
    rw [ordinaryIntegerWeight_eq_ordinaryDegree4] at hw
    exact_mod_cast hw
  · rw [if_neg hw] at hd'
    exact False.elim (hd' rfl)

/-- A nonzero coefficient of the B8 shifted-leading vector comes from the
source-coordinate kernel and has exactly the selected derivative-shifted
transverse weight. -/
theorem shiftedSourceVectorLeading_coeff_source_and_weight
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d (shiftedSourceVectorLeading W hW j) ≠ 0) :
    MvPolynomial.coeff d (W j) ≠ 0 ∧
      Finsupp.weight pureLongitudinalTransverseWeight d =
        shiftedSourceVectorTopWeight W hW +
          pureLongitudinalTransverseWeight j := by
  have hd' := hd
  change
    MvPolynomial.coeff d
      (initialForm pureLongitudinalTransverseWeight
        (shiftedSourceVectorTopWeight W hW +
          pureLongitudinalTransverseWeight j)
        (W j)) ≠ 0 at hd'
  rw [coeff_initialForm] at hd'
  by_cases hw :
      Finsupp.weight pureLongitudinalTransverseWeight d =
        shiftedSourceVectorTopWeight W hW +
          pureLongitudinalTransverseWeight j
  · rw [if_pos hw] at hd'
    exact ⟨hd', hw⟩
  · rw [if_neg hw] at hd'
    exact False.elim (hd' rfl)

/-- **B8+B9 bidegree profile.**

Every surviving coefficient after first taking the derivative-shifted
transverse leading vector and then its maximal ordinary component has both
selected degrees simultaneously. -/
theorem ordinaryOfShiftedLeading_coeff_profile
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (ordinarySourceVectorLeading
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) j) ≠ 0) :
    HC4.Polynomial.ordinaryDegree4 d =
        ordinarySourceVectorTopDegree
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) ∧
      Finsupp.weight pureLongitudinalTransverseWeight d =
        shiftedSourceVectorTopWeight W hW +
          pureLongitudinalTransverseWeight j := by
  have hord :=
    ordinarySourceVectorLeading_coeff_source_and_degree
      (shiftedSourceVectorLeading W hW)
      (shiftedSourceVectorLeading_ne_zero W hW) j d hd
  have hshift :=
    shiftedSourceVectorLeading_coeff_source_and_weight
      W hW j d hord.1
  exact ⟨hord.2, hshift.2⟩

/-- Any two nonzero transverse coordinates of the B9 vector have identical
longitudinal exponent on every pair of supported monomials. -/
theorem ordinaryOfShiftedLeading_transverse_longitudinalExponent_eq
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (j k : Fin 3)
    (d e : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (ordinarySourceVectorLeading
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) j.succ) ≠ 0)
    (he :
      MvPolynomial.coeff e
        (ordinarySourceVectorLeading
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) k.succ) ≠ 0) :
    d (0 : Fin 4) = e (0 : Fin 4) := by
  rcases ordinaryOfShiftedLeading_coeff_profile W hW j.succ d hd with
    ⟨hdegd, hwd⟩
  rcases ordinaryOfShiftedLeading_coeff_profile W hW k.succ e he with
    ⟨hdege, hwe⟩
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 d =
        HC4.Polynomial.ordinaryDegree4 e := by
    omega
  rw [weight_pureLongitudinalTransverseWeight] at hwd hwe
  have htransZ :
      (pureLongitudinalTransverseDegree d : ℤ) =
        (pureLongitudinalTransverseDegree e : ℤ) := by
    simp only [pureLongitudinalTransverseWeight_succ] at hwd hwe
    omega
  have htrans :
      pureLongitudinalTransverseDegree d =
        pureLongitudinalTransverseDegree e := by
    exact_mod_cast htransZ
  unfold HC4.Polynomial.ordinaryDegree4 at hdeg
  unfold pureLongitudinalTransverseDegree at htrans
  omega

/-- The longitudinal coordinate of the B9 vector carries exactly one extra
power of `x₀` compared with every nonzero transverse coordinate. -/
theorem ordinaryOfShiftedLeading_zero_longitudinalExponent_eq_succ
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (j : Fin 3)
    (d e : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (ordinarySourceVectorLeading
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) (0 : Fin 4)) ≠ 0)
    (he :
      MvPolynomial.coeff e
        (ordinarySourceVectorLeading
          (shiftedSourceVectorLeading W hW)
          (shiftedSourceVectorLeading_ne_zero W hW) j.succ) ≠ 0) :
    d (0 : Fin 4) = e (0 : Fin 4) + 1 := by
  rcases ordinaryOfShiftedLeading_coeff_profile W hW (0 : Fin 4) d hd with
    ⟨hdegd, hwd⟩
  rcases ordinaryOfShiftedLeading_coeff_profile W hW j.succ e he with
    ⟨hdege, hwe⟩
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 d =
        HC4.Polynomial.ordinaryDegree4 e := by
    omega
  rw [weight_pureLongitudinalTransverseWeight] at hwd hwe
  have htransZ :
      (pureLongitudinalTransverseDegree e : ℤ) =
        (pureLongitudinalTransverseDegree d : ℤ) + 1 := by
    simp only [pureLongitudinalTransverseWeight_zero,
      pureLongitudinalTransverseWeight_succ] at hwd hwe
    omega
  have htrans :
      pureLongitudinalTransverseDegree e =
        pureLongitudinalTransverseDegree d + 1 := by
    exact_mod_cast htransZ
  unfold HC4.Polynomial.ordinaryDegree4 at hdeg
  unfold pureLongitudinalTransverseDegree at htrans
  omega

/-- The maximal ordinary leading vector depends only on the underlying
vector, not on the particular proof of nonzeroness.  This is the safe
transport lemma used by the carrier wrappers below; it avoids dependent
rewriting through the `V ≠ 0` argument. -/
theorem ordinarySourceVectorLeading_congr
    (V W : Fin 4 → MvPolynomial (Fin 4) K)
    (hV : V ≠ 0) (hW : W ≠ 0)
    (hVW : V = W) :
    ordinarySourceVectorLeading V hV =
      ordinarySourceVectorLeading W hW := by
  subst W
  rfl

/-! ## Carrier-facing canonical vector -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The exact B9 vector attached to a B8 leading-kernel package. -/
noncomputable def FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  ordinarySourceVectorLeading L.leadingVector L.leading_ne_zero

/-- The canonical maximal vector is nonzero. -/
theorem FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    L.maximalHomogeneousVector ≠ 0 := by
  simpa [FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector] using
    ordinarySourceVectorLeading_ne_zero L.leadingVector L.leading_ne_zero

/-- Carrier form of the transverse-coordinate longitudinal-exponent
coincidence. -/
theorem FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector_transverse_longitudinalExponent_eq
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (j k : Fin 3)
    (d e : Fin 4 →₀ ℕ)
    (hd : MvPolynomial.coeff d (L.maximalHomogeneousVector j.succ) ≠ 0)
    (he : MvPolynomial.coeff e (L.maximalHomogeneousVector k.succ) ≠ 0) :
    d (0 : Fin 4) = e (0 : Fin 4) := by
  have hmax :
      L.maximalHomogeneousVector =
        ordinarySourceVectorLeading
          (shiftedSourceVectorLeading
            L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
          (shiftedSourceVectorLeading_ne_zero
            L.sourceKernel.vector L.sourceKernel.vector_ne_zero) := by
    unfold FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector
    exact ordinarySourceVectorLeading_congr
      L.leadingVector
      (shiftedSourceVectorLeading
        L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
      L.leading_ne_zero
      (shiftedSourceVectorLeading_ne_zero
        L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
      L.leading_eq
  rw [hmax] at hd he
  exact ordinaryOfShiftedLeading_transverse_longitudinalExponent_eq
    L.sourceKernel.vector L.sourceKernel.vector_ne_zero j k d e hd he

/-- Carrier form of the one-extra-`x₀` relation between the longitudinal and
transverse vector coordinates. -/
theorem FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector_zero_longitudinalExponent_eq_succ
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (j : Fin 3)
    (d e : Fin 4 →₀ ℕ)
    (hd : MvPolynomial.coeff d (L.maximalHomogeneousVector (0 : Fin 4)) ≠ 0)
    (he : MvPolynomial.coeff e (L.maximalHomogeneousVector j.succ) ≠ 0) :
    d (0 : Fin 4) = e (0 : Fin 4) + 1 := by
  have hmax :
      L.maximalHomogeneousVector =
        ordinarySourceVectorLeading
          (shiftedSourceVectorLeading
            L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
          (shiftedSourceVectorLeading_ne_zero
            L.sourceKernel.vector L.sourceKernel.vector_ne_zero) := by
    unfold FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector
    exact ordinarySourceVectorLeading_congr
      L.leadingVector
      (shiftedSourceVectorLeading
        L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
      L.leading_ne_zero
      (shiftedSourceVectorLeading_ne_zero
        L.sourceKernel.vector L.sourceKernel.vector_ne_zero)
      L.leading_eq
  rw [hmax] at hd he
  exact ordinaryOfShiftedLeading_zero_longitudinalExponent_eq_succ
    L.sourceKernel.vector L.sourceKernel.vector_ne_zero j d e hd he

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
