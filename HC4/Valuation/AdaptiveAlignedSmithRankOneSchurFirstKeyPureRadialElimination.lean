import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyBlockerPatternReduction
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import Mathlib.Tactic

/-!
# Elimination of the pure-longitudinal strict radial first-key branch

Stage 4B16 reduces the first-key frontier to

    transverse degree one
    | pure-longitudinal strict radial
    | genuine nonradial transverse Hessian kernel.

The remaining strict-radial branch is incompatible with the longitudinal
row of the *original* source-coordinate Hessian kernel.

Let `F` be the honest right-recentered special fibre, let `W` be the full
Stage-3 polynomial Hessian-kernel vector, and let `V` be B8's canonical
shifted leading vector at shifted weight `beta`.

For a pure-longitudinal blocker, the weight-zero longitudinal Hessian pivot

    H00^(0) = Hess(in_0 F)_{00}

is nonzero by the already-green pure-longitudinal curvature theorem.  In row
zero of `Hess(F) W = 0`, the `j=0` term has top weight `beta`, whereas every
transverse `j>0` term is bounded by `beta-m`, with `m>0` the first positive
transverse source degree.  Taking exact weight `beta` therefore gives

    H00^(0) * V_0 = 0,

hence `V_0 = 0`.

Ordinary-homogeneous descent preserves this zero coordinate, so the B11
longitudinal profile `A` vanishes.  This contradicts the strict-radial datum
from B15, where `A != 0`.

Thus after this file the frontier is genuinely only

    transverse degree one | nonradial transverse Hessian kernel.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- Row-zero analogue of the B8 leading-kernel filtration in the presence of
an actual nonzero weight-zero longitudinal Hessian pivot.

The transverse row terms lie strictly below the selected shifted top weight,
so the top component of row zero contains only the longitudinal pivot times
the longitudinal coordinate of the leading kernel vector. -/
theorem shiftedSourceVectorLeading_zero_eq_zero_of_axisPivot
    (F : MvPolynomial (Fin 4) K)
    (hpos : (positiveTransverseSourceSupport F).Nonempty)
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    (hkernel : (HC4.Polynomial.hessian F).mulVec W = 0)
    (hpivot :
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian F (0 : Fin 4) (0 : Fin 4)) ≠ 0) :
    shiftedSourceVectorLeading W hW (0 : Fin 4) = 0 := by
  let m := firstPositiveTransverseSourceDegree F hpos
  let beta := shiftedSourceVectorTopWeight W hW
  let V := shiftedSourceVectorLeading W hW
  let Fzero := initialForm pureLongitudinalTransverseWeight 0 F

  have hmpos : 0 < m := by
    rcases exists_source_firstPositiveTransverseSourceDegree F hpos with
      ⟨d, hd, hdpos, hdeq⟩
    simpa [m, hdeq] using hdpos

  have hFLE : IsWeightLE pureLongitudinalTransverseWeight 0 F :=
    isWeightLE_zero_pureLongitudinalTransverseWeight F

  have hH00LE :
      IsWeightLE pureLongitudinalTransverseWeight 0
        (HC4.Polynomial.hessian F (0 : Fin 4) (0 : Fin 4)) := by
    simpa using hFLE.hessian_entry (0 : Fin 4) (0 : Fin 4)

  have hW0LE :
      IsWeightLE pureLongitudinalTransverseWeight beta (W (0 : Fin 4)) := by
    simpa [beta] using
      shiftedSourceVector_component_isWeightLE W hW (0 : Fin 4)

  have htop00 :
      initialForm pureLongitudinalTransverseWeight 0
          (HC4.Polynomial.hessian F (0 : Fin 4) (0 : Fin 4)) =
        HC4.Polynomial.hessian Fzero (0 : Fin 4) (0 : Fin 4) := by
    have hh := hessian_initialForm_entry
      pureLongitudinalTransverseWeight 0 F (0 : Fin 4) (0 : Fin 4)
    simpa [Fzero] using hh.symm

  have hpivot0 :
      HC4.Polynomial.hessian Fzero (0 : Fin 4) (0 : Fin 4) ≠ 0 := by
    simpa [Fzero] using
      hessian_zero_zero_initialForm_zero_ne_zero_of_axisRestriction_ne_zero
        F hpivot

  have hlongTop :
      initialForm pureLongitudinalTransverseWeight beta
          (HC4.Polynomial.hessian F (0 : Fin 4) (0 : Fin 4) * W 0) =
        HC4.Polynomial.hessian Fzero (0 : Fin 4) (0 : Fin 4) * V 0 := by
    have hmul := initialForm_mul_eq_mul_initialForm_of_isWeightLE
      (K := K) hH00LE hW0LE
    have hsum : (0 : ℤ) + beta = beta := by ring
    rw [hsum] at hmul
    rw [htop00] at hmul
    simpa [V, beta, shiftedSourceVectorLeading] using hmul

  have htransTop :
      ∀ j : Fin 3,
        initialForm pureLongitudinalTransverseWeight beta
          (HC4.Polynomial.hessian F (0 : Fin 4) j.succ * W j.succ) = 0 := by
    intro j
    have hHj0LE := transverseHessianRow_isWeightLE_firstPositive
      F hpos j (0 : Fin 4)
    have hH0jLE :
        IsWeightLE pureLongitudinalTransverseWeight (-(m : ℤ) + 1)
          (HC4.Polynomial.hessian F (0 : Fin 4) j.succ) := by
      have hsymm :
          HC4.Polynomial.hessian F (0 : Fin 4) j.succ =
            HC4.Polynomial.hessian F j.succ (0 : Fin 4) := by
        simp only [HC4.Polynomial.hessian_apply]
        exact pderiv_comm_commRing _ _ _
      rw [hsymm]
      simpa [m] using hHj0LE
    have hWjLE :
        IsWeightLE pureLongitudinalTransverseWeight (beta - 1) (W j.succ) := by
      have hw := shiftedSourceVector_component_isWeightLE W hW j.succ
      simpa [beta] using hw
    have hprodLE :
        IsWeightLE pureLongitudinalTransverseWeight
          ((-(m : ℤ) + 1) + (beta - 1))
          (HC4.Polynomial.hessian F (0 : Fin 4) j.succ * W j.succ) :=
      hH0jLE.mul hWjLE
    apply initialForm_eq_zero_of_isWeightLE hprodLE
    have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hmpos
    omega

  have hrow :
      ∑ j : Fin 4,
        HC4.Polynomial.hessian F (0 : Fin 4) j * W j = 0 := by
    have h0 := congrFun hkernel (0 : Fin 4)
    simpa [Matrix.mulVec, dotProduct] using h0

  have hrowSplit := hrow
  rw [Fin.sum_univ_succ] at hrowSplit

  have htransSumTop :
      initialForm pureLongitudinalTransverseWeight beta
          (∑ j : Fin 3,
            HC4.Polynomial.hessian F (0 : Fin 4) j.succ * W j.succ) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact htransTop j

  have htopEq := congrArg
    (fun P : MvPolynomial (Fin 4) K =>
      initialForm pureLongitudinalTransverseWeight beta P)
    hrowSplit
  change
    initialForm pureLongitudinalTransverseWeight beta
        (HC4.Polynomial.hessian F (0 : Fin 4) (0 : Fin 4) * W 0 +
          ∑ i : Fin 3, HC4.Polynomial.hessian F (0 : Fin 4) i.succ * W i.succ) =
      initialForm pureLongitudinalTransverseWeight beta 0 at htopEq
  rw [HC4.Polynomial.initialForm_add, hlongTop, htransSumTop] at htopEq
  simp only [HC4.Polynomial.initialForm_zero, add_zero] at htopEq
  have hprod :
      HC4.Polynomial.hessian Fzero (0 : Fin 4) (0 : Fin 4) * V 0 = 0 := by
    simpa using htopEq
  exact (mul_eq_zero.mp hprod).resolve_left hpivot0

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- On the pure-longitudinal blocker, B8's canonical leading source-kernel
vector has zero longitudinal coordinate. -/
theorem FirstKeyLeadingTransverseKernelData.leadingVector_zero_eq_zero_of_pureLongitudinal
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (hpure : IsPureLongitudinalSmithPattern B.exponent) :
    L.leadingVector (0 : Fin 4) = 0 := by
  rcases B.pureLongitudinalResidual_of_pattern hpure with ⟨P⟩
  have hpivot :
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber C.family)
          (0 : Fin 4) (0 : Fin 4)) ≠ 0 := by
    rw [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family,
      B.aligned.endpoint.rightRecenteredFamily_specialFiber]
    exact P.rightRecentered_hessian_zero_zero_axis_ne_zero
  rw [L.leading_eq]
  exact shiftedSourceVectorLeading_zero_eq_zero_of_axisPivot
    (polynomialFamilySpecialFiber C.family)
    L.hpos L.sourceKernel.vector L.sourceKernel.vector_ne_zero
    L.sourceKernel.kernel hpivot

/-- The zero leading longitudinal coordinate survives the B9 ordinary
homogeneous descent. -/
theorem FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector_zero_eq_zero_of_pureLongitudinal
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData)
    (hpure : IsPureLongitudinalSmithPattern B.exponent) :
    L.maximalHomogeneousVector (0 : Fin 4) = 0 := by
  have h0 := L.leadingVector_zero_eq_zero_of_pureLongitudinal hpure
  unfold FirstKeyLeadingTransverseKernelData.maximalHomogeneousVector
  unfold ordinarySourceVectorLeading
  rw [h0]
  simp

/-- Consequently every B11 factor package over the pure-longitudinal blocker
has zero longitudinal transverse profile. -/
theorem FirstKeyMaximalVectorLongitudinalFactorData.longitudinalProfile_eq_zero_of_pureLongitudinal
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hpure : IsPureLongitudinalSmithPattern B.exponent) :
    F.longitudinalProfile = 0 := by
  have h0 := L.maximalHomogeneousVector_zero_eq_zero_of_pureLongitudinal hpure
  unfold FirstKeyMaximalVectorLongitudinalFactorData.longitudinalProfile
  rw [h0]
  simp

/-- **Stage 4B17 pure-radial elimination.**

The pure-longitudinal strict-radial branch left by B16 is impossible: row-zero
leading-weight filtration forces its longitudinal profile to vanish, whereas
B15 strict radiality proves that profile nonzero. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.no_strictRadial_of_pureLongitudinal
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hpure : IsPureLongitudinalSmithPattern B.exponent)
    (S : C.FirstKeyStrictRadialProfileData D F) : False := by
  exact S.longitudinalProfile_ne_zero
    (F.longitudinalProfile_eq_zero_of_pureLongitudinal hpure)

/-- **Stage 4B17 two-way first-key frontier.**

After the blocker-pattern reduction and the row-zero pure-pivot elimination,
only the intended alternatives remain: the transverse first key has degree
one, or its homogeneous transverse profile carries a genuine nonradial
Hessian-kernel vector. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_nonradialKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyNonradialTransverseKernelData D F) := by
  rcases D.degreeOne_or_pureStrictRadial_or_nonradialKernel F with
    hdegree | hrest
  · exact Or.inl hdegree
  · rcases hrest with hstrict | hnon
    · rcases hstrict with ⟨hpure, ⟨S⟩⟩
      exact False.elim (D.no_strictRadial_of_pureLongitudinal F hpure S)
    · exact Or.inr hnon

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
