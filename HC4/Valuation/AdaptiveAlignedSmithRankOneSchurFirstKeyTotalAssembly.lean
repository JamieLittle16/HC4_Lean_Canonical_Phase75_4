import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLinearCornerElimination
import Mathlib.Tactic

/-!
# Stage 4B28: unconditional assembly of the first-key RS2 frontier

Stages 4B11--4B26 analysed the branch in which the maximal homogeneous
leading kernel vector has a nonzero transverse coordinate.  The B11 API was
intentionally lossless, however, and retained one additional possibility:

    forall j : Fin 3, U_{j+1} = 0.

Before the final Schur/RS2 provenance theorem can consume the classification,
that branch must be discharged rather than silently assuming the B11 factor
package exists.

This file closes it using only already-green machinery.

Let `U` be B10's canonical maximal homogeneous kernel vector and `R = x₀^e H`
the B9 maximal homogeneous first-key slice.  If all three transverse
coordinates of `U` vanish, then `U₀ ≠ 0`.  The transverse Hessian rows give

    (partial_i partial_0 R) U₀ = 0.

Hence every mixed Hessian entry is zero.  If `e > 0`, B13 identifies its pure
transverse profile with

    e * partial_i H.

Since `H` is nonzero homogeneous of positive degree, some `partial_i H` is
nonzero, contradiction.  Thus `e = 0`.

Now B16 says either `m = 1` or the blocker is pure longitudinal.  In the first
case `(e,m)=(0,1)` contradicts B26.  In the second case B17 forces `U₀ = 0`,
contradicting `U₀ ≠ 0`.

Therefore a transverse maximal coordinate always survives.  Consequently the
B11 longitudinal-factor package exists *unconditionally*, and the whole
source-side development can finally be assembled into one record whose only
outcomes are certified rank-two repair or an RS2-ready `x₀^e L^m` packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- If the canonical maximal homogeneous kernel is purely longitudinal, then
its first-key slice has longitudinal exponent zero. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.sourceExponent_eq_zero_of_transverseVector_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (hzero : forall j : Fin 3,
      L.maximalHomogeneousVector j.succ = 0) :
    D.sourceExponent = 0 := by
  by_contra he0
  have hepos : 0 < D.sourceExponent := Nat.pos_of_ne_zero he0
  have hU0 : L.maximalHomogeneousVector (0 : Fin 4) ≠ 0 :=
    L.zeroCoordinate_ne_zero_of_transverse_zero hzero

  rcases homogeneous_exists_pderiv_ne_zero
      D.transverseSourceProfile D.transverseDegree
      D.transverseSourceProfile_homogeneous
      D.transverseSourceProfile_ne_zero D.transverseDegree_pos with
    ⟨i, hi⟩

  have hrow :
      (∑ j : Fin 4,
        HC4.Polynomial.hessian D.sliceData.sliceData.slice i.succ j *
          L.maximalHomogeneousVector j) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using D.transverseKernel i
  rw [Fin.sum_univ_succ] at hrow
  have hrow0 :
      HC4.Polynomial.hessian D.sliceData.sliceData.slice
          i.succ (0 : Fin 4) *
        L.maximalHomogeneousVector (0 : Fin 4) = 0 := by
    simpa [hzero] using hrow
  have hmixedEntry :
      HC4.Polynomial.hessian D.sliceData.sliceData.slice
          i.succ (0 : Fin 4) = 0 :=
    (mul_eq_zero.mp hrow0).resolve_right hU0

  have hprofile0 : D.mixedProfile i = 0 := by
    change
      ((MvPolynomial.finSuccEquiv K 3
        (HC4.Polynomial.hessian D.sliceData.sliceData.slice
          i.succ (0 : Fin 4))).coeff (D.sourceExponent - 1)) = 0
    rw [hmixedEntry]
    simp
  have hprofile := D.mixedProfile_eq i
  rw [hprofile0] at hprofile
  have hprod :
      MvPolynomial.C (D.sourceExponent : K) *
          MvPolynomial.pderiv i D.transverseSourceProfile = 0 := by
    exact hprofile.symm
  have heK : (D.sourceExponent : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hepos)
  have hCe :
      (MvPolynomial.C (D.sourceExponent : K) :
        MvPolynomial (Fin 3) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr heK
  have hi0 : MvPolynomial.pderiv i D.transverseSourceProfile = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hCe
  exact hi hi0

/-- The lossless B11 pure-longitudinal-vector branch is impossible.

This is the missing branch needed to make the later `FirstKeyMaximalVector-
LongitudinalFactorData` construction unconditional. -/
theorem FirstKeyLeadingTransverseKernelData.hasNonzeroTransverseMaximalCoordinate
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    L.HasNonzeroTransverseMaximalCoordinate := by
  classical
  by_contra hnone
  unfold FirstKeyLeadingTransverseKernelData.HasNonzeroTransverseMaximalCoordinate at hnone
  push_neg at hnone
  have hzero : forall j : Fin 3,
      L.maximalHomogeneousVector j.succ = 0 := hnone

  rcases L.exists_canonicalMaximalHomogeneousKernelData with ⟨D⟩
  have he0 := D.sourceExponent_eq_zero_of_transverseVector_zero hzero

  rcases D.degreeOne_or_pureLongitudinalBlocker with hm | hpure
  · exact D.not_linearCorner ⟨he0, hm⟩
  · have hU0 : L.maximalHomogeneousVector (0 : Fin 4) ≠ 0 :=
      L.zeroCoordinate_ne_zero_of_transverse_zero hzero
    have hU0zero :=
      L.maximalHomogeneousVector_zero_eq_zero_of_pureLongitudinal hpure
    exact hU0 hU0zero

/-- B11's exact common-longitudinal-factor package therefore exists for every
canonical first-key leading kernel; no branch hypothesis remains. -/
theorem FirstKeyLeadingTransverseKernelData.exists_longitudinalFactorData_unconditional
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (L : C.FirstKeyLeadingTransverseKernelData) :
    Nonempty (C.FirstKeyMaximalVectorLongitudinalFactorData L) := by
  exact L.exists_longitudinalFactorData L.hasNonzeroTransverseMaximalCoordinate

/-- Complete canonical source-side data retained by the final Schur/RS2
provenance theorem. -/
structure FirstKeyCanonicalRS2AssemblyData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  leading : C.FirstKeyLeadingTransverseKernelData
  canonical : C.FirstKeyCanonicalMaximalHomogeneousKernelData leading
  factor : C.FirstKeyMaximalVectorLongitudinalFactorData leading

/-- Every B1 first-spatial-key certificate now reaches the complete canonical
B26 source frontier without any hidden maximal-vector branch. -/
theorem HasFirstTransverseSourceKey.exists_canonicalRS2AssemblyData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey) :
    Nonempty (C.FirstKeyCanonicalRS2AssemblyData) := by
  rcases hkey.exists_leadingTransverseKernelData with ⟨L⟩
  rcases L.exists_canonicalMaximalHomogeneousKernelData with ⟨D⟩
  rcases L.exists_longitudinalFactorData_unconditional with ⟨F⟩
  exact ⟨{
    leading := L
    canonical := D
    factor := F
  }⟩

/-- **Stage 4B28 total source frontier.**

Once the canonical assembly exists, B26 gives exactly two outcomes and no
unrecorded branch: certified rank-two repair or an RS2-ready `x₀^e L^m`
first-key packet. -/
theorem FirstKeyCanonicalRS2AssemblyData.rankTwoRepair_or_rs2Ready
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : C.FirstKeyCanonicalRS2AssemblyData)
    (complexity : ℕ) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData A.canonical complexity) ∨
      Nonempty (C.FirstKeyXeLmRS2ReadyData A.canonical) := by
  exact A.canonical.rankTwoRepair_or_rs2Ready A.factor complexity

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
