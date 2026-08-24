import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyEulerRadialReduction
import Mathlib.Tactic

/-!
# Exact normal form of the Euler-radial first-key branch

Stage 4B14 isolates the universal Euler-radial mode in the transverse
first-key equation.  This file compresses that radial branch to the one case
which still needs genuine source/Schur provenance.

Let

    e = sourceExponent,
    m = transverseDegree,
    A = longitudinal kernel profile,
    B = transverse kernel profile.

If the Euler-corrected vector vanishes, then

    (m-1) B_j + e A X_j = 0.

Because the factor-data branch contains an actually nonzero transverse
coordinate, at least one `B_j` is nonzero.  Hence:

* if `e = 0`, necessarily `m = 1`;
* if `m >= 2`, necessarily `e > 0` and `A != 0`.

Thus every radial branch is either already degree-one (the desired linear
transverse profile) or belongs to one strict residual normal form with
`e > 0`, `m >= 2`, nonzero `A`, and the displayed radial equations.

Together with B14 this gives the exact three-way frontier used by the next
source/Schur compatibility theorem:

    degree-one | strict radial | genuine nonradial Hessian kernel.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The first positive transverse source degree retained by B14 is genuinely
positive. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree_pos
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    0 < D.transverseDegree := by
  unfold FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree
  rcases exists_source_firstPositiveTransverseSourceDegree
      (polynomialFamilySpecialFiber C.family) L.hpos with
    ⟨d, hd, hpos, hdeg⟩
  rw [← hdeg]
  exact hpos

/-- The longitudinal-factor branch really contains a nonzero pure transverse
profile in at least one coordinate.  This is just the already-recorded
nonzero polynomial coordinate with its common `x₀` monomial removed. -/
theorem FirstKeyMaximalVectorLongitudinalFactorData.exists_transverseProfile_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    ∃ j : Fin 3, F.transverseProfile j ≠ 0 := by
  rcases F.transverse_nonzero with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro hprofile
  apply hj
  apply (MvPolynomial.finSuccEquiv K 3).injective
  have hcoeff :
      ((MvPolynomial.finSuccEquiv K 3
        (L.maximalHomogeneousVector j.succ)).coeff F.exponent) = 0 := by
    simpa [FirstKeyMaximalVectorLongitudinalFactorData.transverseProfile] using hprofile
  rw [F.transverseFactor j, hcoeff]
  simp

/-- If a radial branch has no longitudinal source power, then its transverse
first-key degree is forced to be one. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_sourceExponent_zero_implies_degree_one
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hrad : D.eulerCorrectedVector F = 0)
    (he : D.sourceExponent = 0) :
    D.transverseDegree = 1 := by
  have hmpos := D.transverseDegree_pos
  rcases F.exists_transverseProfile_ne_zero with ⟨j, hBj⟩
  by_contra hne
  have hm2 : 2 ≤ D.transverseDegree := by omega
  have hrel := D.radial_relation F hrad j
  rw [he] at hrel
  simp only [Nat.cast_zero, MvPolynomial.C_0, zero_mul, add_zero] at hrel
  have hm1ne : D.transverseDegree - 1 ≠ 0 := by omega
  have hcast : ((D.transverseDegree - 1 : ℕ) : K) ≠ 0 :=
    (Nat.cast_ne_zero).2 hm1ne
  have hC :
      (MvPolynomial.C ((D.transverseDegree - 1 : ℕ) : K) :
        MvPolynomial (Fin 3) K) ≠ 0 := by
    simpa using hcast
  exact hBj ((mul_eq_zero.mp hrel).resolve_left hC)

/-- Therefore every genuinely higher-degree radial branch has positive
longitudinal source exponent. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_sourceExponent_pos_of_two_le
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hrad : D.eulerCorrectedVector F = 0)
    (hm2 : 2 ≤ D.transverseDegree) :
    0 < D.sourceExponent := by
  by_contra hnot
  have he : D.sourceExponent = 0 := Nat.eq_zero_of_not_pos hnot
  have hm1 := D.radial_sourceExponent_zero_implies_degree_one F hrad he
  omega

/-- In the strict higher-degree radial branch the longitudinal profile `A`
cannot vanish, because at least one transverse profile survives. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_longitudinalProfile_ne_zero_of_two_le
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hrad : D.eulerCorrectedVector F = 0)
    (hm2 : 2 ≤ D.transverseDegree) :
    F.longitudinalProfile ≠ 0 := by
  rcases F.exists_transverseProfile_ne_zero with ⟨j, hBj⟩
  intro hA
  have hrel := D.radial_relation F hrad j
  rw [hA] at hrel
  simp only [mul_zero, zero_mul, add_zero] at hrel
  have hm1ne : D.transverseDegree - 1 ≠ 0 := by omega
  have hcast : ((D.transverseDegree - 1 : ℕ) : K) ≠ 0 :=
    (Nat.cast_ne_zero).2 hm1ne
  have hC :
      (MvPolynomial.C ((D.transverseDegree - 1 : ℕ) : K) :
        MvPolynomial (Fin 3) K) ≠ 0 := by
    simpa using hcast
  exact hBj ((mul_eq_zero.mp hrel).resolve_left hC)

/-- Exact residual normal form of a radial branch which is not already
transverse degree one. -/
structure FirstKeyStrictRadialProfileData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  sourceExponent_pos : 0 < D.sourceExponent
  transverseDegree_two_le : 2 ≤ D.transverseDegree
  longitudinalProfile_ne_zero : F.longitudinalProfile ≠ 0
  radialRelation :
    ∀ j : Fin 3,
      MvPolynomial.C ((D.transverseDegree - 1 : ℕ) : K) *
            F.transverseProfile j +
          MvPolynomial.C (D.sourceExponent : K) *
            F.longitudinalProfile * MvPolynomial.X j = 0

/-- A radial B14 branch is either already degree-one or has the unique strict
normal form above. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.radial_degreeOne_or_strict
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (hrad : D.eulerCorrectedVector F = 0) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyStrictRadialProfileData D F) := by
  by_cases hm1 : D.transverseDegree = 1
  · exact Or.inl hm1
  · right
    have hmpos := D.transverseDegree_pos
    have hm2 : 2 ≤ D.transverseDegree := by omega
    exact ⟨{
      sourceExponent_pos := D.radial_sourceExponent_pos_of_two_le F hrad hm2
      transverseDegree_two_le := hm2
      longitudinalProfile_ne_zero :=
        D.radial_longitudinalProfile_ne_zero_of_two_le F hrad hm2
      radialRelation := D.radial_relation F hrad
    }⟩

/-- **Stage 4B15 exact three-way transverse frontier.**

After B14 there are only three possibilities:

1. the transverse first-key profile has degree one;
2. the kernel is radial in the strict `e>0`, `m>=2`, `A!=0` normal form;
3. the transverse profile carries a genuine nonzero Hessian-kernel vector.

No classification is asserted here beyond what the preceding algebra proves.
The next provenance theorem only has to eliminate/repair the single strict
radial normal form and classify the genuine nonradial kernel branch. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_strictRadial_or_nonradialKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyStrictRadialProfileData D F) ∨
      Nonempty (C.FirstKeyNonradialTransverseKernelData D F) := by
  rcases D.radial_or_nonradialKernel F with hrad | hnon
  · rcases D.radial_degreeOne_or_strict F hrad with hlin | hstrict
    · exact Or.inl hlin
    · exact Or.inr (Or.inl hstrict)
  · exact Or.inr (Or.inr hnon)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
