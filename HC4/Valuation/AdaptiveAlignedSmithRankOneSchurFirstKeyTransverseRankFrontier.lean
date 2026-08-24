import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyPureRadialElimination
import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Transverse rank frontier for the first Schur key

Stage 4B17 removes the Euler-radial obstruction and leaves only

    transverse degree one
    | genuine nonradial polynomial kernel of Hess(H).

The next distinction is the actual transverse Hessian rank.  We deliberately
make it division-free: rank at least two is witnessed by one nonzero `2 x 2`
minor, while the complementary branch records that every `2 x 2` minor
vanishes.

The rank-two witness is immediately coupled to the already-green finite
repair engine via `rankOne_to_rankTwo_repairProgress`; no new progress
relation is introduced.  The residual branch therefore contains exactly the
geometry that still needs classification:

    H != 0, homogeneous of degree m,
    a genuine nonradial Hessian kernel,
    every transverse 2 x 2 Hessian minor zero.

For `m = 1` we are already in the desired linear-form case.  Thus after this
file the only genuinely new algebra is the rank-at-most-one homogeneous
classification `H = c * L^m`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- A division-free witness that the Hessian of a ternary polynomial has
rank at least two: one `2 x 2` minor is nonzero. -/
def HasTransverseHessianRankTwoWitness
    (H : MvPolynomial (Fin 3) K) : Prop :=
  ∃ i j k l : Fin 3,
    HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
      HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j ≠ 0

/-- Division-free rank-at-most-one certificate for a ternary Hessian. -/
def HasTransverseHessianRankAtMostOne
    (H : MvPolynomial (Fin 3) K) : Prop :=
  ∀ i j k l : Fin 3,
    HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
      HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0

/-- Exhaustive finite determinantal split. -/
theorem transverseHessian_rankTwoWitness_or_rankAtMostOne
    (H : MvPolynomial (Fin 3) K) :
    HasTransverseHessianRankTwoWitness H ∨
      HasTransverseHessianRankAtMostOne H := by
  classical
  by_cases hall : HasTransverseHessianRankAtMostOne H
  · exact Or.inr hall
  · left
    unfold HasTransverseHessianRankAtMostOne at hall
    simp only [not_forall] at hall
    rcases hall with ⟨i, hi⟩
    rcases hi with ⟨j, hj⟩
    rcases hj with ⟨k, hk⟩
    rcases hk with ⟨l, hl⟩
    exact ⟨i, j, k, l, hl⟩

/-- Principal `2 x 2` relation extracted from the all-minors certificate. -/
theorem transverseHessian_principalMinor_eq_zero
    (H : MvPolynomial (Fin 3) K)
    (hall : HasTransverseHessianRankAtMostOne H)
    (i j : Fin 3) :
    HC4.Polynomial.hessian H i i * HC4.Polynomial.hessian H j j -
      HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H j i = 0 := by
  exact hall i i j j

/-- Three-index cross relation extracted from the all-minors certificate. -/
theorem transverseHessian_crossMinor_eq_zero
    (H : MvPolynomial (Fin 3) K)
    (hall : HasTransverseHessianRankAtMostOne H)
    (i j k : Fin 3) :
    HC4.Polynomial.hessian H i i * HC4.Polynomial.hessian H j k -
      HC4.Polynomial.hessian H i k * HC4.Polynomial.hessian H j i = 0 := by
  exact hall i i j k

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A first-key transverse rank-two witness, coupled immediately to the
existing certified rank-one -> rank-two finite-repair step. -/
structure FirstKeyTransverseRankTwoRepairData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (complexity : ℕ) where
  i : Fin 3
  j : Fin 3
  k : Fin 3
  l : Fin 3
  minor_ne_zero :
    HC4.Polynomial.hessian D.transverseSourceProfile i j *
          HC4.Polynomial.hessian D.transverseSourceProfile k l -
        HC4.Polynomial.hessian D.transverseSourceProfile i l *
          HC4.Polynomial.hessian D.transverseSourceProfile k j ≠ 0
  repairProgress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

/-- Construct the repair package from a geometric rank-two witness.  The
strict finite progress is the already-green canonical rank promotion. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.rankTwoRepairData_of_witness
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (complexity : ℕ)
    (h : HasTransverseHessianRankTwoWitness D.transverseSourceProfile) :
    Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) := by
  rcases h with ⟨i, j, k, l, hminor⟩
  have hprogress :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) :=
    rankOne_to_rankTwo_repairProgress complexity
  exact ⟨{
    i := i
    j := j
    k := k
    l := l
    minor_ne_zero := hminor
    repairProgress := hprogress
    measure_lt := repairState_measure_lt_of_progress hprogress
  }⟩

/-- The sole residual geometry after removing degree one and the actual
rank-two repair branch.  We retain the genuine B14 nonradial kernel instead
of forgetting why the transverse Hessian is singular. -/
structure FirstKeyTransverseRankOneResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  nonradial : C.FirstKeyNonradialTransverseKernelData D F
  allMinors : HasTransverseHessianRankAtMostOne D.transverseSourceProfile

/-- The residual branch still carries the nonzero homogeneous source profile
and its exact degree. -/
theorem FirstKeyTransverseRankOneResidualData.profile_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyTransverseRankOneResidualData D F) :
    D.transverseSourceProfile ≠ 0 := by
  exact D.transverseSourceProfile_ne_zero

/-- **Stage 4B18 transverse-rank frontier.**

B17 gives degree one or a genuine nonradial Hessian kernel.  In the latter
case we split on the finite `2 x 2` minors.  A nonzero minor is immediately a
certified rank-one -> rank-two repair at the existing complexity; if every
minor vanishes, all remaining information is retained in one rank-at-most-one
residual object.

No Hessian classification is reproved here. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_rankTwoRepair_or_rankOneResidual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyTransverseRankOneResidualData D F) := by
  rcases D.degreeOne_or_nonradialKernel F with hdegree | hnon
  · exact Or.inl hdegree
  · rcases hnon with ⟨N⟩
    rcases transverseHessian_rankTwoWitness_or_rankAtMostOne
        D.transverseSourceProfile with hrankTwo | hall
    · exact Or.inr (Or.inl (D.rankTwoRepairData_of_witness complexity hrankTwo))
    · exact Or.inr (Or.inr ⟨{
        nonradial := N
        allMinors := hall
      }⟩)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
