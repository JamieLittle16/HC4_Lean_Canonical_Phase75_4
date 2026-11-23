import HC4.Polynomial.RankTwoKernelSecondVariation
import Mathlib.Tactic

/-!
# Rank-two kernel-block constraint from only the second determinant coefficient

The existing rank-two second-jet theorem required the determinant
of an entire polynomial matrix to vanish identically. For a cubic
Hessian source, the normalized determinant is generally a NONZERO
high-degree monomial, not the zero polynomial. The relevant fact
is only that its parameter coefficient at twice the first positive
order vanishes.

We weaken the endpoint precisely to that coefficient equation,
without changing any base-block or no-small-parameter-term
hypothesis. This lemma is the appropriate algebraic input for
the forthcoming source-normalized rank-two second variation.
-/

namespace HC4.Polynomial

open scoped Matrix
noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000

/-- A four-by-four polynomial family whose constant block has
two-dimensional kernel, and whose entries have no positive parameter
terms below j, has singular j-th coefficient kernel block whenever
the determinant coefficient at order 2j vanishes.

Unlike the earlier version, det(M) need NOT be identically zero. -/
theorem kernelBlock_det_eq_zero_of_secondDetCoeff_gap_domain
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hgap : ∀ r s,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s,
      (M r s).coeff 0 = rankTwoZeroKernelBase a b c d r s)
    (htwo : (2 : R) ≠ 0)
    (hactive : a * d - b * c ≠ 0)
    (hcoeff : M.det.coeff (2 * j) = 0) :
    let B : Matrix (Fin 4) (Fin 4) R :=
      fun r s => (M r s).coeff j
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  let B : Matrix (Fin 4) (Fin 4) R :=
    fun r s => (M r s).coeff j
  let C : Matrix (Fin 4) (Fin 4) R :=
    fun r s => (M r s).coeff (2 * j)
  change B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0
  have hjet :
      HC4.Valuation.matrixParameterGapSecondJet hj M hgap =
        rankTwoZeroKernelSecondVariation a b c d B C := by
    apply Matrix.ext
    intro r s
    rw [HC4.Valuation.matrixParameterGapSecondJet_apply]
    simp [rankTwoZeroKernelSecondVariation, rankTwoSecondVariationEntry,
      B, C, hbase]
  have hbridge :=
    HC4.Valuation.snd_snd_det_matrixParameterGapSecondJet
      (R := R) hj M hgap
  have hzero :
      TrivSqZeroExt.snd
          (TrivSqZeroExt.snd
            (HC4.Valuation.matrixParameterGapSecondJet hj M hgap).det) = 0 := by
    rw [hbridge, hcoeff]
    simp
  rw [hjet] at hzero
  exact kernelBlock_det_eq_zero_of_secondVariation_eq_zero_domain
    B C htwo hactive hzero

/-- Characteristic-zero field specialization of the second-coefficient
rank-two kernel obstruction. -/
theorem kernelBlock_det_eq_zero_of_secondDetCoeff_gap
    {K : Type*} [Field K] [CharZero K]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hgap : ∀ r s,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : K)
    (hbase : ∀ r s,
      (M r s).coeff 0 = rankTwoZeroKernelBase a b c d r s)
    (hactive : a * d - b * c ≠ 0)
    (hcoeff : M.det.coeff (2 * j) = 0) :
    let B : Matrix (Fin 4) (Fin 4) K :=
      fun r s => (M r s).coeff j
    B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
  have htwo : (2 : K) ≠ 0 :=
    (Nat.cast_ne_zero).2 (by decide)
  exact kernelBlock_det_eq_zero_of_secondDetCoeff_gap_domain
    hj M hgap a b c d hbase htwo hactive hcoeff

end
end HC4.Polynomial
