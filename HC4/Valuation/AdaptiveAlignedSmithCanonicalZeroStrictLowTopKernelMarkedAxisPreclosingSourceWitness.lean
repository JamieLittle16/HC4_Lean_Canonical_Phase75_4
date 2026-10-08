import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisPotentialTiming
import Mathlib.Tactic

/-!
# Reachable marked-axis first actual layer: represented-source witness

The canonical square arithmetic describes a non-integrality witness for an
*aligned square packet*, but the construction of that packet uses the
unreachable exact-closing clock.  To retain real information from the
strictly preclosing branch, return directly to the first actual coefficient
of the honest marked-axis reverse-Rees family.

This module lifts the first actual family coefficient to a **supported
monomial in the represented determinant-one source** and proves its exact
transverse degree:

    d_1 + d_2 + d_3 + j = D,

where D is the maximal top-face degree and j is the first actual parameter
order.  The ordinary-degree bound then implies d_0 <= j.

This holds for every actual singular terminal, without any E3 extractor,
canonical square, extra normalisation, terminal cocharacter or JC2 assumption.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The nonzero coefficient on the first positive marked-axis layer is already
a nonzero coefficient of the very same represented determinant-one source.
The reverse-Rees coefficient formula records its exact transverse degree,
and the source degree bound controls its longitudinal exponent. -/
theorem topKernelMarkedAxis_firstActual_exists_representedSourceWitness
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) +
          T.topKernelMarkedAxisFirstActualLayerOrder = T.topFace.degree ∧
        d (0 : Fin 4) ≤ T.topKernelMarkedAxisFirstActualLayerOrder := by
  let j : ℕ := T.topKernelMarkedAxisFirstActualLayerOrder
  rcases T.topKernelMarkedAxisFirstActualLayerOrder_realised with
    ⟨d, hfamily, hcoef⟩
  have hsource : d ∈ T.topKernelReesSource.support := by
    by_contra hnot
    have hfamilyZero :
        MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily = 0 := by
      rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
        reverseWeightedReesFamily_coeff, if_neg hnot]
    rw [hfamilyZero] at hcoef
    simp at hcoef
  have hweightLe :
      Finsupp.weight topKernelMarkedAxisNatWeight d ≤ T.topFace.degree :=
    T.topKernelReesSource_hasMarkedAxisReverseWeightBound d hsource
  let q : ℕ :=
    T.topFace.degree - Finsupp.weight topKernelMarkedAxisNatWeight d
  have hcoeff :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily =
        Polynomial.X ^ q *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
      reverseWeightedReesFamily_coeff, if_pos hsource]
    rfl
  have hq : q = j := by
    by_contra hne
    have hbad := hcoef
    rw [hcoeff, mul_comm, Polynomial.coeff_C_mul_X_pow] at hbad
    simp [j, hne, Ne.symm hne] at hbad
  have htrans :
      d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) +
        T.topKernelMarkedAxisFirstActualLayerOrder = T.topFace.degree := by
    have hw :=
      weight_topKernelMarkedAxisNatWeight d
    have hle :
        d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) ≤
          T.topFace.degree := by
      simpa [hw] using hweightLe
    dsimp [q] at hq
    rw [hw] at hq
    dsimp [j] at hq
    omega
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
    simpa [topKernelReesSource] using
      T.topFace.maximal d (by simpa [topKernelReesSource] using hsource)
  have hlong :
      d (0 : Fin 4) ≤ T.topKernelMarkedAxisFirstActualLayerOrder := by
    unfold HC4.Polynomial.ordinaryDegree4 at hdeg
    omega
  exact ⟨d, by simpa [topKernelReesSource] using hsource, htrans, hlong⟩

/-- In particular every actual marked-axis terminal has an honest represented
source monomial whose transverse degree lies strictly below the top degree,
with its longitudinal exponent bounded by the first positive layer. -/
theorem topKernelMarkedAxis_firstActual_exists_strictlyLowerTransverseWitness
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) <
        T.topFace.degree ∧
      d (0 : Fin 4) ≤ T.topKernelMarkedAxisFirstActualLayerOrder := by
  rcases T.topKernelMarkedAxis_firstActual_exists_representedSourceWitness with
    ⟨d, hd, hdegree, hlong⟩
  refine ⟨d, hd, ?_, hlong⟩
  have hjpos := T.topKernelMarkedAxisFirstActualLayerOrder_pos
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
