import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointReverseRees
import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import HC4.Valuation.RankOneSpecialFiberFirstBreak
import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# First rank-two break from a pure lower-ray facet endpoint

The honest endpoint reverse-Rees family has a pure monomial special fibre and
a nonzero positive-power Hessian determinant.  A missing coordinate therefore
starts as a literal Hessian-kernel row but cannot remain zero through the whole
family.  Any coordinate occurring with exponent at least two supplies the
nonzero active special-fibre diagonal required by the generic rank-one first-
break theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsRayFacetEndpointSourceExposure

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Layer zero of the endpoint Rees family is its pure endpoint monomial. -/
theorem reverseReesFamily_layer_zero
    (E : QsRayFacetEndpointSourceExposure C) :
    familyParameterLayer E.reverseReesFamily 0 =
      MvPolynomial.monomial C.ray.facetExponent
        (MvPolynomial.coeff C.ray.facetExponent
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) := by
  calc
    familyParameterLayer E.reverseReesFamily 0 =
        polynomialFamilySpecialFiber E.reverseReesFamily := by
      ext d
      rw [familyParameterLayer_coeff, coeff_polynomialFamilySpecialFiber]
      simp [Polynomial.constantCoeff]
    _ = _ := E.reverseReesFamily_specialFiber

/-- The positive pure determinant clock prevents the reindexed kernel row from
remaining identically zero. -/
theorem kernelLastBlock_kernelRow_ne_zero
    (E : QsRayFacetEndpointSourceExposure C)
    (k : Fin 4) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    B.q ≠ 0 ∨ B.s ≠ 0 ∨ B.y ≠ 0 ∨ B.z ≠ 0 := by
  let rho := kernelLastPerm k
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let Delta := 4 * E.natLevel - 2 * ∑ i : Fin 4, E.natWeight i
  have hdet :
      B.determinantCore =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
    dsimp [B, rho]
    simpa [kernelLastFamilyHessianFourBlock,
      kernelLastParameterFirstHessian, permutedFamilyHessianFourBlock] using
      (permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
        (kernelLastPerm k) E.reverseReesFamily
        E.reverseReesFamily_hasHessianDefect)
  by_contra hnot
  push_neg at hnot
  have hdet0 : B.determinantCore = 0 := by
    rcases hnot with ⟨hq, hs, hy, hz⟩
    unfold GeneralFourBlock.determinantCore
    rw [hq, hs, hy, hz]
    ring
  rw [hdet0] at hdet
  have hX :
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta ≠ 0 :=
    pow_ne_zero _ (by simp)
  exact hX hdet.symm

/-- A coordinate absent from the pure endpoint monomial gives zero constant
coefficient in every entry of its reindexed Hessian kernel row. -/
theorem kernelLastBlock_kernelRow_coeff_zero
    (E : QsRayFacetEndpointSourceExposure C)
    (k : Fin 4) (hk : C.ray.facetExponent k = 0) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    B.q.coeff 0 = 0 ∧ B.s.coeff 0 = 0 ∧
      B.y.coeff 0 = 0 ∧ B.z.coeff 0 = 0 := by
  let rho := kernelLastPerm k
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let d := C.ray.facetExponent
  let c := MvPolynomial.coeff d
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  have hkernel :
      MvPolynomial.pderiv k (MvPolynomial.monomial d c) = 0 := by
    rw [MvPolynomial.pderiv_monomial, hk]
    simp
  have hentry (j : Fin 4) :
      (parameterFirstHessian E.reverseReesFamily (rho j) (rho 3)).coeff 0 = 0 := by
    have hlast : rho (3 : Fin 4) = k := by simp [rho, kernelLastPerm]
    rw [hlast, parameterFirstHessian_symmetric]
    rw [parameterFirstHessian_coeff, E.reverseReesFamily_layer_zero]
    have h := congrArg (MvPolynomial.pderiv (rho j)) hkernel
    simpa [d, c, HC4.Polynomial.hessian_apply] using h
  dsimp [B]
  constructor
  · change
      (parameterFirstHessian E.reverseReesFamily (rho 0) (rho 3)).coeff 0 = 0
    exact hentry 0
  constructor
  · change
      (parameterFirstHessian E.reverseReesFamily (rho 1) (rho 3)).coeff 0 = 0
    exact hentry 1
  constructor
  · change
      (parameterFirstHessian E.reverseReesFamily (rho 2) (rho 3)).coeff 0 = 0
    exact hentry 2
  · change
      (parameterFirstHessian E.reverseReesFamily (rho 3) (rho 3)).coeff 0 = 0
    exact hentry 3

/-- A coordinate occurring at least twice in the pure endpoint gives a nonzero
active special-fibre diagonal after the absent kernel coordinate is moved last. -/
theorem kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
    (E : QsRayFacetEndpointSourceExposure C)
    (a k : Fin 4) (hak : a ≠ k) (ha : 2 ≤ C.ray.facetExponent a) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
  let rho := kernelLastPerm k
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let d := C.ray.facetExponent
  let c := MvPolynomial.coeff d
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  let j : Fin 4 := rho.symm a
  have hrhoj : rho j = a := by simp [j]
  have hjne : j ≠ (3 : Fin 4) := by
    intro hj
    have h := hrhoj
    rw [hj, kernelLastPerm_last] at h
    exact hak h.symm
  have hdSource :
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support := by
    have hset := E.exposed.subset (show d ∈ ({d} : Set (Fin 4 →₀ ℕ)) by simp)
    simpa [d] using hset
  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp hdSource
  have hdMon :
      d ∈ (MvPolynomial.monomial d c).support := by
    rw [MvPolynomial.mem_support_iff]
    simp [hc]
  have hdiag :
      HC4.Polynomial.hessian (MvPolynomial.monomial d c) a a ≠ 0 := by
    simpa [HC4.Polynomial.hessian_apply] using
      (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (K := K) a (MvPolynomial.monomial d c) d hdMon ha)
  have hentry :
      (parameterFirstHessian E.reverseReesFamily a a).coeff 0 ≠ 0 := by
    rw [parameterFirstHessian_coeff, E.reverseReesFamily_layer_zero]
    exact hdiag
  have hentry' :
      (parameterFirstHessian E.reverseReesFamily (rho j) (rho j)).coeff 0 ≠ 0 := by
    simpa [hrhoj] using hentry
  dsimp [B]
  by_cases hj0 : j = (0 : Fin 4)
  · exact Or.inl (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 0) (rho 0)).coeff 0 ≠ 0
      simpa [hj0] using hentry')
  by_cases hj1 : j = (1 : Fin 4)
  · exact Or.inr (Or.inl (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 1) (rho 1)).coeff 0 ≠ 0
      simpa [hj1] using hentry'))
  by_cases hj2 : j = (2 : Fin 4)
  · exact Or.inr (Or.inr (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 2) (rho 2)).coeff 0 ≠ 0
      simpa [hj2] using hentry'))
  have hj0v : j.val ≠ 0 := by
    intro h
    apply hj0
    apply Fin.ext
    simpa using h
  have hj1v : j.val ≠ 1 := by
    intro h
    apply hj1
    apply Fin.ext
    simpa using h
  have hj2v : j.val ≠ 2 := by
    intro h
    apply hj2
    apply Fin.ext
    simpa using h
  have hj3 : j = (3 : Fin 4) := by
    apply Fin.ext
    simp
    omega
  exact (hjne hj3).elim

/-- **Pure endpoint first-break closure.** -/
noncomputable def firstBreakRankTwoOutcome
    (E : QsRayFacetEndpointSourceExposure C)
    (a k : Fin 4) (hak : a ≠ k)
    (ha : 2 ≤ C.ray.facetExponent a)
    (hk : C.ray.facetExponent k = 0) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    let hrow := E.kernelLastBlock_kernelRow_ne_zero k
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let hrow := E.kernelLastBlock_kernelRow_ne_zero k
  have hzero := E.kernelLastBlock_kernelRow_coeff_zero k hk
  have hactive := E.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero a k hak ha
  exact rankOneSpecialFiber_firstKernelRowBreak_rankTwo
    B hrow hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2 hactive

end QsRayFacetEndpointSourceExposure
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
