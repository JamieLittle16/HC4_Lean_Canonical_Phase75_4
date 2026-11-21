import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceReverseRees
import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import HC4.Valuation.RankOneSpecialFiberFirstBreak
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# First rank-two break from a singleton `.pr` highest slice

The direct source exposure and reverse-Rees adapter give an honest polynomial
family whose special fibre is the stored highest pair slice and whose Hessian
determinant is a positive power of the Rees parameter.

For a singleton slice, if one coordinate `a` occurs with exponent at least two
and a distinct coordinate `k` is absent, then:

* the `k`-th special-fibre Hessian row is zero;
* the `a,a` special-fibre Hessian entry is nonzero;
* the full Rees Hessian cannot keep the `k`-th row identically zero, because
  its determinant is a nonzero parameter monomial.

Moving `k` to the last slot therefore puts us exactly in the hypotheses of the
existing rank-one-special-fibre first-break theorem.  The conclusion is
concrete rank-two geometry at the first actual opening layer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero monomial with exponent at least two in coordinate `i` has a
nonzero Hessian diagonal entry in that coordinate. -/
theorem hessian_monomial_diagonal_ne_zero_of_two_le
    {d : Fin 4 →₀ ℕ} {c : K} {i : Fin 4}
    (hc : c ≠ 0) (hi : 2 ≤ d i) :
    HC4.Polynomial.hessian (MvPolynomial.monomial d c) i i ≠ 0 := by
  have hh := HC4.Polynomial.eval_one_hessian_monomial (K := K) d c
  have hii := congrFun (congrFun hh i) i
  have hval :
      MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
          (HC4.Polynomial.hessian (MvPolynomial.monomial d c) i i) =
        c * ((d i : K) * (d i : K) - (d i : K)) := by
    change MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (HC4.Polynomial.hessian (MvPolynomial.monomial d c) i i) =
      (c • HC4.Polynomial.exponentHessianCore (K := K) d) i i at hii
    simpa [HC4.Polynomial.exponentHessianCore] using hii
  have hdi : (d i : K) ≠ 0 := by
    exact_mod_cast (show d i ≠ 0 by omega)
  have hdim1 : (d i : K) - 1 ≠ 0 := by
    intro hz
    have hone : (d i : K) = 1 := sub_eq_zero.mp hz
    have honeNat : d i = 1 := by exact_mod_cast hone
    omega
  have hscalar :
      c * ((d i : K) * (d i : K) - (d i : K)) ≠ 0 := by
    have hfactor :
        (d i : K) * (d i : K) - (d i : K) =
          (d i : K) * ((d i : K) - 1) := by ring
    rw [hfactor]
    exact mul_ne_zero hc (mul_ne_zero hdi hdim1)
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun _ : Fin 4 => (1 : K))) hzero
  rw [hval] at heval
  simp only [map_zero] at heval
  exact hscalar heval

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrHighestSliceSourceExposure

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}

/-- Layer zero of the honest reverse Rees is the stored highest slice. -/
theorem reverseReesFamily_layer_zero
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    familyParameterLayer E.reverseReesFamily 0 = S.slice := by
  calc
    familyParameterLayer E.reverseReesFamily 0 =
        polynomialFamilySpecialFiber E.reverseReesFamily := by
      ext d
      rw [familyParameterLayer_coeff, coeff_polynomialFamilySpecialFiber]
    _ = S.slice := E.reverseReesFamily_specialFiber

/-- A nonzero pure determinant clock prevents any reindexed Hessian row from
remaining identically zero. -/
theorem kernelLastBlock_kernelRow_ne_zero
    (E : QsOtherFacetPrHighestSliceSourceExposure P S)
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
  simp only [not_or] at hnot
  have hdet0 : B.determinantCore = 0 := by
    rcases hnot with ⟨hq, hs, hy, hz⟩
    unfold GeneralFourBlock.determinantCore
    rw [hq, hs, hy, hz]
    ring
  rw [hdet0] at hdet
  have hX :
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta ≠ 0 := by
    exact pow_ne_zero _ (by simp)
  exact hX hdet.symm

/-- A missing singleton coordinate gives zero constant coefficient in every
entry of the corresponding reindexed kernel row. -/
theorem kernelLastBlock_kernelRow_coeff_zero
    (E : QsOtherFacetPrHighestSliceSourceExposure P S)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d})
    (k : Fin 4) (hk : d k = 0) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    B.q.coeff 0 = 0 ∧ B.s.coeff 0 = 0 ∧
      B.y.coeff 0 = 0 ∧ B.z.coeff 0 = 0 := by
  classical
  let rho := kernelLastPerm k
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  have hd : d ∈ S.slice.support := by rw [hsupp]; simp
  have hc : MvPolynomial.coeff d S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hmono :
      S.slice = MvPolynomial.monomial d (MvPolynomial.coeff d S.slice) := by
    have hsum := MvPolynomial.as_sum S.slice
    rw [hsupp] at hsum
    simpa using hsum
  have hkernel : MvPolynomial.pderiv k S.slice = 0 := by
    rw [hmono, MvPolynomial.pderiv_monomial, hk]
    simp
  have hentry (j : Fin 4) :
      (parameterFirstHessian E.reverseReesFamily (rho j) (rho 3)).coeff 0 = 0 := by
    have hlast : rho (3 : Fin 4) = k := by simp [rho, kernelLastPerm]
    rw [hlast, parameterFirstHessian_symmetric]
    rw [parameterFirstHessian_coeff, E.reverseReesFamily_layer_zero]
    have h := congrArg (MvPolynomial.pderiv (rho j)) hkernel
    simpa [HC4.Polynomial.hessian_apply] using h
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

/-- A singleton coordinate with exponent at least two gives a nonzero active
special-fibre diagonal after the absent kernel coordinate is moved last. -/
theorem kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
    (E : QsOtherFacetPrHighestSliceSourceExposure P S)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d})
    (a k : Fin 4) (hak : a ≠ k) (ha : 2 ≤ d a) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
  classical
  let rho := kernelLastPerm k
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let j : Fin 4 := rho.symm a
  have hrhoj : rho j = a := by simp [j]
  have hjne : j ≠ (3 : Fin 4) := by
    intro hj
    have h := hrhoj
    rw [hj, kernelLastPerm_last] at h
    exact hak h.symm
  have hd : d ∈ S.slice.support := by rw [hsupp]; simp
  have hc : MvPolynomial.coeff d S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hmono :
      S.slice = MvPolynomial.monomial d (MvPolynomial.coeff d S.slice) := by
    have hsum := MvPolynomial.as_sum S.slice
    rw [hsupp] at hsum
    simpa using hsum
  have hdiag : HC4.Polynomial.hessian S.slice a a ≠ 0 := by
    rw [hmono]
    exact hessian_monomial_diagonal_ne_zero_of_two_le hc ha
  have hentry :
      (parameterFirstHessian E.reverseReesFamily a a).coeff 0 ≠ 0 := by
    rw [parameterFirstHessian_coeff, E.reverseReesFamily_layer_zero]
    exact hdiag
  have hentry' :
      (parameterFirstHessian E.reverseReesFamily (rho j) (rho j)).coeff 0 ≠ 0 := by
    simpa [hrhoj] using hentry
  dsimp [B]
  fin_cases j
  · exact Or.inl (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 0) (rho 0)).coeff 0 ≠ 0
      exact hentry')
  · exact Or.inr (Or.inl (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 1) (rho 1)).coeff 0 ≠ 0
      exact hentry'))
  · exact Or.inr (Or.inr (by
      change
        (parameterFirstHessian E.reverseReesFamily (rho 2) (rho 2)).coeff 0 ≠ 0
      exact hentry'))
  · exact (hjne rfl).elim

/-- **Singleton highest-slice first-break closure.** -/
noncomputable def singleton_firstBreakRankTwoOutcome
    (E : QsOtherFacetPrHighestSliceSourceExposure P S)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d})
    (a k : Fin 4) (hak : a ≠ k)
    (ha : 2 ≤ d a) (hk : d k = 0) :
    let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
    let hrow := E.kernelLastBlock_kernelRow_ne_zero k
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  let B := kernelLastFamilyHessianFourBlock E.reverseReesFamily k
  let hrow := E.kernelLastBlock_kernelRow_ne_zero k
  have hzero := E.kernelLastBlock_kernelRow_coeff_zero hsupp k hk
  have hactive :=
    E.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero hsupp a k hak ha
  exact rankOneSpecialFiber_firstKernelRowBreak_rankTwo
    B hrow hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2 hactive

end QsOtherFacetPrHighestSliceSourceExposure
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
