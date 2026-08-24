import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTransverseReesKernel
import Mathlib.Tactic

/-!
# Stage 4B35: the B8 shifted leading vector is the first coefficient of the Rees kernel

B34 transports an honest source-coordinate Hessian kernel to the transverse
Rees family, with the complementary scaling

    W^R = (tau W_0(x_0,tau x_perp), W_1(...), W_2(...), W_3(...)).

B8 selected the source-kernel leading vector using the shifted weight

    beta = max (wt(d) - wt(j)).

For the weight `wt(0)=0`, `wt(1)=wt(2)=wt(3)=-1`, the ordinary Rees order of
one monomial in coordinate `j` is exactly

    1 - (wt(d) - wt(j)).

Consequently the least Rees order is `r = 1 - beta`, every lower coefficient
of the rescaled Rees kernel vanishes, and the coefficient at `r` is literally
B8's `shiftedSourceVectorLeading`.

This is the exact normalisation needed by the final first-projective-departure
calculation.  In particular there is no arbitrary shift and no identification
with the original closing-family parameter clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Extra ordinary Rees power inserted in one vector coordinate. -/
def transverseReesKernelParameterShift (j : Fin 4) : ℕ :=
  if j = 0 then 1 else 0

@[simp] theorem transverseReesKernelParameterShift_zero :
    transverseReesKernelParameterShift (0 : Fin 4) = 1 := by
  simp [transverseReesKernelParameterShift]

@[simp] theorem transverseReesKernelParameterShift_succ (j : Fin 3) :
    transverseReesKernelParameterShift j.succ = 0 := by
  simp [transverseReesKernelParameterShift]

/-- The polynomial scaling from B34 is exactly the corresponding monomial
`X^shift`. -/
theorem transverseReesKernelScale_eq_X_pow_shift
    (j : Fin 4) :
    transverseReesKernelScale (K := K) j =
      Polynomial.X ^ transverseReesKernelParameterShift j := by
  fin_cases j <;>
    simp [transverseReesKernelScale, transverseReesKernelParameterShift]

/-- Source-monomial/parameter coefficient formula for the rescaled Rees
kernel.  A source monomial of transverse degree `q` in coordinate `j` occurs
at ordinary Rees order `q + shift(j)`. -/
theorem coeff_coeff_transverseSourceReesKernel
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (n : ℕ) :
    (MvPolynomial.coeff d (transverseSourceReesKernel W j)).coeff n =
      if pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j = n then
        MvPolynomial.coeff d (W j)
      else 0 := by
  rw [transverseSourceReesKernel]
  rw [MvPolynomial.coeff_C_mul]
  rw [coeff_transverseSourceReesFamily]
  rw [transverseReesKernelScale_eq_X_pow_shift]
  rw [← mul_assoc, ← pow_add]
  rw [Nat.add_comm (transverseReesKernelParameterShift j)
    (pureLongitudinalTransverseDegree d)]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hdn :
      pureLongitudinalTransverseDegree d +
          transverseReesKernelParameterShift j = n
  · subst n
    simp
  · have hlt_or_gt :
        n < pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j ∨
          pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j < n := by
      omega
    rcases hlt_or_gt with hlt | hgt
    · simp [Nat.not_le.mpr hlt, hdn]
    · have hle :
          pureLongitudinalTransverseDegree d +
              transverseReesKernelParameterShift j ≤ n := Nat.le_of_lt hgt
      have hsubpos :
          0 < n - (pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j) := by
        omega
      simp [hle, hdn, Polynomial.coeff_C, Nat.ne_of_gt hsubpos]

/-- Parameter layer of the complete rescaled Rees kernel vector. -/
noncomputable def transverseSourceReesKernelLayer
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (n : ℕ) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  fun j => familyParameterLayer (transverseSourceReesKernel W j) n

/-- Every shifted source weight is at most `1`; hence B8's maximal shifted
weight is at most `1` as well. -/
theorem shiftedSourceVectorTopWeight_le_one
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    shiftedSourceVectorTopWeight W hW ≤ 1 := by
  have htop := shiftedSourceVectorTopWeight_mem W hW
  unfold shiftedSourceVectorWeightSupport at htop
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at htop
  rcases htop with ⟨j, hj⟩
  rcases Finset.mem_image.mp hj with ⟨d, _hd, hweight⟩
  rw [← hweight]
  rw [weight_pureLongitudinalTransverseWeight]
  fin_cases j <;>
    simp [pureLongitudinalTransverseWeight] <;> omega

/-- First ordinary parameter order of the rescaled Rees kernel.  The `toNat`
is harmless because the preceding theorem proves `1 - beta >= 0`. -/
noncomputable def transverseSourceReesKernelLeadingOrder
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) : ℕ :=
  (1 - shiftedSourceVectorTopWeight W hW).toNat

/-- Integer form of the defining order identity. -/
theorem transverseSourceReesKernelLeadingOrder_cast
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    (transverseSourceReesKernelLeadingOrder W hW : ℤ) =
      1 - shiftedSourceVectorTopWeight W hW := by
  unfold transverseSourceReesKernelLeadingOrder
  exact Int.toNat_of_nonneg (by
    have h := shiftedSourceVectorTopWeight_le_one W hW
    omega)

/-- The B34 Rees order of a source monomial is `1` minus its B8 shifted
weight. -/
theorem transverseDegree_add_kernelShift_eq_one_sub_shiftedWeight
    (j : Fin 4)
    (d : Fin 4 →₀ ℕ) :
    (pureLongitudinalTransverseDegree d +
        transverseReesKernelParameterShift j : ℤ) =
      1 -
        (Finsupp.weight pureLongitudinalTransverseWeight d -
          pureLongitudinalTransverseWeight j) := by
  rw [weight_pureLongitudinalTransverseWeight]
  fin_cases j <;>
    simp [transverseReesKernelParameterShift,
      pureLongitudinalTransverseWeight] <;> omega

/-- **Exact B8/B34 identification.**

The first nonzero ordinary coefficient vector of the rescaled polynomial Rees
kernel is literally the derivative-shifted leading vector selected in B8. -/
theorem transverseSourceReesKernelLayer_leadingOrder
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    transverseSourceReesKernelLayer W
        (transverseSourceReesKernelLeadingOrder W hW) =
      shiftedSourceVectorLeading W hW := by
  funext j
  ext d
  rw [transverseSourceReesKernelLayer]
  rw [familyParameterLayer_coeff]
  rw [coeff_coeff_transverseSourceReesKernel]
  rw [shiftedSourceVectorLeading, coeff_initialForm]
  have horder := transverseSourceReesKernelLeadingOrder_cast W hW
  have hrees := transverseDegree_add_kernelShift_eq_one_sub_shiftedWeight j d
  by_cases hshift :
      Finsupp.weight pureLongitudinalTransverseWeight d -
          pureLongitudinalTransverseWeight j =
        shiftedSourceVectorTopWeight W hW
  · have hparam :
        pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j =
          transverseSourceReesKernelLeadingOrder W hW := by
      exact_mod_cast (by omega :
        (pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j : ℤ) =
          (transverseSourceReesKernelLeadingOrder W hW : ℤ))
    rw [if_pos hparam]
    have hweight :
        Finsupp.weight pureLongitudinalTransverseWeight d =
          shiftedSourceVectorTopWeight W hW +
            pureLongitudinalTransverseWeight j := by
      omega
    rw [if_pos hweight]
  · have hparam :
        pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j ≠
          transverseSourceReesKernelLeadingOrder W hW := by
      intro hparam
      apply hshift
      have hparamZ :
          (pureLongitudinalTransverseDegree d +
              transverseReesKernelParameterShift j : ℤ) =
            (transverseSourceReesKernelLeadingOrder W hW : ℤ) := by
        exact_mod_cast hparam
      omega
    rw [if_neg hparam]
    have hweight :
        Finsupp.weight pureLongitudinalTransverseWeight d ≠
          shiftedSourceVectorTopWeight W hW +
            pureLongitudinalTransverseWeight j := by
      intro h
      apply hshift
      omega
    rw [if_neg hweight]

/-- Every Rees-kernel coefficient strictly before the B8 leading order
vanishes. -/
theorem transverseSourceReesKernelLayer_eq_zero_of_lt_leadingOrder
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0)
    {n : ℕ}
    (hn : n < transverseSourceReesKernelLeadingOrder W hW) :
    transverseSourceReesKernelLayer W n = 0 := by
  funext j
  apply MvPolynomial.ext
  intro d
  rw [transverseSourceReesKernelLayer]
  rw [familyParameterLayer_coeff]
  rw [coeff_coeff_transverseSourceReesKernel]
  change (if pureLongitudinalTransverseDegree d +
      transverseReesKernelParameterShift j = n then
    MvPolynomial.coeff d (W j) else 0) = 0
  by_cases hcoeff : MvPolynomial.coeff d (W j) = 0
  · simp [hcoeff]
  · have hdmem : d ∈ (W j).support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hmem := shiftedSourceVectorWeight_mem W j d hdmem
    have hle :
        Finsupp.weight pureLongitudinalTransverseWeight d -
            pureLongitudinalTransverseWeight j ≤
          shiftedSourceVectorTopWeight W hW := by
      unfold shiftedSourceVectorTopWeight
      exact Finset.le_max' _ _ hmem
    have hrees := transverseDegree_add_kernelShift_eq_one_sub_shiftedWeight j d
    have horder := transverseSourceReesKernelLeadingOrder_cast W hW
    have hnot :
        pureLongitudinalTransverseDegree d +
            transverseReesKernelParameterShift j ≠ n := by
      intro heq
      have heqZ :
          (pureLongitudinalTransverseDegree d +
              transverseReesKernelParameterShift j : ℤ) = (n : ℤ) := by
        exact_mod_cast heq
      omega
    rw [if_neg hnot]

/-- Hence the selected leading Rees-kernel coefficient is genuinely nonzero. -/
theorem transverseSourceReesKernelLayer_leadingOrder_ne_zero
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hW : W ≠ 0) :
    transverseSourceReesKernelLayer W
        (transverseSourceReesKernelLeadingOrder W hW) ≠ 0 := by
  rw [transverseSourceReesKernelLayer_leadingOrder W hW]
  exact shiftedSourceVectorLeading_ne_zero W hW

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Carrier-facing form for the exact B30-provenanced kernel.  B34's
polynomial Rees kernel begins with exactly B8's retained `leadingVector`. -/
theorem FirstKeyCanonicalRS2ProvenanceAssemblyData.reesKernel_firstLayer
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData) :
    transverseSourceReesKernelLayer A.leading.sourceKernel.vector
        (transverseSourceReesKernelLeadingOrder
          A.leading.sourceKernel.vector A.leading.sourceKernel.vector_ne_zero) =
      A.leading.leadingVector := by
  rw [transverseSourceReesKernelLayer_leadingOrder]
  exact A.leading.leading_eq.symm

/-- All lower rescaled Rees-kernel layers vanish for the same retained
source-coordinate kernel. -/
theorem FirstKeyCanonicalRS2ProvenanceAssemblyData.reesKernel_lowerLayers_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData)
    {n : ℕ}
    (hn : n < transverseSourceReesKernelLeadingOrder
      A.leading.sourceKernel.vector A.leading.sourceKernel.vector_ne_zero) :
    transverseSourceReesKernelLayer A.leading.sourceKernel.vector n = 0 := by
  exact transverseSourceReesKernelLayer_eq_zero_of_lt_leadingOrder
    A.leading.sourceKernel.vector A.leading.sourceKernel.vector_ne_zero hn

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
