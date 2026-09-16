import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRowBreak
import HC4.Valuation.CoordinateMaxKernelOpeningPureAxisHessian
import HC4.Valuation.RankOneSpecialFiberFirstBreak
import Mathlib.Tactic

/-!
# First-break closure of the A19.55 top-kernel linear-power residual

Suppose the actual maximal ordinary top face is

    a * L^D,

with `D >= 3`, and the stored kernel coordinate is absent from `L`.
Nonvanishing of the top face forces both `a != 0` and `L != 0`, so some
coordinate different from the kernel has a nonzero coefficient in `L`.  The
corresponding top-face Hessian diagonal is nonzero.

After moving the kernel coordinate to slot `3`, this gives one nonzero active
constant diagonal in the honest ordinary reverse-Rees family.  The previous
module gives a genuine kernel-row opening, and the generic rank-one-special-
fibre first-break theorem therefore supplies explicit rank-two geometry.

No auxiliary Rees order is compared with the zero blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}
variable (P : T.TopFaceLinearPowerKernelData kernelCoordinate)

/-- The scalar coefficient in the nonzero top-face linear power is nonzero. -/
theorem coefficient_ne_zero : P.coefficient ≠ 0 := by
  intro ha
  apply T.topFace.face_ne_zero
  rw [P.eq_power, ha]
  simp

/-- The linear form in the nonzero top face is nonzero. -/
theorem linearForm_ne_zero :
    gradientRatioLinearForm P.ratio ≠ 0 := by
  intro hL
  apply T.topFace.face_ne_zero
  rw [P.eq_power, hL]
  simp [show 0 < T.topFace.degree by omega]

/-- Some coordinate other than the stored kernel coordinate occurs genuinely
in the top linear form. -/
theorem exists_active_ratio_ne_zero :
    ∃ j : Fin 4, j ≠ kernelCoordinate ∧ P.ratio j ≠ 0 := by
  have hexists : ∃ j : Fin 4, P.ratio j ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply P.linearForm_ne_zero
    unfold gradientRatioLinearForm
    simp [hnone]
  rcases hexists with ⟨j, hj⟩
  have hjk : j ≠ kernelCoordinate := by
    intro h
    subst j
    exact hj P.kernel_ratio_zero
  exact ⟨j, hjk, hj⟩

/-- Any nonzero coefficient of the top linear form supplies a nonzero Hessian
diagonal on the degree-at-least-three top face. -/
theorem topFace_hessian_diagonal_ne_zero
    (j : Fin 4)
    (hj : P.ratio j ≠ 0) :
    HC4.Polynomial.hessian T.topFace.face j j ≠ 0 := by
  have hrepr : T.topFace.degree = (T.topFace.degree - 2) + 2 := by omega
  have ha : P.coefficient ≠ 0 := P.coefficient_ne_zero
  have hL : gradientRatioLinearForm P.ratio ≠ 0 := P.linearForm_ne_zero
  have hn2 : (((T.topFace.degree - 2 + 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show T.topFace.degree - 2 + 2 ≠ 0 by omega)
  have hn1 : (((T.topFace.degree - 2 + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show T.topFace.degree - 2 + 1 ≠ 0 by omega)
  rw [P.eq_power, hrepr]
  rw [hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin]
  apply mul_ne_zero
  · simp only [MvPolynomial.C_ne_zero]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hn2) hn1) hj) hj
  · exact pow_ne_zero _ hL

/-- After the honest kernel-last reindexing, some active constant Hessian
diagonal is nonzero. -/
theorem kernelLastBlock_activeDiagonal_coeff_zero_ne_zero :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
  rcases P.exists_active_ratio_ne_zero with ⟨j, hjk, hj⟩
  have hjdiag := P.topFace_hessian_diagonal_ne_zero j hj
  let rho := kernelLastPerm kernelCoordinate
  let r : Fin 4 := rho.symm j
  have hrho : rho r = j := by simp [r]
  have hrne : r ≠ (3 : Fin 4) := by
    intro hr
    have h := hrho
    rw [hr, kernelLastPerm_last] at h
    exact hjk h.symm
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hentry :
      (parameterFirstHessian T.topKernelReverseReesFamily
        (rho r) (rho r)).coeff 0 ≠ 0 := by
    rw [parameterFirstHessian_coeff]
    rw [T.topKernelReverseRees_layer_zero_eq_topFace]
    simpa [hrho] using hjdiag
  dsimp [B]
  fin_cases r
  · exact Or.inl (by
      change
        (parameterFirstHessian T.topKernelReverseReesFamily
          (rho 0) (rho 0)).coeff 0 ≠ 0
      exact hentry)
  · exact Or.inr (Or.inl (by
      change
        (parameterFirstHessian T.topKernelReverseReesFamily
          (rho 1) (rho 1)).coeff 0 ≠ 0
      exact hentry))
  · exact Or.inr (Or.inr (by
      change
        (parameterFirstHessian T.topKernelReverseReesFamily
          (rho 2) (rho 2)).coeff 0 ≠ 0
      exact hentry))
  · exact (hrne rfl).elim

/-- **Top-kernel linear-power closure.**  The honest ordinary reverse-Rees
family necessarily reaches concrete rank-two geometry at the first actual
opening of the stored top-face kernel row. -/
noncomputable def firstBreakRankTwoOutcome :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  have hzero :=
    T.topKernelLastBlock_kernelRow_coeff_zero kernelCoordinate
      (by
        rw [P.eq_power, MvPolynomial.pderiv_C_mul]
        have hmrepr :
            T.topFace.degree = (T.topFace.degree - 1) + 1 := by omega
        conv_lhs =>
          rhs
          rw [hmrepr]
        rw [pderiv_gradientRatioLinearForm_pow_succ]
        simp [P.kernel_ratio_zero])
  have hactive :
      B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
    dsimp [B]
    exact P.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
  exact rankOneSpecialFiber_firstKernelRowBreak_rankTwo
    B hrow hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2 hactive

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
