import HC4.Polynomial.OneZeroWeightTerminal
import HC4.Newton.TerminalCoordinatePermutation

/-!
# Exhaustive nonnegative zero-clock terminal

For four variables, positive cap and nonnegative weights, the
invertible leading Hessian gives a complementary permutation.
There are zero, one, or two zero-weight coordinates. In the last
case a coordinate permutation puts the actual source under the
standard two-zero cap, and the full-source planar endpoint applies.

No descent or extraction premise is hidden in the terminal theorem.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The actual maximal layer at clock zero has complementary
weight matching, with no conformal-face certificate required. -/
theorem zeroClock_has_complementWeightPermutation
    (w : Fin 4 → ℤ) (m : ℤ)
    (P : MvPolynomial (Fin 4) K) (hcap : IsWeightLE w m P)
    (hclock : (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w i) = 0)
    (hdet : hessianDeterminant P = 1) :
    HasTerminalComplementWeightPermutation w m := by
  classical
  let L := initialForm w m P
  have hL : hessianDeterminant L = 1 := by
    change hessianDeterminant (initialForm w m P) = 1
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap,
      hclock, hdet]
    exact initialForm_eq_self_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_one K w)
  let T := (hessian L).map (MvPolynomial.eval (0 : Fin 4 → K))
  have hT : T.det = 1 := by
    change ((MvPolynomial.eval (0 : Fin 4 → K)).mapMatrix (hessian L)).det = 1
    rw [← RingHom.map_det, show (hessian L).det = 1 from hL, map_one]
  obtain ⟨π, hπ⟩ := matrix4_det_ne_zero_exists_permutation_entries_ne_zero T
    (by rw [hT]; exact one_ne_zero)
  refine ⟨π, ?_⟩
  intro i
  by_contra hn
  apply hπ i
  change MvPolynomial.eval (0 : Fin 4 → K) (hessian L (π i) i) = 0
  have hh := hessian_entry_isWeightedHomogeneous
    (initialForm_isWeightedHomogeneous w m P) (π i) i
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  exact hh.coeff_eq_zero 0 (by rw [map_zero]; omega)

/-- Renaming the actual polynomial transports its weight cap. -/
theorem terminal_isWeightLE_rename_perm
    (w : Fin 4 → ℤ) (m : ℤ) (P : MvPolynomial (Fin 4) K)
    (hcap : IsWeightLE w m P) (rho : Equiv.Perm (Fin 4)) :
    IsWeightLE (fun i => w (rho.symm i)) m (rename rho P) := by
  classical
  intro u hu
  rw [MvPolynomial.support_rename_of_injective rho.injective] at hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  have he : Finsupp.weight (fun i => w (rho.symm i)) (Finsupp.mapDomain rho v) =
      Finsupp.weight w v := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply]
    rw [Finsupp.sum_fintype, Finsupp.sum_fintype]
    · simp only [Finsupp.mapDomain_equiv_apply]
      exact Equiv.sum_comp rho.symm (fun i : Fin 4 => v i • w i)
    · intro i
      simp
    · intro i
      simp
  rw [he]
  exact hcap hv

set_option maxHeartbeats 4000000 in
/-- Full-source injectivity at every nonnegative zero-clock
presentation of positive cap in four variables, under planar JC2. -/
theorem gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (w : Fin 4 → ℤ) (hw : ∀ i, 0 ≤ w i) (m : ℤ) (hm : 0 < m)
    (P : MvPolynomial (Fin 4) K) (hcap : IsWeightLE w m P)
    (hclock : (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w i) = 0)
    (hdet : hessianDeterminant P = 1) :
    Function.Injective (mvGradientMap P) := by
  classical
  by_cases hz : ∃ a : Fin 4, w a = 0
  · obtain ⟨a, ha⟩ := hz
    by_cases hu : ∀ i, w i = 0 → i = a
    · exact gradient_injective_of_oneZeroWeight_zeroClock w hw m a ha hu P hcap hclock hdet
    · push_neg at hu
      obtain ⟨b, hb, hba⟩ := hu
      let s : Equiv.Perm (Fin 4) := Equiv.swap a 0
      let rho : Equiv.Perm (Fin 4) := s.trans (Equiv.swap (s b) 1)
      have hs0 : s a = 0 := Equiv.swap_apply_left _ _
      have hsb : s b ≠ 0 := by
        intro he
        exact hba (s.injective (he.trans hs0.symm))
      have hra : rho a = 0 := by
        change Equiv.swap (s b) 1 (s a) = 0
        rw [hs0, Equiv.swap_apply_of_ne_of_ne (Ne.symm hsb) (by decide : (0 : Fin 4) ≠ 1)]
      have hrb : rho b = 1 := by
        change Equiv.swap (s b) 1 (s b) = 1
        exact Equiv.swap_apply_left _ _
      let w' : Fin 4 → ℤ := fun i => w (rho.symm i)
      have hw0 : w' 0 = 0 := by
        change w (rho.symm 0) = 0
        rw [← hra, rho.symm_apply_apply, ha]
      have hw1 : w' 1 = 0 := by
        change w (rho.symm 1) = 0
        rw [← hrb, rho.symm_apply_apply, hb]
      let P' := rename rho P
      have hcap' : IsWeightLE w' m P' := terminal_isWeightLE_rename_perm w m P hcap rho
      have hclock' : (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w' i) = 0 := by
        change (Fintype.card (Fin 4) : ℤ) * m - 2 * (∑ i : Fin 4, w (rho.symm i)) = 0
        rw [Equiv.sum_comp rho.symm w]
        exact hclock
      have hdet' : hessianDeterminant P' = 1 := by
        change hessianDeterminant (rename rho P) = 1
        rw [hessianDeterminant_rename_perm, hdet, map_one]
      have hperm := zeroClock_has_complementWeightPermutation w' m P' hcap' hclock' hdet'
      have h23 := complementPermutation_two_standard_zeros hm hperm hw0 hw1
      have he : w' = standardTwoZeroTerminalWeight m := by
        funext i
        fin_cases i <;> simp [hw0, hw1, h23.1, h23.2]
      rw [he] at hcap'
      apply mvGradientMap_injective_of_rename_perm rho P
      exact gradient_injective_of_twoZeroWeight_cap hJC2 m hm P' hcap' hdet'
  · have hpos (i : Fin 4) : 0 < w i := by
      have h := hw i
      by_contra hn
      exact hz ⟨i, by omega⟩
    exact gradient_injective_of_positiveWeight_zeroClock w hpos m P hcap hclock
      (δ := (1 : K)) one_ne_zero (by simpa using hdet)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.gradient_injective_of_nonnegativeWeight_zeroClock_of_JC2
