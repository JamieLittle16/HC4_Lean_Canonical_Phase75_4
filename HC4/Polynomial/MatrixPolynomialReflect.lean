import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Reflection of polynomial matrices

For a polynomial matrix whose entries all have degree at most `N`, reflecting
each entry at `N` reverses a common finite grading.  Determinant is homogeneous
of degree `card n` in the columns, so the determinant reflects at
`card n * N`.

This is the state-free algebra needed to reverse the exact three-layer A19
pair-Rees pencil without constructing a second source family.
-/

namespace HC4.Polynomial

open Polynomial Matrix Equiv.Perm
open scoped BigOperators Matrix

noncomputable section

universe u v
variable {R : Type u} [CommRing R]

/-- Reflection is additive across a finite sum. -/
theorem reflect_finset_sum
    {ι : Type v} (s : Finset ι) (f : ι → Polynomial R) (N : ℕ) :
    Polynomial.reflect N (∑ i in s, f i) =
      ∑ i in s, Polynomial.reflect N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.reflect_add, ih,
        Finset.sum_insert ha]

/-- Uniform degree-bounded reflection commutes with a finite product, with the
reflection degree adding over the factors. -/
theorem reflect_finset_prod_uniform
    {ι : Type v} (s : Finset ι) (f : ι → Polynomial R) (N : ℕ)
    (hdeg : ∀ i ∈ s, (f i).natDegree ≤ N) :
    Polynomial.reflect (s.card * N) (∏ i in s, f i) =
      ∏ i in s, Polynomial.reflect N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haDeg : (f a).natDegree ≤ N :=
        hdeg a (Finset.mem_insert_self a s)
      have hsDeg : (∏ i in s, f i).natDegree ≤ s.card * N := by
        calc
          (∏ i in s, f i).natDegree ≤
              ∑ i in s, (f i).natDegree :=
            Polynomial.natDegree_prod_le s f
          _ ≤ ∑ _i in s, N := by
            exact Finset.sum_le_sum fun i hi =>
              hdeg i (Finset.mem_insert_of_mem hi)
          _ = s.card * N := by simp
      have ih' := ih (fun i hi => hdeg i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Nat.succ_mul, add_comm]
      rw [Polynomial.reflect_mul (f a) (∏ i in s, f i) haDeg hsDeg]
      rw [ih', Finset.prod_insert ha]

/-- Reflect every entry of a polynomial matrix at one common degree. -/
noncomputable def reflectMatrix
    {n : Type*} (N : ℕ) (M : Matrix n n (Polynomial R)) :
    Matrix n n (Polynomial R) :=
  fun i j => Polynomial.reflect N (M i j)

/-- **Determinant reflection.**  If every entry has degree at most `N`, then
reflecting all entries at `N` reflects the determinant at the total column
degree `card n * N`. -/
theorem det_reflectMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial R)) (N : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ N) :
    (reflectMatrix N M).det =
      Polynomial.reflect (Fintype.card n * N) M.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  rw [reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hprod :
      Polynomial.reflect (Fintype.card n * N)
          (∏ i : n, M (σ i) i) =
        ∏ i : n, Polynomial.reflect N (M (σ i) i) := by
    have h := reflect_finset_prod_uniform
      (R := R) (Finset.univ : Finset n)
      (fun i : n => M (σ i) i) N
      (fun i _ => hdeg (σ i) i)
    simpa [Finset.card_univ] using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, one_smul]
    exact hprod.symm
  · rw [hs, Units.neg_smul, one_smul, Units.neg_smul, one_smul,
      Polynomial.reflect_neg]
    exact congrArg Neg.neg hprod.symm

end

end HC4.Polynomial
