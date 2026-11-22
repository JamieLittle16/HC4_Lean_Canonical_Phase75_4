import HC4.Polynomial.RankThreeCubicSourcePoleRankSplit
import Mathlib.Tactic

/-!
# Rigidity of a rank-one symmetric matrix pencil

For symmetric matrices A and B over an integral domain, assume the
principal-pivot rank-one cross-product identities for A, B and A+B
at an index k where A(k,k) is nonzero.

Then the matrices are proportional *without dividing*:
  A(k,k) * B(i,j) = B(k,k) * A(i,j).

This is the algebraic core of a potential rank-one cubic Hessian
plane classification. The cross identities can be obtained by
vanishing 2x2 minors; none of the actual-source hypotheses are
assumed at this stage.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

theorem symmetric_rankOne_pencil_proportional
    {R : Type*} [CommRing R] [IsDomain R]
    (A B : Matrix (Fin 3) (Fin 3) R)
    (hA_symm : A.IsSymm)
    (hB_symm : B.IsSymm)
    (k : Fin 3)
    (hak : A k k ≠ 0)
    (hA : ∀ i j : Fin 3,
      A k k * A i j = A i k * A k j)
    (hB : ∀ i j : Fin 3,
      B k k * B i j = B i k * B k j)
    (hAB : ∀ i j : Fin 3,
      (A + B) k k * (A + B) i j =
        (A + B) i k * (A + B) k j) :
    ∀ i j : Fin 3, A k k * B i j = B k k * A i j := by
  classical
  have ha_diag (i : Fin 3) :
      A k k * A i i = A i k * A i k := by
    simpa only [hA_symm.apply i k] using hA i i
  have hb_diag (i : Fin 3) :
      B k k * B i i = B i k * B i k := by
    simpa only [hB_symm.apply i k] using hB i i
  have hab_diag (i : Fin 3) :
      (A k k + B k k) * (A i i + B i i) =
        (A i k + B i k) * (A i k + B i k) := by
    simpa only [Matrix.add_apply, hA_symm.apply i k,
      hB_symm.apply i k] using hAB i i
  have hcross (i : Fin 3) :
      A k k * B i i + B k k * A i i =
        2 * A i k * B i k := by
    calc
      _ = (A k k + B k k) * (A i i + B i i) -
          A k k * A i i - B k k * B i i := by ring
      _ = (A i k + B i k) * (A i k + B i k) -
          A i k * A i k - B i k * B i k := by
            rw [hab_diag, ha_diag, hb_diag]
      _ = 2 * A i k * B i k := by ring
  have halign (i : Fin 3) :
      A k k * B i k = B k k * A i k := by
    have hsquare :
        (A k k * B i k - B k k * A i k) *
        (A k k * B i k - B k k * A i k) = 0 := by
      calc
        _ = A k k * A k k *
              (B i k * B i k - B k k * B i i) +
            B k k * B k k *
              (A i k * A i k - A k k * A i i) +
            A k k * B k k *
              (A k k * B i i + B k k * A i i -
                2 * A i k * B i k) := by ring
        _ = 0 := by
              rw [← hb_diag i, ← ha_diag i, hcross i]
              ring
    have hz : A k k * B i k - B k k * A i k = 0 := by
      rcases mul_eq_zero.mp hsquare with hz | hz
      · exact hz
      · exact hz
    exact sub_eq_zero.mp hz
  have halign_row (j : Fin 3) :
      A k k * B k j = B k k * A k j := by
    simpa only [hB_symm.apply k j, hA_symm.apply k j] using halign j
  by_cases hbk : B k k = 0
  · have hBcol (i : Fin 3) : B i k = 0 := by
      have hsq : B i k * B i k = 0 := by
        simpa only [hbk, zero_mul] using (hb_diag i).symm
      rcases mul_eq_zero.mp hsq with hz | hz
      · exact hz
      · exact hz
    intro i j
    have hBrow : B k j = 0 := by
      rw [hB_symm.apply k j]
      exact hBcol j
    have hsum :
        A k k * (A i j + B i j) = A i k * A k j := by
      simpa [Matrix.add_apply, hbk, hBcol i, hBrow] using hAB i j
    calc
      A k k * B i j =
          A k k * (A i j + B i j) - A k k * A i j := by ring
      _ = 0 := by rw [hsum, hA i j]; ring
      _ = B k k * A i j := by rw [hbk, zero_mul]
  · intro i j
    have hweight :
        (A k k * B k k) * (A k k * B i j) =
        (A k k * B k k) * (B k k * A i j) := by
      calc
        _ = A k k * A k k * (B k k * B i j) := by ring
        _ = A k k * A k k * (B i k * B k j) := by rw [hB i j]
        _ = (A k k * B i k) * (A k k * B k j) := by ring
        _ = (B k k * A i k) * (B k k * A k j) := by
              rw [halign i, halign_row j]
        _ = B k k * B k k * (A i k * A k j) := by ring
        _ = B k k * B k k * (A k k * A i j) := by
              rw [hA i j]
        _ = (A k k * B k k) * (B k k * A i j) := by ring
    exact mul_left_cancel₀ (mul_ne_zero hak hbk) hweight

end
end HC4.Polynomial.RankThreeCubic
