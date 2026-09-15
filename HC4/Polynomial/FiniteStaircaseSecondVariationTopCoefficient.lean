import HC4.Polynomial.HeterogeneousTopCoefficient
import HC4.Valuation.ParameterGapSecondJet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Top longitudinal coefficient of a second determinant variation

Let `A(X), B(X), C(X)` be four-by-four polynomial matrices with entrywise
degree bounds `1`, `m`, `1`, where `1 < m`.  The nested dual matrix

    ((A,B),(B,2C))

is the universal `(0,q,2q)` second parameter jet.  Its doubly nilpotent
determinant component is the second determinant variation.

At longitudinal degree `2+2m`, every contribution involving `C` is too small:
it has degree at most four.  Hence the top coefficient is obtained by replacing
`A` by its `X^1` coefficient, `B` by its `X^m` coefficient, and `C` by zero.
This is the exact no-cancellation statement needed by the final one-fibre A19
pure-mode elimination.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- One scalar entry of the universal second variation jet. -/
def secondVariationJetEntry
    (a b c : Polynomial R) : DualNumber (DualNumber (Polynomial R)) :=
  ((a, b), (b, 2 * c))

/-- The corresponding scalar top-mode jet. -/
def secondVariationTopEntry
    (a b : R) : DualNumber (DualNumber R) :=
  ((a, b), (b, 0))

/-- Exact four-factor second-jet product formula. -/
theorem snd_snd_mul_four_secondVariationJetEntry
    (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3 : Polynomial R) :
    TrivSqZeroExt.snd (TrivSqZeroExt.snd
      (secondVariationJetEntry a0 b0 c0 *
        secondVariationJetEntry a1 b1 c1 *
        secondVariationJetEntry a2 b2 c2 *
        secondVariationJetEntry a3 b3 c3)) =
      2 * (c0 * a1 * a2 * a3 + a0 * c1 * a2 * a3 +
        a0 * a1 * c2 * a3 + a0 * a1 * a2 * c3 +
        b0 * b1 * a2 * a3 + b0 * a1 * b2 * a3 +
        b0 * a1 * a2 * b3 + a0 * b1 * b2 * a3 +
        a0 * b1 * a2 * b3 + a0 * a1 * b2 * b3) := by
  simp [secondVariationJetEntry, DualNumber.snd_mul]
  ring

/-- Scalar version of the same formula when the second-order layer is zero. -/
theorem snd_snd_mul_four_secondVariationTopEntry
    (a0 b0 a1 b1 a2 b2 a3 b3 : R) :
    TrivSqZeroExt.snd (TrivSqZeroExt.snd
      (secondVariationTopEntry a0 b0 *
        secondVariationTopEntry a1 b1 *
        secondVariationTopEntry a2 b2 *
        secondVariationTopEntry a3 b3)) =
      2 * (b0 * b1 * a2 * a3 + b0 * a1 * b2 * a3 +
        b0 * a1 * a2 * b3 + a0 * b1 * b2 * a3 +
        a0 * b1 * a2 * b3 + a0 * a1 * b2 * b3) := by
  simp [secondVariationTopEntry, DualNumber.snd_mul]
  ring

private theorem natDegree_mul_four_le
    {p q r s : Polynomial R} {a b c d : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (hr : r.natDegree ≤ c) (hs : s.natDegree ≤ d) :
    (p * q * r * s).natDegree ≤ a + b + c + d := by
  calc
    (p * q * r * s).natDegree ≤
        (p * q * r).natDegree + s.natDegree := Polynomial.natDegree_mul_le
    _ ≤ ((p * q).natDegree + r.natDegree) + s.natDegree := by
      omega
    _ ≤ (((p.natDegree + q.natDegree) + r.natDegree) + s.natDegree) := by
      omega
    _ ≤ a + b + c + d := by omega

/-- Top longitudinal coefficient of one four-entry second-jet product. -/
theorem coeff_top_snd_snd_mul_four_secondVariationJetEntry
    {m : ℕ} (hm : 1 < m)
    (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3 : Polynomial R)
    (ha0 : a0.natDegree ≤ 1) (ha1 : a1.natDegree ≤ 1)
    (ha2 : a2.natDegree ≤ 1) (ha3 : a3.natDegree ≤ 1)
    (hb0 : b0.natDegree ≤ m) (hb1 : b1.natDegree ≤ m)
    (hb2 : b2.natDegree ≤ m) (hb3 : b3.natDegree ≤ m)
    (hc0 : c0.natDegree ≤ 1) (hc1 : c1.natDegree ≤ 1)
    (hc2 : c2.natDegree ≤ 1) (hc3 : c3.natDegree ≤ 1) :
    (TrivSqZeroExt.snd (TrivSqZeroExt.snd
      (secondVariationJetEntry a0 b0 c0 *
        secondVariationJetEntry a1 b1 c1 *
        secondVariationJetEntry a2 b2 c2 *
        secondVariationJetEntry a3 b3 c3))).coeff (2 + 2 * m) =
      TrivSqZeroExt.snd (TrivSqZeroExt.snd
        (secondVariationTopEntry (a0.coeff 1) (b0.coeff m) *
          secondVariationTopEntry (a1.coeff 1) (b1.coeff m) *
          secondVariationTopEntry (a2.coeff 1) (b2.coeff m) *
          secondVariationTopEntry (a3.coeff 1) (b3.coeff m))) := by
  rw [snd_snd_mul_four_secondVariationJetEntry]
  rw [snd_snd_mul_four_secondVariationTopEntry]
  have htop : 4 < 2 + 2 * m := by omega
  have hcTerm0 : (c0 * a1 * a2 * a3).coeff (2 + 2 * m) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (natDegree_mul_four_le hc0 ha1 ha2 ha3) htop
  have hcTerm1 : (a0 * c1 * a2 * a3).coeff (2 + 2 * m) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (natDegree_mul_four_le ha0 hc1 ha2 ha3) htop
  have hcTerm2 : (a0 * a1 * c2 * a3).coeff (2 + 2 * m) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (natDegree_mul_four_le ha0 ha1 hc2 ha3) htop
  have hcTerm3 : (a0 * a1 * a2 * c3).coeff (2 + 2 * m) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (natDegree_mul_four_le ha0 ha1 ha2 hc3) htop
  have h01 := coeff_mul_four_at_degree_bounds hb0 hb1 ha2 ha3
  have h02 := coeff_mul_four_at_degree_bounds hb0 ha1 hb2 ha3
  have h03 := coeff_mul_four_at_degree_bounds hb0 ha1 ha2 hb3
  have h12 := coeff_mul_four_at_degree_bounds ha0 hb1 hb2 ha3
  have h13 := coeff_mul_four_at_degree_bounds ha0 hb1 ha2 hb3
  have h23 := coeff_mul_four_at_degree_bounds ha0 ha1 hb2 hb3
  simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul]
  rw [hcTerm0, hcTerm1, hcTerm2, hcTerm3]
  have hi01 : m + m + 1 + 1 = 2 + 2 * m := by omega
  have hi02 : m + 1 + m + 1 = 2 + 2 * m := by omega
  have hi03 : m + 1 + 1 + m = 2 + 2 * m := by omega
  have hi12 : 1 + m + m + 1 = 2 + 2 * m := by omega
  have hi13 : 1 + m + 1 + m = 2 + 2 * m := by omega
  have hi23 : 1 + 1 + m + m = 2 + 2 * m := by omega
  rw [hi01] at h01
  rw [hi02] at h02
  rw [hi03] at h03
  rw [hi12] at h12
  rw [hi13] at h13
  rw [hi23] at h23
  rw [h01, h02, h03, h12, h13, h23]
  ring

/-- Universal second-variation jet of three polynomial matrices. -/
noncomputable def secondVariationJetMatrix
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial R)) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber (Polynomial R))) :=
  fun i j => secondVariationJetEntry (A i j) (B i j) (C i j)

/-- Matrix of the two relevant top longitudinal coefficient layers. -/
noncomputable def secondVariationTopMatrix
    (A B : Matrix (Fin 4) (Fin 4) (Polynomial R)) (m : ℕ) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber R)) :=
  fun i j => secondVariationTopEntry ((A i j).coeff 1) ((B i j).coeff m)

/-- **No-cancellation top-coefficient theorem.**  At degree `2+2m`, the
second determinant variation sees only the leading endpoint and interior
matrices; an arbitrary degree-one second-order layer cannot contribute. -/
theorem coeff_top_snd_snd_det_secondVariationJetMatrix
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (m : ℕ) (hm : 1 < m)
    (hA : ∀ i j, (A i j).natDegree ≤ 1)
    (hB : ∀ i j, (B i j).natDegree ≤ m)
    (hC : ∀ i j, (C i j).natDegree ≤ 1) :
    (TrivSqZeroExt.snd (TrivSqZeroExt.snd
      (secondVariationJetMatrix A B C).det)).coeff (2 + 2 * m) =
      TrivSqZeroExt.snd (TrivSqZeroExt.snd
        (secondVariationTopMatrix A B m).det) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [secondVariationJetMatrix, secondVariationTopMatrix,
    Matrix.det_fin_three, Fin.succAbove,
    coeff_top_snd_snd_mul_four_secondVariationJetEntry
      (m := m) hm,
    hA, hB, hC]

end

end HC4.Polynomial
