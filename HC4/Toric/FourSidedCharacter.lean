import HC4.Toric.ExceptionalGrading

/-!
# Arithmetic endpoint of the four-sided character obstruction

At the generic `p`-corner, the manuscript's two-torus rigidity argument
produces a Laurent monomial coefficient ratio `x1^m x4^n`.  Equality of the
original torus characters gives

    a * (m - n) = -2b.

This file formalises the exact lattice consequence of that identity and
connects it to the already verified exceptional-grading theorem.  The
upstream Schur/binary-Hessian argument which produces the Laurent ratio is a
separate remaining obligation.
-/

namespace HC4.Toric

/-- The Laurent-monomial character equation forces `a ∣ 2b`. -/
theorem dvd_two_mul_of_laurent_weight_relation
    {a b : ℕ} {m n : ℤ}
    (hweight : (a : ℤ) * (m - n) = -(2 * (b : ℤ))) :
    a ∣ 2 * b := by
  have hdivZ : (a : ℤ) ∣ (2 * (b : ℤ)) := by
    refine ⟨n - m, ?_⟩
    calc
      (2 * (b : ℤ)) = -((a : ℤ) * (m - n)) := by linarith
      _ = (a : ℤ) * (n - m) := by ring
  exact_mod_cast hdivZ

/-- Under the symmetric-grading hypotheses, the Laurent character equation
leaves exactly the exceptional pair `(2,1)`. -/
theorem exceptional_pair_of_laurent_weight_relation
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) {m n : ℤ}
    (hweight : (a : ℤ) * (m - n) = -(2 * (b : ℤ))) :
    a = 2 ∧ b = 1 := by
  exact exceptional_pair_of_dvd_two_mul ha hb hba hcop
    (dvd_two_mul_of_laurent_weight_relation hweight)

/-- Away from `(2,1)`, no Laurent coefficient ratio can have the required
original character difference `-2b`. -/
theorem no_laurent_weight_relation_of_nonexceptional
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hne : ¬ (a = 2 ∧ b = 1)) :
    ¬ ∃ m n : ℤ, (a : ℤ) * (m - n) = -(2 * (b : ℤ)) := by
  rintro ⟨m, n, hweight⟩
  exact hne (exceptional_pair_of_laurent_weight_relation
    ha hb hba hcop hweight)

end HC4.Toric
