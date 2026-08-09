import HC4.Toric.BranchCharacter

/-!
# Arithmetic isolation of the exceptional symmetric grading

The four-sided character calculation in the paper yields `a ∣ 2b`.  For
coprime positive weights with `a > b`, this forces the unique pair `(2,1)`.
This module isolates that number-theoretic conclusion from the surrounding
geometric argument.
-/

namespace HC4.Toric

/-- Coprimality removes the factor `b` from a divisor of `2b`. -/
theorem dvd_two_of_coprime_dvd_two_mul
    {a b : ℕ} (hcop : a.Coprime b) (hdiv : a ∣ 2 * b) :
    a ∣ 2 := by
  exact hcop.dvd_of_dvd_mul_right hdiv

/--
The local character divisibility `a ∣ 2b` leaves only the exceptional pair
`(a,b)=(2,1)` under the symmetric-grading hypotheses.
-/
theorem exceptional_pair_of_dvd_two_mul
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hdiv : a ∣ 2 * b) :
    a = 2 ∧ b = 1 := by
  have haDvdTwo : a ∣ 2 := dvd_two_of_coprime_dvd_two_mul hcop hdiv
  have haLe : a ≤ 2 := Nat.le_of_dvd (by decide) haDvdTwo
  omega

/-- Contrapositive form used to exclude four-sided faces away from `(2,1)`. -/
theorem not_dvd_two_mul_of_nonexceptional
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hcop : a.Coprime b) (hne : ¬ (a = 2 ∧ b = 1)) :
    ¬ a ∣ 2 * b := by
  intro hdiv
  exact hne (exceptional_pair_of_dvd_two_mul ha hb hba hcop hdiv)

end HC4.Toric
