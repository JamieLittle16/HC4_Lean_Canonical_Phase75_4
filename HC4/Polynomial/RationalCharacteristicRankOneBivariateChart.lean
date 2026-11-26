import HC4.Polynomial.RationalCharacteristicRankOneChartDescent

/-!
# Bivariate chart coefficient extraction

Regard T as a coefficient variable and y,z as the two polynomial
variables. The normalized chart identity then gives an identity
of univariate parameter polynomials at every y,z exponent.
The bivariate coefficients are exactly the already verified source
chart coefficient family. The Euler and derivative coefficient
identities are the remaining steps to the recurrence.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev A (K : Type*) [Field K] :=
  MvPolynomial (Fin 2) (_root_.Polynomial K)

def rankOne_bivariateExponent (j l : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j + Finsupp.single 1 l

/-- Move the chart parameter into the coefficient ring. -/
def rankOne_bivariateChart : B K →ₐ[K] A K :=
  MvPolynomial.aeval
    ![MvPolynomial.C _root_.Polynomial.X, X 0, X 1]

/-- The same map composed with the original source chart. -/
def rankOne_bivariateSource : B K →ₐ[K] A K :=
  MvPolynomial.aeval
    ![MvPolynomial.C _root_.Polynomial.X * X 0, X 0, X 1]

theorem rankOne_bivariateChart_comp :
    (rankOne_bivariateChart (K := K)).comp rankOne_normalizedChart =
      rankOne_bivariateSource := by
  unfold rankOne_normalizedChart rankOne_bivariateSource
  rw [MvPolynomial.comp_aeval]
  congr 1
  funext i
  fin_cases i <;> simp [rankOne_bivariateChart]

/-- A source monomial becomes a bivariate monomial with its original
x exponent recorded as a power of the parameter. -/
theorem rankOne_bivariateSource_monomial
    (m : Fin 3 →₀ ℕ) (c : K) :
    rankOne_bivariateSource (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (rankOne_bivariateExponent (m 0 + m 1) (m 2))
        (_root_.Polynomial.C c * _root_.Polynomial.X ^ m 0) := by
  classical
  unfold rankOne_bivariateSource
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_three]
  change MvPolynomial.C (_root_.Polynomial.C c) *
    ((MvPolynomial.C (_root_.Polynomial.X : _root_.Polynomial K) *
      (X (0 : Fin 2) : A K)) ^ m 0 * X 0 ^ m 1 * X 1 ^ m 2) = _
  rw [mul_pow, ← map_pow]
  calc
    _ = MvPolynomial.C (_root_.Polynomial.C c * _root_.Polynomial.X ^ m 0) *
        (X (0 : Fin 2) : A K) ^ (m 0 + m 1) * X 1 ^ m 2 := by
      rw [map_mul, pow_add]
      ring
    _ = _ := by
      rw [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul, mul_one]
      rfl

private theorem rankOne_bivariateExponent_eq_iff
    (j l j' l' : ℕ) :
    rankOne_bivariateExponent j l = rankOne_bivariateExponent j' l' ↔
      j = j' ∧ l = l' := by
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
    exact ⟨by simpa [rankOne_bivariateExponent] using h0,
      by simpa [rankOne_bivariateExponent] using h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem rankOne_chartExponent_eq_iff
    (m : Fin 3 →₀ ℕ) (n j l : ℕ) (hn : n ≤ j) :
    m = rankOne_chartExponent n j l ↔
      m 0 = n ∧ m 0 + m 1 = j ∧ m 2 = l := by
  constructor
  · intro h
    have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
    have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
    have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
    simp only [rankOne_chartExponent, Finsupp.add_apply] at h0 h1 h2
    simp at h0 h1 h2
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simp [rankOne_chartExponent] <;> omega

/-- Coefficients in the bivariate chart agree exactly with the
finite source coefficient family already used by the obstruction. -/
theorem rankOne_bivariateSource_coeff (f : B K) (j l : ℕ) :
    (rankOne_bivariateSource f).coeff (rankOne_bivariateExponent j l) =
      rankOne_chartCoeff f j l := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [rankOne_bivariateSource_monomial, MvPolynomial.coeff_monomial]
    apply _root_.Polynomial.ext
    intro n
    rw [rankOne_chartCoeff_coeff]
    by_cases hn : n ≤ j
    · rw [if_pos hn, MvPolynomial.coeff_monomial]
      simp only [rankOne_chartExponent_eq_iff m n j l hn,
        rankOne_bivariateExponent_eq_iff]
      by_cases hj : m 0 + m 1 = j
      · by_cases hl : m 2 = l
        · simp [hj, hl, eq_comm]
        · simp [hj, hl]
      · simp [hj]
    · rw [if_neg hn]
      simp only [rankOne_bivariateExponent_eq_iff]
      by_cases hj : m 0 + m 1 = j
      · by_cases hl : m 2 = l
        · have hne : n ≠ m 0 := by omega
          simp [hj, hl, hne]
        · simp [hj, hl]
      · simp [hj]
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, hp, hq]
    apply _root_.Polynomial.ext
    intro n
    simp only [_root_.Polynomial.coeff_add, rankOne_chartCoeff_coeff]
    split_ifs <;> simp [MvPolynomial.coeff_add]

/-- Parameter polynomials become constant bivariate polynomials. -/
theorem rankOne_bivariateChartTime_parameter
    (U : _root_.Polynomial K) :
    rankOne_bivariateChart
      (rankOne_normalizedChartTime (U.map (MvPolynomial.C : K →+* B K))) =
      MvPolynomial.C U := by
  induction U using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [_root_.Polynomial.map_add, map_add, hp, hq]
  | monomial n a =>
    rw [← _root_.Polynomial.C_mul_X_pow_eq_monomial,
      _root_.Polynomial.map_mul, _root_.Polynomial.map_C,
      _root_.Polynomial.map_pow, _root_.Polynomial.map_X, map_mul, map_pow,
      rankOne_normalizedChartTime_C, rankOne_normalizedChartTime_X]
    have hc : rankOne_normalizedChart (MvPolynomial.C a) = MvPolynomial.C a := by
      simp [rankOne_normalizedChart]
    rw [hc]
    have hC : rankOne_bivariateChart (MvPolynomial.C a) =
        (MvPolynomial.C (_root_.Polynomial.C a) : A K) := by
      unfold rankOne_bivariateChart
      rw [MvPolynomial.aeval_C]
      rfl
    have hX : rankOne_bivariateChart (X (0 : Fin 3) : B K) =
        (MvPolynomial.C _root_.Polynomial.X : A K) := by
      simp [rankOne_bivariateChart]
    rw [map_mul, map_pow, hC, hX, ← map_pow, ← map_mul]

/-- The descended trace equation has an exact bivariate coefficient
identity for each y,z exponent. -/
theorem rankOne_chartCoeff_trace_zero
    (f : B K) (U : Fin 3 → _root_.Polynomial K)
    (h : rankOne_normalizedChartTime (rankOne_tracePolynomial f U) = 0)
    (j l : ℕ) :
    (∑ i : Fin 3, U i * rankOne_chartCoeff (pderiv i f) j l) = 0 := by
  have h' := congrArg (rankOne_bivariateChart (K := K)) h
  simp only [map_zero, rankOne_tracePolynomial, map_sum, map_mul,
    rankOne_normalizedChartTime_C, rankOne_bivariateChartTime_parameter] at h'
  have hsource (i : Fin 3) :
      rankOne_bivariateChart (rankOne_normalizedChart (pderiv i f)) =
        rankOne_bivariateSource (pderiv i f) :=
    congrArg (fun g : B K →ₐ[K] A K => g (pderiv i f))
      rankOne_bivariateChart_comp
  simp only [hsource] at h'
  have hc := congrArg (MvPolynomial.coeff (rankOne_bivariateExponent j l)) h'
  change (∑ i : Fin 3, rankOne_bivariateSource (pderiv i f) *
    MvPolynomial.C (U i)).coeff (rankOne_bivariateExponent j l) = 0 at hc
  simp only [MvPolynomial.coeff_sum] at hc
  simpa only [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
    rankOne_bivariateSource_coeff] using hc

end
end HC4.Polynomial.RankThreeCubic
