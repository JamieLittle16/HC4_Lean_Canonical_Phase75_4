import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.Tactic

/-!
# A18.5.25: recognise and reconstruct an actual complementary support edge

The complementary-edge rigidity theorem is stated for the canonical honest
polynomial built from a univariate coefficient polynomial.  The Newton
endgame, however, produces an actual exposed multivariate edge.

This file closes the representation seam in the reverse direction.  If the
support of an actual polynomial is contained in the finite complementary
exponent line

  (h*a1*j, h*a2*j, k*b1*(M-j), k*b2*(M-j)),  0 <= j <= M,

then positivity of `h` and `a1` makes `j` recoverable from coordinate zero.
We extract the line coefficients canonically and reconstruct the original
multivariate polynomial exactly.
-/

namespace HC4.Polynomial

noncomputable section

/-- Actual support confinement to one finite complementary exponent line. -/
def IsSupportedOnComplementaryLine
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    ∃ j : ℕ, j ≤ M ∧
      d = complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j

/-- Positive first ray exponent and positive line scale make the line parameter
unique. -/
theorem complementaryLineExponentFinsupp_injective
    (a1 a2 b1 b2 h k M : ℕ)
    (ha1 : 0 < a1) (hh : 0 < h)
    {j r : ℕ}
    (hjr :
      complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j =
        complementaryLineExponentFinsupp a1 a2 b1 b2 h k M r) :
    j = r := by
  have h0 := congrArg (fun d : Fin 4 →₀ ℕ => d (0 : Fin 4)) hjr
  simp [complementaryLineExponentFinsupp] at h0
  rcases h0 with hjr | hh0 | ha10
  · exact hjr
  · exact (Nat.ne_of_gt hh hh0).elim
  · exact (Nat.ne_of_gt ha1 ha10).elim

/-- Canonical univariate coefficient polynomial extracted from an actual
complementary edge. -/
noncomputable def complementaryLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) : Polynomial K :=
  ∑ j ∈ Finset.range (M + 1),
    Polynomial.monomial j
      (MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j) F)

/-- Exact coefficient formula for the extracted complementary line. -/
theorem coeff_complementaryLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (j : ℕ) :
    (complementaryLineCoefficientPolynomial
      a1 a2 b1 b2 h k M F).coeff j =
      if j ≤ M then
        MvPolynomial.coeff
          (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j) F
      else 0 := by
  classical
  simp [complementaryLineCoefficientPolynomial,
    Polynomial.coeff_monomial, Nat.lt_succ_iff]

/-- The extracted coefficient polynomial is bounded by the finite edge length. -/
theorem complementaryLineCoefficientPolynomial_natDegree_le
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (complementaryLineCoefficientPolynomial
      a1 a2 b1 b2 h k M F).natDegree ≤ M := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_complementaryLineCoefficientPolynomial]
  simp [Nat.not_le.mpr hn]

@[simp] theorem coeff_zero_complementaryLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (complementaryLineCoefficientPolynomial
      a1 a2 b1 b2 h k M F).coeff 0 =
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M 0) F := by
  rw [coeff_complementaryLineCoefficientPolynomial]
  simp

@[simp] theorem coeff_M_complementaryLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (complementaryLineCoefficientPolynomial
      a1 a2 b1 b2 h k M F).coeff M =
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M M) F := by
  rw [coeff_complementaryLineCoefficientPolynomial]
  simp

/-- Direct finite range-sum using the coefficients of an actual edge. -/
noncomputable def complementaryLineRangePolynomial
    {K : Type*} [CommSemiring K]
    (a1 a2 b1 b2 h k M : ℕ)
    (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∑ j ∈ Finset.range (M + 1),
    complementaryLineTerm a1 a2 b1 b2 h k M j
      (MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j) F)

/-- An actual supported complementary edge is its coefficient range-sum. -/
theorem eq_complementaryLineRangePolynomial_of_supported
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (ha1 : 0 < a1) (hh : 0 < h)
    (hsupp : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M F) :
    F = complementaryLineRangePolynomial a1 a2 b1 b2 h k M F := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ F.support
  · rcases hsupp d hd with ⟨j, hj, rfl⟩
    unfold complementaryLineRangePolynomial
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [complementaryLineTerm_eq_monomial]
      simp
    · intro r hr hrj
      have hExp :
          complementaryLineExponentFinsupp a1 a2 b1 b2 h k M r ≠
            complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j := by
        intro heq
        have hindex := complementaryLineExponentFinsupp_injective
          a1 a2 b1 b2 h k M ha1 hh heq
        exact hrj hindex
      rw [complementaryLineTerm_eq_monomial]
      simp [hExp]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))).elim
  · have hd0 : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    unfold complementaryLineRangePolynomial
    rw [MvPolynomial.coeff_sum]
    rw [hd0]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    by_cases heq :
        complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j = d
    · rw [complementaryLineTerm_eq_monomial]
      simp [heq, hd0]
    · rw [complementaryLineTerm_eq_monomial]
      simp [heq]

/-- Bounded canonical complementary-line polynomials equal their complete
coefficient range-sum. -/
theorem complementaryLinePolynomial_eq_range
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M : ℕ}
    {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    complementaryLinePolynomial a1 a2 b1 b2 h k M phi =
      ∑ j ∈ Finset.range (M + 1),
        complementaryLineTerm a1 a2 b1 b2 h k M j (phi.coeff j) := by
  classical
  unfold complementaryLinePolynomial
  rw [Polynomial.sum_def]
  apply Finset.sum_subset
  · intro j hj
    have hjle : j ≤ M :=
      le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hdeg
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjle)
  · intro j hjRange hjNot
    have hc : phi.coeff j = 0 := Polynomial.notMem_support_iff.mp hjNot
    simp [hc, complementaryLineTerm]

/-- **Exact reconstruction of an actual complementary support edge.** -/
theorem eq_complementaryLinePolynomial_of_supported
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (ha1 : 0 < a1) (hh : 0 < h)
    (hsupp : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M F) :
    F = complementaryLinePolynomial a1 a2 b1 b2 h k M
      (complementaryLineCoefficientPolynomial a1 a2 b1 b2 h k M F) := by
  let phi := complementaryLineCoefficientPolynomial a1 a2 b1 b2 h k M F
  have hdeg : phi.natDegree ≤ M := by
    dsimp [phi]
    exact complementaryLineCoefficientPolynomial_natDegree_le
      a1 a2 b1 b2 h k M F
  rw [complementaryLinePolynomial_eq_range hdeg]
  have hrange := eq_complementaryLineRangePolynomial_of_supported
    (F := F) ha1 hh hsupp
  rw [hrange]
  unfold complementaryLineRangePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [coeff_complementaryLineCoefficientPolynomial]
  simp [hjle, phi]

end

end HC4.Polynomial