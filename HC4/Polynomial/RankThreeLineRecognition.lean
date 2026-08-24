import HC4.Polynomial.RankThreeMvSubstitution
import Mathlib.Tactic

/-!
# A18.5.21: recognising an actual rank-three support line

A18.5.4 constructs an honest multivariate rank-three line from a univariate
coefficient polynomial.  The Newton endgame needs the converse direction:
starting from an actual exposed polynomial whose support is known to lie on
one finite affine rank-three line, recover the coefficient polynomial without
losing any multivariate provenance.

The omitted coordinate is the canonical lattice parameter.  Along the line
its exponent is `j * u1`; when `u1 > 0` this makes the index `j` unique.  We
therefore extract the coefficient of the `j`th line exponent directly and
package those finitely many coefficients as a univariate polynomial.
-/

namespace HC4.Polynomial

noncomputable section

/-- Actual support confinement to the finite honest rank-three line from
A18.5.4. -/
def IsSupportedOnRankThreeLine
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    ∃ j : ℕ, j ≤ M ∧
      d = rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M j

/-- Positive omitted-coordinate step makes the honest line parameter unique. -/
theorem rankThreeLineExponentFinsupp_injective_of_u1_pos
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (hu1 : 0 < u1)
    {j k : ℕ}
    (hjk :
      rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M j =
        rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M k) :
    j = k := by
  have h0 := congrArg (fun d : Fin 4 →₀ ℕ => d (0 : Fin 4)) hjk
  simp [rankThreeLineExponentFinsupp] at h0
  nlinarith

/-- The univariate coefficient polynomial canonically extracted from an actual
multivariate rank-three line. -/
noncomputable def rankThreeLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) : Polynomial K :=
  ∑ j ∈ Finset.range (M + 1),
    Polynomial.monomial j
      (MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M j) F)

/-- Exact coefficient formula for the extracted line polynomial. -/
theorem coeff_rankThreeLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (j : ℕ) :
    (rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F).coeff j =
      if j ≤ M then
        MvPolynomial.coeff
          (rankThreeLineExponentFinsupp
            v2 v3 v4 u1 u2 u3 u4 M j) F
      else 0 := by
  classical
  simp [rankThreeLineCoefficientPolynomial,
    Polynomial.coeff_monomial, Nat.lt_succ_iff]

/-- The extracted coefficient polynomial has no terms beyond the chosen finite
line segment. -/
theorem rankThreeLineCoefficientPolynomial_natDegree_le
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F).natDegree ≤ M := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_rankThreeLineCoefficientPolynomial]
  simp [Nat.not_le.mpr hn]

/-- A nonzero polynomial genuinely supported on the line gives a nonzero
extracted coefficient polynomial. -/
theorem rankThreeLineCoefficientPolynomial_ne_zero_of_supported
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hF : F ≠ 0)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F) :
    rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F ≠ 0 := by
  rcases MvPolynomial.support_nonempty.mpr hF with ⟨d, hd⟩
  rcases hsupp d hd with ⟨j, hj, rfl⟩
  have hcoeff :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M j) F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  intro hzero
  have hz := congrArg
    (fun p : Polynomial K => p.coeff j) hzero
  rw [coeff_rankThreeLineCoefficientPolynomial] at hz
  simp [hj] at hz
  exact hcoeff hz

/-- Endpoint coefficient at `j=0` is retained literally. -/
theorem coeff_zero_rankThreeLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F).coeff 0 =
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) F := by
  rw [coeff_rankThreeLineCoefficientPolynomial]
  simp

/-- Endpoint coefficient at `j=M` is retained literally. -/
theorem coeff_M_rankThreeLineCoefficientPolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    (rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F).coeff M =
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) F := by
  rw [coeff_rankThreeLineCoefficientPolynomial]
  simp

end

end HC4.Polynomial
