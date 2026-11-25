import HC4.Polynomial.RationalCharacteristicParameterLift

/-!
# Rank-one trace lift and affine-parameter assembly

The evaluated trace equation at a reduced nonconstant rational
parameter supplies the entire lifted trace identity. Its time
coefficients are constant linear combinations of the transverse
partials of p and q, hence have strictly smaller source degree.

Combining the reduced-parameter lift with the symmetric pencil
argument gives affine parameter polynomials whenever the polynomial
derivative vector has no nonzero constant relation. The remaining
rank-one parametrization and Hessian obstruction are not assumed
to have been proved here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev T (K : Type*) [Field K] := _root_.Polynomial (B K)

/-- The source polynomial in an independent parameter whose
coefficients encode the gradient contraction. -/
def rankOne_tracePolynomial (p : B K) (U : Fin 3 → _root_.Polynomial K) : T K :=
  ∑ j : Fin 3, _root_.Polynomial.C (pderiv j p) *
    (U j).map (MvPolynomial.C : K →+* B K)

/-- Coefficients of the trace polynomial are constant linear
combinations of the source partials. -/
theorem rankOne_tracePolynomial_coeff
    (p : B K) (U : Fin 3 → _root_.Polynomial K) (n : ℕ) :
    (rankOne_tracePolynomial p U).coeff n =
      ∑ j : Fin 3, pderiv j p * MvPolynomial.C ((U j).coeff n) := by
  simp only [rankOne_tracePolynomial, _root_.Polynomial.finset_sum_coeff,
    _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_map]

private theorem trace_degree_sum_lt
    (s : Finset (Fin 3)) (f : Fin 3 → B K) (D : ℕ)
    (hD : 0 < D) (hf : ∀ i ∈ s, (f i).totalDegree < D) :
    (∑ i ∈ s, f i).totalDegree < D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
    apply max_lt_iff.mpr
    exact ⟨hf i (Finset.mem_insert_self _ _),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))⟩

variable [CharZero K]

private theorem trace_pderiv_mul_C_degree_lt
    (p : B K) (i : Fin 3) (c : K) (D : ℕ)
    (hD : 0 < D) (hp : p.totalDegree ≤ D) :
    (pderiv i p * MvPolynomial.C c).totalDegree < D := by
  by_cases h : p.totalDegree = 0
  · have hc : p = MvPolynomial.C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
    rw [hc, pderiv_C, zero_mul, MvPolynomial.totalDegree_zero]
    exact hD
  · have hd := totalDegree_pderiv_lt_of_totalDegree_pos p i (Nat.pos_of_ne_zero h)
    have hm := MvPolynomial.totalDegree_mul (pderiv i p) (MvPolynomial.C c)
    rw [MvPolynomial.totalDegree_C, add_zero] at hm
    exact lt_of_le_of_lt hm (lt_of_lt_of_le hd hp)

/-- Every coefficient has strictly smaller source degree than any
positive common upper bound for the degree of the parameter pair. -/
theorem rankOne_tracePolynomial_coeff_degree_lt
    (p : B K) (U : Fin 3 → _root_.Polynomial K) (n D : ℕ)
    (hD : 0 < D) (hp : p.totalDegree ≤ D) :
    ((rankOne_tracePolynomial p U).coeff n).totalDegree < D := by
  rw [rankOne_tracePolynomial_coeff]
  apply trace_degree_sum_lt _ _ D hD
  intro i _
  exact trace_pderiv_mul_C_degree_lt p i ((U i).coeff n) D hD hp

/-- The evaluated rank-one trace equation forces its lifted identity.
The evaluated equation is given in terms of the original source
polynomials, so no independent lifted-trace hypothesis is needed. -/
theorem rankOne_lifted_trace_of_evaluated_trace
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hpos : 0 < max p.totalDegree q.totalDegree)
    (htrace : (rankOne_tracePolynomial p U).eval₂ (algebraMap (B K) (E K))
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) =
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) *
        (rankOne_tracePolynomial q U).eval₂ (algebraMap (B K) (E K))
          (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q)) :
    rankOne_tracePolynomial p U =
      _root_.Polynomial.X * rankOne_tracePolynomial q U := by
  let P := rankOne_tracePolynomial p U
  let Q := rankOne_tracePolynomial q U
  let D := max p.totalDegree q.totalDegree
  let F : T K := P - _root_.Polynomial.X * Q
  have hP (n : ℕ) : (P.coeff n).totalDegree < D :=
    rankOne_tracePolynomial_coeff_degree_lt p U n D hpos (le_max_left _ _)
  have hQ (n : ℕ) : (Q.coeff n).totalDegree < D :=
    rankOne_tracePolynomial_coeff_degree_lt q U n D hpos (le_max_right _ _)
  have hsmall (n : ℕ) : (F.coeff n).totalDegree < D := by
    have hX : ((_root_.Polynomial.X * Q).coeff n).totalDegree < D := by
      cases n with
      | zero => simpa only [_root_.Polynomial.coeff_X_mul_zero,
          MvPolynomial.totalDegree_zero] using hpos
      | succ n => simpa only [Nat.succ_eq_add_one, _root_.Polynomial.coeff_X_mul] using hQ n
    change ((P - _root_.Polynomial.X * Q).coeff n).totalDegree < D
    rw [_root_.Polynomial.coeff_sub, sub_eq_add_neg]
    apply lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
    rw [MvPolynomial.totalDegree_neg]
    exact max_lt_iff.mpr ⟨hP n, hX⟩
  have hF : F.eval₂ (algebraMap (B K) (E K))
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) = 0 := by
    change (P - _root_.Polynomial.X * Q).eval₂ _ _ = 0
    rw [_root_.Polynomial.eval₂_sub, _root_.Polynomial.eval₂_mul,
      _root_.Polynomial.eval₂_X]
    exact sub_eq_zero.mpr htrace
  exact sub_eq_zero.mp (rationalParameter_lift_of_eval_zero p q hq hcop F hF hsmall)

/-- Rank-one affine parameter rigidity directly from the evaluated
trace equation and independence of the derivative vector. -/
theorem rankOne_affine_parameters_of_evaluated_trace
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hpos : 0 < max p.totalDegree q.totalDegree)
    (htrace : (rankOne_tracePolynomial p U).eval₂ (algebraMap (B K) (E K))
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) =
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) *
        (rankOne_tracePolynomial q U).eval₂ (algebraMap (B K) (E K))
          (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q))
    (hind : ∀ b : Fin 3 → K,
      (∑ j : Fin 3, _root_.Polynomial.C (b j) * U j) = 0 → b = 0) :
    (p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j) ∧
    (q = MvPolynomial.C (q.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j q).coeff 0) * X j) :=
  rankOne_affine_parameters_of_lifted_trace_independent p q U
    (rankOne_lifted_trace_of_evaluated_trace p q U hq hcop hpos htrace) hind

end
end HC4.Polynomial.RankThreeCubic
