module

public import HC4.Polynomial.RationalCharacteristicRankOneNormalizedNilpotent

/-!
# Rank-one rational parameter assembly

Starting from a polynomial parameter factorization of the velocity
Jacobian, derive the evaluated trace from cube-zero and independence
of the polynomial components from the absence of a constant left
kernel. The existing trace lift then forces the reduced parameter
polynomials to be affine.

The existence of the one-parameter factorization (Lüroth), and
normalization of the resulting affine pair, are separate obligations.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RationalCharacteristicRankOneParameterAssembly

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)

end RationalCharacteristicRankOneParameterAssembly

open RationalCharacteristicRankOneParameterAssembly (B E)

/-- A ground-field relation on the polynomial parameter vector
is already a constant left kernel of its factored matrix. -/
theorem rankOne_parameter_relation_leftKernel
    (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K) (t s : E K)
    (r : Fin 3 → E K)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K)) t * r j)
    (b : Fin 3 → K)
    (hb : (∑ i : Fin 3, _root_.Polynomial.C (b i) * U i) = 0) :
    (fun i => algebraMap K (E K) (b i)) ᵥ* N = 0 := by
  have he := congrArg
    (fun P : _root_.Polynomial K => P.eval₂ (algebraMap K (E K)) t) hb
  simp only [_root_.Polynomial.eval₂_finset_sum, _root_.Polynomial.eval₂_mul,
    _root_.Polynomial.eval₂_C, _root_.Polynomial.eval₂_zero] at he
  funext j
  change (∑ i : Fin 3, algebraMap K (E K) (b i) * N i j) = 0
  calc
    _ = s * (∑ i : Fin 3, algebraMap K (E K) (b i) *
          (U i).eval₂ (algebraMap K (E K)) t) * r j := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [hN]
      ring
    _ = 0 := by rw [he, mul_zero, zero_mul]

/-- The polynomial trace evaluates to the actual source gradient
contraction at any rational parameter, not just the normalized one. -/
theorem rankOne_tracePolynomial_eval_parameter
    (f : B K) (U : Fin 3 → _root_.Polynomial K) (t : E K) :
    (rankOne_tracePolynomial f U).eval₂ (algebraMap (B K) (E K)) t =
      ∑ i : Fin 3, (U i).eval₂ (algebraMap K (E K)) t *
        algebraMap (B K) (E K) (pderiv i f) := by
  unfold rankOne_tracePolynomial
  rw [_root_.Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C,
    rankOne_parameter_eval_map, mul_comm]

/-- Nilpotence of the factored matrix supplies the trace identity
at the reduced rational parameter. The right factor is the cleared
gradient of p/q. This includes the zero-row case. -/
theorem rankOne_evaluated_trace_of_cleared_factor
    (N : Matrix (Fin 3) (Fin 3) (E K))
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (s : E K) (hs : s ≠ 0)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K))
        (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) *
      (algebraMap (B K) (E K) (pderiv j p) -
        (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) *
          algebraMap (B K) (E K) (pderiv j q)))
    (h3 : N ^ 3 = 0) :
    let t := algebraMap (B K) (E K) p / algebraMap (B K) (E K) q
    (rankOne_tracePolynomial p U).eval₂ (algebraMap (B K) (E K)) t =
      t * (rankOne_tracePolynomial q U).eval₂ (algebraMap (B K) (E K)) t := by
  let t : E K := algebraMap (B K) (E K) p / algebraMap (B K) (E K) q
  let u : Fin 3 → E K := fun i => s * (U i).eval₂ (algebraMap K (E K)) t
  let r : Fin 3 → E K := fun j =>
    algebraMap (B K) (E K) (pderiv j p) -
      t * algebraMap (B K) (E K) (pderiv j q)
  have hn : ∀ i j, N i j = u i * r j := hN
  have hd : r ⬝ᵥ u = 0 := by
    by_cases hex : ∃ k : Fin 3, r k ≠ 0
    · obtain ⟨k, hk⟩ := hex
      exact rankOne_dot_zero_of_cube_zero N u r hn h3 k hk
    · have hr (k : Fin 3) : r k = 0 := by
        by_contra hk
        exact hex ⟨k, hk⟩
      simp [dotProduct, hr]
  have hfac : r ⬝ᵥ u =
      s * (∑ i : Fin 3, (U i).eval₂ (algebraMap K (E K)) t * r i) := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [u]
    ring
  rw [hfac] at hd
  have hz := (mul_eq_zero.mp hd).resolve_left hs
  change (rankOne_tracePolynomial p U).eval₂ (algebraMap (B K) (E K)) t =
    t * (rankOne_tracePolynomial q U).eval₂ (algebraMap (B K) (E K)) t
  rw [rankOne_tracePolynomial_eval_parameter, rankOne_tracePolynomial_eval_parameter]
  apply sub_eq_zero.mp
  calc
    _ = ∑ i : Fin 3, (U i).eval₂ (algebraMap K (E K)) t * r i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [r]
      ring
    _ = 0 := hz

variable [CharZero K]

/-- The actual fraction-field partial derivative of a reduced
rational parameter satisfies the cleared quotient rule. -/
theorem rationalParameter_cleared_partial
    (p q : B K) (hq : q ≠ 0) (j : Fin 3) :
    let t := algebraMap (B K) (E K) p / algebraMap (B K) (E K) q
    rationalCharacteristicPartial j t * algebraMap (B K) (E K) q =
      algebraMap (B K) (E K) (pderiv j p) -
        t * algebraMap (B K) (E K) (pderiv j q) := by
  let f : B K →+* E K := algebraMap (B K) (E K)
  let t := f p / f q
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hm : t * f q = f p := div_mul_cancel₀ _ hqf
  have h := congrArg (rationalCharacteristicPartial j) hm
  change rationalCharacteristicPartial j (t * f q) =
    rationalCharacteristicPartial j (f p) at h
  simp only [Derivation.leibniz, smul_eq_mul, f,
    rationalCharacteristicPartial_algebraMap] at h
  change rationalCharacteristicPartial j t * f q =
    f (pderiv j p) - t * f (pderiv j q)
  linear_combination h

/-- In the absence of a constant left kernel, a cube-zero
parameterized matrix forces its reduced parameter pair to be affine.
Neither a lifted trace nor independence of U is assumed. -/
theorem rankOne_affine_parameters_of_derivative_factor
    (N : Matrix (Fin 3) (Fin 3) (E K))
    (p q : B K) (U : Fin 3 → _root_.Polynomial K)
    (s : E K) (hs : s ≠ 0)
    (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hpos : 0 < max p.totalDegree q.totalDegree)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K))
        (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) *
      rationalCharacteristicPartial j
        (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q))
    (h3 : N ^ 3 = 0)
    (hno : ∀ b : Fin 3 → K,
      (fun i => algebraMap K (E K) (b i)) ᵥ* N = 0 → b = 0) :
    (p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j) ∧
    (q = MvPolynomial.C (q.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j q).coeff 0) * X j) := by
  let f : B K →+* E K := algebraMap (B K) (E K)
  let t := f p / f q
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hind (b : Fin 3 → K)
      (hb : (∑ i : Fin 3, _root_.Polynomial.C (b i) * U i) = 0) : b = 0 :=
    hno b (rankOne_parameter_relation_leftKernel N U t s
      (fun j => rationalCharacteristicPartial j t) hN b hb)
  have hc (i j : Fin 3) : N i j =
      (s / f q) * (U i).eval₂ (algebraMap K (E K)) t *
        (f (pderiv j p) - t * f (pderiv j q)) := by
    have hd : rationalCharacteristicPartial j t =
        (f (pderiv j p) - t * f (pderiv j q)) / f q :=
      (eq_div_iff hqf).mpr (rationalParameter_cleared_partial p q hq j)
    change N i j = _
    rw [show N i j = s * (U i).eval₂ (algebraMap K (E K)) t *
      rationalCharacteristicPartial j t from hN i j, hd]
    simp only [div_eq_mul_inv]
    ring
  have htrace := rankOne_evaluated_trace_of_cleared_factor N p q U
    (s / f q) (div_ne_zero hs hqf) hc h3
  exact rankOne_affine_parameters_of_evaluated_trace p q U hq hcop hpos htrace hind

end
end HC4.Polynomial.RankThreeCubic
