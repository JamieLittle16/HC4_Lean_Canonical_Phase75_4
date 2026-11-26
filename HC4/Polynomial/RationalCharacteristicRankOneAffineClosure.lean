module

public import HC4.Polynomial.RationalCharacteristicAffineOperator

/-!
# Closure for the rank-one rational derivative factorization

For a reduced nonconstant parameter, cube-zero and absence of a
constant left kernel force independent affine numerator and
denominator. Straighten these two coordinates using the verified
affine chart. The transformed operator has the normalized polynomial
factorization, so the normalized Hessian obstruction applies.

The existence of the one-parameter derivative factorization for an
arbitrary rank-one rational Jacobian remains a separate obligation.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RationalCharacteristicRankOneAffineClosure

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev Mat (K : Type*) := Matrix (Fin 3) (Fin 3) K

end RationalCharacteristicRankOneAffineClosure

open RationalCharacteristicRankOneAffineClosure (B E Mat)

/-- Evaluating scalar parameter polynomials commutes with a
ground-field algebra homomorphism. -/
theorem rankOne_parameter_eval_algHom
    (φ : E K →ₐ[K] E K) (U : _root_.Polynomial K) (t : E K) :
    φ (U.eval₂ (algebraMap K (E K)) t) =
      U.eval₂ (algebraMap K (E K)) (φ t) := by
  induction U using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
    rw [_root_.Polynomial.eval₂_add, map_add, hp, hq,
      _root_.Polynomial.eval₂_add]
  | monomial n a =>
    rw [_root_.Polynomial.eval₂_monomial, map_mul, map_pow,
      φ.commutes, _root_.Polynomial.eval₂_monomial]

/-- A constant matrix acts on polynomial parameter vectors before
or after evaluation, with the same result. -/
theorem rankOne_parameter_eval_matrix
    (P : Mat K) (U : Fin 3 → _root_.Polynomial K) (t : E K) (i : Fin 3) :
    (∑ k : Fin 3, _root_.Polynomial.C (P i k) * U k).eval₂
        (algebraMap K (E K)) t =
      ∑ k : Fin 3, algebraMap K (E K) (P i k) *
        (U k).eval₂ (algebraMap K (E K)) t := by
  rw [_root_.Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C]

/-- Matrix similarity of an outer product acts on its two factors
separately. This also isolates the common scalar. -/
theorem rankOne_similarity_factor
    {F : Type*} [Field F]
    (P N M : Mat F) (u r : Fin 3 → F) (s : F)
    (hn : ∀ i j, N i j = s * u i * r j) (i j : Fin 3) :
    (P * N * M) i j =
      s * (P *ᵥ u) i * (r ᵥ* M) j := by
  simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    hn, Fin.sum_univ_three]
  ring

variable [CharZero K]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- Full constant-left-kernel conclusion for the reduced rational
derivative factorization. No affine, normalized-chart, trace or
independence assumptions are imposed on its parameter. -/
theorem rankOne_exists_constant_leftKernel_of_derivative_factor
    (f : B K) (N : Mat (E K))
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
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N)
    (hreg : (hessian f).det ≠ 0) :
    ∃ b : Fin 3 → K, b ≠ 0 ∧
      (fun i => algebraMap K (E K) (b i)) ᵥ* N = 0 := by
  classical
  by_contra hno'
  have hno (b : Fin 3 → K)
      (hb : (fun i => algebraMap K (E K) (b i)) ᵥ* N = 0) : b = 0 := by
    by_contra hn
    exact hno' ⟨b, hn, hb⟩
  obtain ⟨hp, hqa⟩ := rankOne_affine_parameters_of_derivative_factor N p q U
    s hs hq hcop hpos hN h3 hno
  let A : Fin 3 → K := fun j => (pderiv j p).coeff 0
  let D : Fin 3 → K := fun j => (pderiv j q).coeff 0
  have hind := rankOne_affine_parameter_linearParts_independent N p q U
    s hs hq hcop hpos hN h3 hno
  obtain ⟨P, hP, hPA, hPD⟩ := rationalAffine_complete_covectors A D hind
  let M : Mat K := P⁻¹
  have hPM : P * M = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)
  have hMP : M * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP)
  have hM : M.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hPM
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at he
    exact zero_ne_one he
  let d : Fin 3 → K := ![p.coeff 0, q.coeff 0, 0]
  let c : Fin 3 → K := M.mulVec (-d)
  have hc : P.mulVec c = -d := by
    change P *ᵥ (M *ᵥ (-d)) = -d
    rw [Matrix.mulVec_mulVec, hPM, Matrix.one_mulVec]
  have hcomp : (rationalAffine_substitution M c).comp
      (rationalAffine_substitution P d) = AlgHom.id K (B K) := by
    rw [rationalAffine_substitution_comp, hPM, hc, add_neg_cancel,
      rationalAffine_substitution_one_zero]
  have hpX : rationalAffine_substitution P d (X 0) = p := by
    rw [rationalAffine_substitution_X]
    change MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C (P 0 j) * X j = p
    simp only [hPA]
    exact hp.symm
  have hqX : rationalAffine_substitution P d (X 1) = q := by
    rw [rationalAffine_substitution_X]
    change MvPolynomial.C (q.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C (P 1 j) * X j = q
    simp only [hPD]
    exact hqa.symm
  have hpchart : rationalAffine_substitution M c p = X 0 := by
    rw [← hpX]
    exact congrArg (fun e : B K →ₐ[K] B K => e (X 0)) hcomp
  have hqchart : rationalAffine_substitution M c q = X 1 := by
    rw [← hqX]
    exact congrArg (fun e : B K →ₐ[K] B K => e (X 1)) hcomp
  let g := algebraMap K (E K)
  let e := algebraMap (B K) (E K)
  let t := e p / e q
  let T := rankOne_normalizedParameter (K := K)
  let φ := rationalAffine_fraction M c hM
  have ht : φ t = T := by
    change φ (e p / e q) = T
    rw [map_div₀]
    change rationalAffine_fraction M c hM (e p) /
      rationalAffine_fraction M c hM (e q) = T
    rw [rationalAffine_fraction_algebraMap, rationalAffine_fraction_algebraMap,
      hpchart, hqchart]
    rfl
  have hqf : e q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hC (a : K) : e (MvPolynomial.C a) = g a :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
  let v : Fin 3 → E K := fun j => g (A j) - T * g (D j)
  let W : Fin 3 → _root_.Polynomial K := fun i =>
    ∑ k : Fin 3, _root_.Polynomial.C (P i k) * U k
  let Me := M.map g
  let Pe := P.map g
  let Ne := N.map φ.toRingHom
  let Nt := Pe * Ne * Me
  let σ := φ (s / e q)
  have hσ : σ ≠ 0 := by
    change φ.toRingHom (s / e q) ≠ 0
    simpa only [map_zero] using φ.toRingHom.injective.ne (div_ne_zero hs hqf)
  have hd (j : Fin 3) :
      rationalCharacteristicPartial j t = (g (A j) - t * g (D j)) / e q := by
    apply (eq_div_iff hqf).mpr
    have h := rationalParameter_cleared_partial p q hq j
    change rationalCharacteristicPartial j t * e q =
      e (pderiv j p) - t * e (pderiv j q) at h
    rw [rankOne_affine_partial_eq_C p hp j, rankOne_affine_partial_eq_C q hqa j,
      hC, hC] at h
    exact h
  have hNe (i j : Fin 3) :
      Ne i j = σ * (U i).eval₂ g T * v j := by
    have h := hN i j
    change N i j = s * (U i).eval₂ g t * rationalCharacteristicPartial j t at h
    rw [hd] at h
    have hh : N i j = (s / e q) * (U i).eval₂ g t *
        (g (A j) - t * g (D j)) := by
      rw [h]
      simp only [div_eq_mul_inv]
      ring
    change φ (N i j) = _
    rw [hh, map_mul, map_mul, map_sub, map_mul,
      rankOne_parameter_eval_algHom, ht, φ.commutes, φ.commutes]
  have hPME : Pe * Me = 1 := rationalAffine_mapped_inverse P M hPM
  have hrow (j : Fin 3) : (v ᵥ* Me) j = rankOne_normalizedRow j := by
    have h0 := congrArg (fun Q : Mat (E K) => Q 0 j) hPME
    have h1 := congrArg (fun Q : Mat (E K) => Q 1 j) hPME
    change (∑ k : Fin 3, g (P 0 k) * g (M k j)) =
      (1 : Mat (E K)) 0 j at h0
    change (∑ k : Fin 3, g (P 1 k) * g (M k j)) =
      (1 : Mat (E K)) 1 j at h1
    simp only [hPA] at h0
    simp only [hPD] at h1
    change (∑ k : Fin 3, (g (A k) - T * g (D k)) * g (M k j)) =
      rankOne_normalizedRow j
    calc
      _ = (∑ k : Fin 3, g (A k) * g (M k j)) -
          T * (∑ k : Fin 3, g (D k) * g (M k j)) := by
        simp only [Fin.sum_univ_three]
        ring
      _ = rankOne_normalizedRow j := by
        rw [h0, h1]
        fin_cases j <;> simp [Matrix.one_apply, rankOne_normalizedRow, T]
  have hcol (i : Fin 3) :
      (Pe *ᵥ (fun k => (U k).eval₂ g T)) i = (W i).eval₂ g T := by
    change (∑ k : Fin 3, g (P i k) * (U k).eval₂ g T) =
      (∑ k : Fin 3, _root_.Polynomial.C (P i k) * U k).eval₂ g T
    exact (rankOne_parameter_eval_matrix P U T i).symm
  have hNt (i j : Fin 3) :
      Nt i j = σ * (W i).eval₂ g T * rankOne_normalizedRow j := by
    change (Pe * Ne * Me) i j = _
    rw [rankOne_similarity_factor Pe Ne Me _ v σ hNe, hcol, hrow]
  let H := (hessian f).map e
  obtain ⟨hn3, hns⟩ := rationalAffine_fraction_operator_identities M c hM N H h3 hself
  have hNt3 : Nt ^ 3 = 0 :=
    rationalAffine_similarity_cube_zero Me Pe Ne
      (rationalAffine_mapped_inverse M P hMP) hn3
  have hNts : Nt.transpose *
      (hessian (rationalAffine_substitution M c f)).map e =
      (hessian (rationalAffine_substitution M c f)).map e * Nt := by
    rw [rationalAffine_fraction_hessian M c hM f]
    exact rationalAffine_similarity_selfAdjoint Me Pe Ne (H.map φ.toRingHom)
      (rationalAffine_mapped_inverse M P hMP) hns
  obtain ⟨b, hb, hk⟩ := rankOne_normalized_exists_constant_leftKernel
    (rationalAffine_substitution M c f) Nt W σ hσ hNt hNt3 hNts
    (rationalAffine_substitution_hessian_det_ne_zero M c hM f hreg)
  exact hno' (rationalAffine_similarity_leftKernel_pullback M P c hM hMP hPM N b hb hk)

end
end HC4.Polynomial.RankThreeCubic
