import HC4.Polynomial.RationalCharacteristicAffineFraction

/-!
# Similarity transport for affine rational charts

Transport the operator by the inverse linear matrix on the left
and the linear matrix on the right, and the Hessian by congruence.
Cube-zero and self-adjointness survive. A constant left kernel of
the transported operator pulls back to the original operator.

The final affine-ratio factor computation is separate.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section MatrixAlgebra

variable {F : Type*} [Field F]

private abbrev Mat (F : Type*) := Matrix (Fin 3) (Fin 3) F

/-- Similarity preserves cube-zero, using only the two-sided inverse
identities needed for the coordinate change. -/
theorem rationalAffine_similarity_cube_zero
    (M P N : Mat F) (hMP : M * P = 1) (hN : N ^ 3 = 0) :
    (P * N * M) ^ 3 = 0 := by
  have hs : (P * N * M) * (P * N * M) = P * (N * N) * M := by
    calc
      _ = P * N * (M * P) * N * M := by noncomm_ring
      _ = _ := by rw [hMP, mul_one]; noncomm_ring
  have ht : (P * N * M) ^ 3 = P * (N ^ 3) * M := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [hs]
    calc
      _ = P * (N * N) * (M * P) * N * M := by noncomm_ring
      _ = _ := by rw [hMP, mul_one]; noncomm_ring
  rw [ht, hN, mul_zero, zero_mul]

/-- Self-adjointness is preserved by paired similarity and congruence. -/
theorem rationalAffine_similarity_selfAdjoint
    (M P N H : Mat F) (hMP : M * P = 1)
    (hself : N.transpose * H = H * N) :
    (P * N * M).transpose * (M.transpose * H * M) =
      (M.transpose * H * M) * (P * N * M) := by
  have ht : P.transpose * M.transpose = 1 := by
    rw [← Matrix.transpose_mul, hMP, Matrix.transpose_one]
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    _ = M.transpose * N.transpose * (P.transpose * M.transpose) * H * M := by
      noncomm_ring
    _ = M.transpose * (N.transpose * H) * M := by rw [ht, mul_one]; noncomm_ring
    _ = M.transpose * (H * N) * M := by rw [hself]
    _ = (M.transpose * H * M) * (P * N * M) := by
      symm
      calc
        _ = M.transpose * H * (M * P) * N * M := by noncomm_ring
        _ = _ := by rw [hMP, mul_one]; noncomm_ring

end MatrixAlgebra

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)

/-- The constant-coordinate matrices retain their inverse identity
after extending scalars to the transverse fraction field. -/
theorem rationalAffine_mapped_inverse
    (M P : Mat K) (hMP : M * P = 1) :
    M.map (algebraMap K (E K)) * P.map (algebraMap K (E K)) = 1 := by
  rw [← Matrix.map_mul, hMP, Matrix.map_one]

/-- The Hessian of the actual substituted reference polynomial is
the fraction-field congruence of the original Hessian. -/
theorem rationalAffine_fraction_hessian
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0) (f : B K) :
    (hessian (rationalAffine_substitution M c f)).map (algebraMap (B K) (E K)) =
      (M.map (algebraMap K (E K))).transpose *
        ((hessian f).map (algebraMap (B K) (E K))).map
          (rationalAffine_fraction M c hM).toRingHom *
        M.map (algebraMap K (E K)) := by
  rw [rationalAffine_substitution_hessian, Matrix.map_mul, Matrix.map_mul]
  have hC : (M.map (MvPolynomial.C : K →+* B K)).map
      (algebraMap (B K) (E K)) = M.map (algebraMap K (E K)) := by
    apply Matrix.ext
    intro i j
    exact (IsScalarTower.toAlgHom K (B K) (E K)).commutes (M i j)
  have hCt : ((M.map (MvPolynomial.C : K →+* B K)).transpose).map
      (algebraMap (B K) (E K)) = (M.map (algebraMap K (E K))).transpose := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun Q : Mat (E K) => Q j i) hC
  have hS : ((hessian f).map (rationalAffine_substitution M c).toRingHom).map
      (algebraMap (B K) (E K)) =
      ((hessian f).map (algebraMap (B K) (E K))).map
        (rationalAffine_fraction M c hM).toRingHom := by
    apply Matrix.ext
    intro i j
    exact (rationalAffine_fraction_algebraMap M c hM (hessian f i j)).symm
  rw [hCt, hS, hC]

/-- Entrywise fraction-field substitution preserves the two operator
identities, before applying the constant matrix change of basis. -/
theorem rationalAffine_fraction_operator_identities
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0)
    (N H : Mat (E K)) (h3 : N ^ 3 = 0)
    (hself : N.transpose * H = H * N) :
    let φ := (rationalAffine_fraction M c hM).toRingHom
    (N.map φ) ^ 3 = 0 ∧
      (N.map φ).transpose * H.map φ = H.map φ * N.map φ := by
  let φ := (rationalAffine_fraction M c hM).toRingHom
  have ht : N.transpose.map φ = (N.map φ).transpose := by
    apply Matrix.ext
    intro i j
    rfl
  have hc := congrArg (fun Q : Mat (E K) => Q.map φ) h3
  have hs := congrArg (fun Q : Mat (E K) => Q.map φ) hself
  simp only [pow_succ, pow_zero, one_mul, Matrix.map_mul, Matrix.map_zero] at hc
  rw [Matrix.map_mul, Matrix.map_mul, ht] at hs
  exact ⟨by simpa only [pow_succ, pow_zero, one_mul] using hc, hs⟩

/-- Pull a constant left kernel back through the chart and the
similarity, using injectivity of the fraction-field homomorphism.
The pulled covector is nonzero by the inverse identities. -/
theorem rationalAffine_similarity_leftKernel_pullback
    (M P : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0)
    (hMP : M * P = 1) (hPM : P * M = 1)
    (N : Mat (E K)) (b : Fin 3 → K) (hb : b ≠ 0)
    (hk : (fun i => algebraMap K (E K) (b i)) ᵥ*
      (P.map (algebraMap K (E K)) *
        N.map (rationalAffine_fraction M c hM).toRingHom *
        M.map (algebraMap K (E K))) = 0) :
    ∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ᵥ* N = 0 := by
  let g := algebraMap K (E K)
  let φ := rationalAffine_fraction M c hM
  let d := b ᵥ* P
  let be : Fin 3 → E K := fun i => g (b i)
  let de : Fin 3 → E K := fun i => g (d i)
  let Me := M.map g
  let Pe := P.map g
  let Ne := N.map φ.toRingHom
  have hde : de = be ᵥ* Pe := by
    funext j
    change g (∑ i : Fin 3, b i * P i j) =
      ∑ i : Fin 3, g (b i) * g (P i j)
    simp only [map_sum, map_mul]
  have hMP' : Me * Pe = 1 := rationalAffine_mapped_inverse M P hMP
  have hdk : de ᵥ* Ne = 0 := by
    change be ᵥ* (Pe * Ne * Me) = 0 at hk
    have he : (de ᵥ* Ne) ᵥ* Me = 0 := by
      rw [hde, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
      exact hk
    calc
      de ᵥ* Ne = (de ᵥ* Ne) ᵥ* (1 : Mat (E K)) := by rw [Matrix.vecMul_one]
      _ = ((de ᵥ* Ne) ᵥ* Me) ᵥ* Pe := by
        rw [Matrix.vecMul_vecMul, hMP']
      _ = 0 := by rw [he, Matrix.zero_vecMul]
  refine ⟨d, ?_, ?_⟩
  · intro hz
    apply hb
    calc
      b = b ᵥ* (1 : Mat K) := by rw [Matrix.vecMul_one]
      _ = (b ᵥ* P) ᵥ* M := by rw [Matrix.vecMul_vecMul, hPM]
      _ = 0 := by change d ᵥ* M = 0; rw [hz, Matrix.zero_vecMul]
  · funext j
    apply φ.toRingHom.injective
    have he := congrFun hdk j
    change (∑ i : Fin 3, g (d i) * φ (N i j)) = 0 at he
    change φ (∑ i : Fin 3, g (d i) * N i j) = φ 0
    simpa only [map_sum, map_mul, φ.commutes, map_zero] using he

end
end HC4.Polynomial.RankThreeCubic
