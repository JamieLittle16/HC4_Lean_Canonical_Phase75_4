import HC4.Polynomial.RationalCharacteristicRankOneParameterAssembly

/-!
# Rank-one affine parameter frontier

A cube-zero operator with a constant right factor already has a
nonzero constant left kernel. Consequently a reduced affine parameter
pair in the no-left-kernel branch has independent linear parts.
This removes both the constant-denominator and proportional-gradient
cases without a coordinate normalization.

The normalized obstruction also exports a constant left kernel, and
hence an annihilator of the actual original source adjugate.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- A constant right factor of a cube-zero matrix yields a
constant left kernel. No nonzero rank hypothesis is required. -/
theorem rankOne_constantRow_impossible_of_no_leftKernel
    (N : Matrix (Fin 3) (Fin 3) (E K))
    (u : Fin 3 → E K) (b : Fin 3 → K)
    (hN : ∀ i j, N i j = u i * algebraMap K (E K) (b j))
    (h3 : N ^ 3 = 0)
    (hno : ∀ c : Fin 3 → K,
      (fun i => algebraMap K (E K) (c i)) ᵥ* N = 0 → c = 0) : False := by
  classical
  by_cases hb : b = 0
  · have hz : N = 0 := by
      ext i j
      rw [hN, hb]
      simp
    have hone := hno (fun _ => 1) (by rw [hz, Matrix.vecMul_zero])
    exact one_ne_zero (congrFun hone (0 : Fin 3))
  · have hex : ∃ k : Fin 3, b k ≠ 0 := by
      by_contra hn
      apply hb
      funext k
      by_contra hk
      exact hn ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    let r : Fin 3 → E K := fun i => algebraMap K (E K) (b i)
    have hr : r k ≠ 0 := by
      change algebraMap K (E K) (b k) ≠ 0
      simpa only [map_zero] using (algebraMap K (E K)).injective.ne hk
    have hd := rankOne_dot_zero_of_cube_zero N u r hN h3 k hr
    apply hb
    apply hno b
    funext j
    change (∑ i : Fin 3, r i * N i j) = 0
    calc
      _ = (r ⬝ᵥ u) * r j := by
        rw [dotProduct, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hN]
        change r i * (u i * r j) = r i * u i * r j
        ring
      _ = 0 := by rw [hd, zero_mul]

/-- The first derivatives of the explicit affine representation
are the corresponding ground-field coefficients. -/
theorem rankOne_affine_partial_eq_C
    (p : B K)
    (hp : p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j)
    (i : Fin 3) :
    pderiv i p = MvPolynomial.C ((pderiv i p).coeff 0) := by
  classical
  calc
    _ = pderiv i (MvPolynomial.C (p.coeff 0) +
        ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j) :=
      congrArg (pderiv i : Derivation K (B K) (B K)) hp
    _ = _ := by
      rw [map_add, pderiv_C, zero_add, map_sum]
      simp only [MvPolynomial.pderiv_C_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [pderiv_X_of_ne hj, mul_zero]
      · simp

variable [CharZero K]

/-- An affine-ratio parameter with dependent linear parts would
give a constant right factor, contradicting the no-left-kernel
branch. The conclusion includes both nonzero gradients. -/
theorem rankOne_affine_parameter_linearParts_independent
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
    ∀ a b : K, (∀ j : Fin 3,
      a * (pderiv j p).coeff 0 + b * (pderiv j q).coeff 0 = 0) →
      a = 0 ∧ b = 0 := by
  obtain ⟨hp, hqaff⟩ :=
    rankOne_affine_parameters_of_derivative_factor N p q U s hs hq hcop
      hpos hN h3 hno
  let A : Fin 3 → K := fun j => (pderiv j p).coeff 0
  let D : Fin 3 → K := fun j => (pderiv j q).coeff 0
  let f : B K →+* E K := algebraMap (B K) (E K)
  let g : K →+* E K := algebraMap K (E K)
  let t := f p / f q
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hC (c : K) : f (MvPolynomial.C c) = g c :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes c
  have hd (j : Fin 3) :
      rationalCharacteristicPartial j t = (g (A j) - t * g (D j)) / f q := by
    apply (eq_div_iff hqf).mpr
    have h := rationalParameter_cleared_partial p q hq j
    change rationalCharacteristicPartial j t * f q =
      f (pderiv j p) - t * f (pderiv j q) at h
    rw [rankOne_affine_partial_eq_C p hp j, rankOne_affine_partial_eq_C q hqaff j,
      hC, hC] at h
    exact h
  let u : Fin 3 → E K := fun i =>
    s * (U i).eval₂ (algebraMap K (E K)) t
  have hn (i j : Fin 3) : N i j =
      u i * ((g (A j) - t * g (D j)) / f q) := by
    change N i j = _
    calc
      _ = u i * rationalCharacteristicPartial j t := hN i j
      _ = _ := by rw [hd]
  intro a b hab
  change ∀ j : Fin 3, a * A j + b * D j = 0 at hab
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    by_contra hb
    have hD (j : Fin 3) : D j = 0 := by
      have h := hab j
      rw [ha, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hb
    apply rankOne_constantRow_impossible_of_no_leftKernel N
      (fun i => u i / f q) A _ h3 hno
    intro i j
    rw [hn, hD j, map_zero, mul_zero, sub_zero]
    change u i * (g (A j) / f q) = (u i / f q) * g (A j)
    simp only [div_eq_mul_inv]
    ring
  · exfalso
    have hA (j : Fin 3) : A j = (-(b / a)) * D j := by
      apply mul_left_cancel₀ ha
      have he : a * (-(b / a) * D j) = -(b * D j) := by
        field_simp [ha]
      rw [he]
      linear_combination hab j
    apply rankOne_constantRow_impossible_of_no_leftKernel N
      (fun i => u i * ((g (-(b / a)) - t) / f q)) D _ h3 hno
    intro i j
    rw [hn, hA j, map_mul]
    change u i * ((g (-(b / a)) * g (D j) - t * g (D j)) / f q) =
      (u i * ((g (-(b / a)) - t) / f q)) * g (D j)
    simp only [div_eq_mul_inv]
    ring

/-- The already verified normalized contradiction gives the
actual constant-left-kernel conclusion in its natural matrix form. -/
theorem rankOne_normalized_exists_constant_leftKernel
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K))
    (U : Fin 3 → _root_.Polynomial K) (s : E K) (hs : s ≠ 0)
    (hN : ∀ i j, N i j =
      s * (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j)
    (h3 : N ^ 3 = 0)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N)
    (hreg : (hessian f).det ≠ 0) :
    ∃ b : Fin 3 → K, b ≠ 0 ∧
      (fun i => algebraMap K (E K) (b i)) ᵥ* N = 0 := by
  classical
  by_contra h
  apply rankOne_normalized_scaled_independent_impossible f N U s hs hN h3 hself _ hreg
  intro a b c hrel
  let d : Fin 3 → K := ![a, b, c]
  have hd : (∑ i : Fin 3, _root_.Polynomial.C (d i) * U i) = 0 := by
    simpa [Fin.sum_univ_three, d] using hrel
  have hk := rankOne_parameter_relation_leftKernel N U rankOne_normalizedParameter
    s rankOne_normalizedRow hN d hd
  have hz : d = 0 := by
    by_contra hn
    exact h ⟨d, hn, hk⟩
  exact ⟨congrFun hz (0 : Fin 3), congrFun hz (1 : Fin 3), congrFun hz (2 : Fin 3)⟩

/-- Source-honest normalized rank-one endpoint: the constant
relation pulls back to the adjugate of the original four-variable
polynomial, not merely to a rational reference-slice matrix. -/
theorem rationalCharacteristic_normalizedRankOne_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (U : Fin 3 → _root_.Polynomial K) (s : E K) (hs : s ≠ 0)
    (hN : ∀ i j, rationalCharacteristicJacobian V i j =
      s * (U i).eval₂ (algebraMap K (E K)) rankOne_normalizedParameter *
        rankOne_normalizedRow j) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  have h3 := rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg
    (fun i => hgrad (.inr i))
  have hself := rationalCharacteristicJacobian_selfAdjoint a L V hV
    (fun i => hgrad (.inr i))
  change (rationalCharacteristicJacobian V).transpose *
      rationalCharacteristicHessian a L =
    rationalCharacteristicHessian a L * rationalCharacteristicJacobian V at hself
  rw [rationalCharacteristicHessian_eq_slice_hessian] at hself
  have hf : (hessian (referenceSlice a L)).det ≠ 0 := by
    intro hz
    have he := rationalCharacteristicHessian_det_ne_zero a L hreg
    apply he
    rw [rationalCharacteristicHessian_eq_slice_hessian]
    change ((algebraMap (B K) (E K)).mapMatrix
      (hessian (referenceSlice a L))).det = 0
    rw [← RingHom.map_det, hz, map_zero]
  obtain ⟨b, hb0, hb⟩ := rankOne_normalized_exists_constant_leftKernel
    (referenceSlice a L) (rationalCharacteristicJacobian V) U s hs hN h3 hself hf
  obtain ⟨d, hd0, hd⟩ :=
    rationalCharacteristic_exists_annihilator_of_constant_leftKernel V hV b hb0 hb
  exact ⟨d, hd0, rationalCharacteristic_adjugate_annihilator a L V d hdet hV hreg hgrad hd⟩

end
end HC4.Polynomial.RankThreeCubic
