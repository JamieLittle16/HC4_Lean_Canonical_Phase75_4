import HC4.Polynomial.RationalCharacteristicRankOneAffineClosure

/-!
# From a common rational parameter to actual characteristic rigidity

The one-parameter existence problem need only supply rational
representations of the three velocity components. Differentiation,
clearing the common denominator, reducing the parameter in the
actual transverse fraction field, and exporting the original
constant adjugate annihilator are handled here.

The existence of such a common parameter for a rank-one Jacobian
is not assumed as an axiom or proved by this file.
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
private abbrev P (K : Type*) [Field K] := _root_.Polynomial K

/-- Scalar polynomial evaluation obeys the ordinary chain rule for
any ground-field derivation of a field. -/
theorem rationalParameter_polynomial_chainRule
    {F : Type*} [Field F] [Algebra K F]
    (D : Derivation K F F) (t : F) (p : P K) :
    D (p.eval₂ (algebraMap K F) t) =
      p.derivative.eval₂ (algebraMap K F) t * D t := by
  induction p using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
    rw [_root_.Polynomial.eval₂_add, map_add, hp, hq,
      _root_.Polynomial.derivative_add, _root_.Polynomial.eval₂_add, add_mul]
  | monomial n a =>
    simp only [_root_.Polynomial.eval₂_monomial,
      _root_.Polynomial.derivative_monomial, Derivation.leibniz,
      Derivation.map_algebraMap, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul, map_mul, map_natCast, mul_zero, add_zero] <;> ring

/-- If the components are rational functions of one parameter,
a common nonzero denominator for their derivatives can be cleared
without making any assumptions on their degrees or independence. -/
theorem rationalCharacteristic_commonParameter_factor
    (V : I → E K) (t : E K) (A Q : Fin 3 → P K)
    (hq : ∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hv : ∀ i, V (.inr i) = (A i).eval₂ (algebraMap K (E K)) t /
      (Q i).eval₂ (algebraMap K (E K)) t) :
    ∃ (U : Fin 3 → P K) (s : E K), s ≠ 0 ∧
      ∀ i j, rationalCharacteristicJacobian V i j =
        s * (U i).eval₂ (algebraMap K (E K)) t *
          rationalCharacteristicPartial j t := by
  classical
  let ev : P K →+* E K := _root_.Polynomial.eval₂RingHom (algebraMap K (E K)) t
  let R : Fin 3 → P K := fun i => ∏ k ∈ Finset.univ.erase i, Q k ^ 2
  let L : P K := ∏ k : Fin 3, Q k ^ 2
  let U : Fin 3 → P K := fun i =>
    ((Q i) * (A i).derivative - (A i) * (Q i).derivative) * R i
  have hL (i : Fin 3) : L = Q i ^ 2 * R i := by
    dsimp only [L, R]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hLn : ev L ≠ 0 := by
    change ev (∏ k : Fin 3, Q k ^ 2) ≠ 0
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    rw [map_pow]
    exact pow_ne_zero _ (hq k)
  refine ⟨U, (ev L)⁻¹, inv_ne_zero hLn, ?_⟩
  intro i j
  let D := rationalCharacteristicPartial (K := K) j
  change D (V (.inr i)) = (ev L)⁻¹ * ev (U i) * D t
  have hvi : V (.inr i) = ev (A i) / ev (Q i) := hv i
  have hA : D (ev (A i)) = ev (A i).derivative * D t :=
    rationalParameter_polynomial_chainRule D t (A i)
  have hQ : D (ev (Q i)) = ev (Q i).derivative * D t :=
    rationalParameter_polynomial_chainRule D t (Q i)
  rw [hvi, Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul, hA, hQ]
  have hqv : ev (Q i) ≠ 0 := hq i
  have hRv : ev (R i) ≠ 0 := by
    intro hz
    apply hLn
    rw [hL i, map_mul, hz, mul_zero]
  rw [hL i]
  simp only [U, map_mul, map_sub, map_pow]
  field_simp [hqv, hRv] <;> ring

variable [CharZero K]

set_option maxHeartbeats 2000000

/-- A nonconstant common rational parameter is automatically
represented by a reduced pair of positive maximum total degree
in the original transverse fraction ring. -/
theorem rationalParameter_exists_reduced_nonconstant
    (t : E K) (ht : ∀ c : K, t ≠ algebraMap K (E K) c) :
    ∃ p q : B K, q ≠ 0 ∧ IsRelPrime p q ∧
      0 < max p.totalDegree q.totalDegree ∧
      algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = t := by
  let p : B K := IsFractionRing.num (B K) t
  let q : B K := IsFractionRing.den (B K) t
  have hq : q ≠ 0 := nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) t)
  have hr : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = t :=
    IsFractionRing.mk'_num_den' (B K) t
  refine ⟨p, q, hq, IsFractionRing.num_den_reduced (B K) t, ?_, hr⟩
  by_contra hn
  have hp0 : p.totalDegree = 0 := by
    have hm : p.totalDegree ≤ max p.totalDegree q.totalDegree := le_max_left _ _
    omega
  have hq0 : q.totalDegree = 0 := by
    have hm : q.totalDegree ≤ max p.totalDegree q.totalDegree := le_max_right _ _
    omega
  have hpC := totalDegree_eq_zero_iff_eq_C.mp hp0
  have hqC := totalDegree_eq_zero_iff_eq_C.mp hq0
  let e := algebraMap (B K) (E K)
  let g := algebraMap K (E K)
  have hC (a : K) : e (MvPolynomial.C a) = g a :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
  apply ht (p.coeff 0 / q.coeff 0)
  calc
    t = e p / e q := hr.symm
    _ = e (MvPolynomial.C (p.coeff 0)) / e (MvPolynomial.C (q.coeff 0)) := by
      exact congrArg₂ (fun x y : B K => e x / e y) hpC hqC
    _ = g (p.coeff 0 / q.coeff 0) := by rw [hC, hC, map_div₀]

/-- The normalized source obstruction now consumes common rational
representations of the actual velocities, not a supplied derivative
factor, reduced parameter, affine chart or trace identity. -/
theorem rationalCharacteristic_commonParameter_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (t : E K) (A Q : Fin 3 → P K)
    (hq : ∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hv : ∀ i, V (.inr i) = (A i).eval₂ (algebraMap K (E K)) t /
      (Q i).eval₂ (algebraMap K (E K)) t) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  obtain ⟨U, s, hs, hn⟩ := rationalCharacteristic_commonParameter_factor V t A Q hq hv
  by_cases ht : ∃ c : K, t = algebraMap K (E K) c
  · obtain ⟨c, hc⟩ := ht
    have hz : rationalCharacteristicJacobian V = 0 := by
      apply Matrix.ext
      intro i j
      rw [hn, hc, Derivation.map_algebraMap, mul_zero] <;> rfl
    exact rationalCharacteristic_rankZero_adjugate_annihilator a L V hdet hV hreg hgrad hz
  · have hnc (c : K) : t ≠ algebraMap K (E K) c := fun hc => ht ⟨c, hc⟩
    obtain ⟨p, q, hqn, hcop, hpos, hr⟩ := rationalParameter_exists_reduced_nonconstant t hnc
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
      apply rationalCharacteristicHessian_det_ne_zero a L hreg
      rw [rationalCharacteristicHessian_eq_slice_hessian]
      change ((algebraMap (B K) (E K)).mapMatrix (hessian (referenceSlice a L))).det = 0
      rw [← RingHom.map_det, hz, map_zero]
    obtain ⟨b, hb0, hb⟩ := rankOne_exists_constant_leftKernel_of_derivative_factor
      (referenceSlice a L) (rationalCharacteristicJacobian V) p q U s hs hqn hcop hpos
      (by intro i j; rw [hr]; exact hn i j) h3 hself hf
    obtain ⟨d, hd0, hd⟩ :=
      rationalCharacteristic_exists_annihilator_of_constant_leftKernel V hV b hb0 hb
    exact ⟨d, hd0, rationalCharacteristic_adjugate_annihilator a L V d hdet hV hreg hgrad hd⟩

end
end HC4.Polynomial.RankThreeCubic
