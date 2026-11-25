import HC4.Polynomial.RationalCharacteristicPullback
import HC4.Polynomial.RankThreeCubicSquarefreePoleFinal
import HC4.Polynomial.RankThreeCubicPoleReducedDenominator

/-!
# Constants of the transverse rational partial derivatives

The reduced numerator and denominator of a rational function with
vanishing partials satisfy the cross-multiplied quotient equations.
Relative primality forces the denominator to divide each of its
partials. Strict total-degree descent makes each such partial zero.
The numerator is then constant as well.

This supplies the rank-zero characteristic case and converts any
constant left-kernel relation of the velocity Jacobian to an affine
relation of the actual velocity. No rank-one or rank-two
classification is assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- A polynomial killed by all transverse partials is constant. -/
theorem transverse_eq_C_of_all_pderiv_zero
    (p : B K) (hp : ∀ i : Fin 3, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  have he : transverseEuler p = (0 : ℕ) • p := by
    simp [transverseEuler, hp]
  have hh := isHomogeneous_of_transverseEuler_eq_nsmul p 0 he
  exact totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hh)

/-- A polynomial dividing one of its first partials has that partial
zero. This is a degree argument, not a squarefree assumption. -/
theorem transverse_pderiv_zero_of_dvd
    (q : B K) (i : Fin 3) (hq : q ≠ 0) (hd : q ∣ pderiv i q) :
    pderiv i q = 0 := by
  by_cases hdeg : q.totalDegree = 0
  · have hc := totalDegree_eq_zero_iff_eq_C.mp hdeg
    rw [hc, pderiv_C]
  · by_contra hn
    obtain ⟨u, hu⟩ := hd
    have hu0 : u ≠ 0 := by
      intro hz
      apply hn
      rw [hu, hz, mul_zero]
    have h := totalDegree_pderiv_lt_of_totalDegree_pos q i (Nat.pos_of_ne_zero hdeg)
    have he : (pderiv i q).totalDegree = q.totalDegree + u.totalDegree := by
      rw [hu]
      exact totalDegree_mul_of_isDomain hq hu0
    omega

/-- The joint constant field of the three localized partials is
exactly the original ground field. -/
theorem rationalCharacteristicPartial_constants
    (z : E K) (hz : ∀ i : Fin 3, rationalCharacteristicPartial i z = 0) :
    ∃ c : K, z = algebraMap K (E K) c := by
  classical
  let f : B K →+* E K := algebraMap (B K) (E K)
  let p : B K := IsFractionRing.num (B K) z
  let q : B K := IsFractionRing.den (B K) z
  have hq : q ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) z)
  have hqf : f q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hrepr : f p / f q = z := IsFractionRing.mk'_num_den' (B K) z
  have hmul : z * f q = f p := by
    rw [← hrepr, div_mul_cancel₀ _ hqf]
  have hcop : IsRelPrime q p :=
    (IsFractionRing.num_den_reduced (B K) z).symm
  have hdiff (i : Fin 3) : z * f (pderiv i q) = f (pderiv i p) := by
    have h := congrArg (rationalCharacteristicPartial i) hmul
    change rationalCharacteristicPartial i (z * f q) =
      rationalCharacteristicPartial i (f p) at h
    rw [Derivation.leibniz, hz i] at h
    change z * rationalCharacteristicPartial i (f q) +
      f q * 0 = rationalCharacteristicPartial i (f p) at h
    simpa [f] using h
  have hcross (i : Fin 3) : pderiv i p * q = pderiv i q * p := by
    apply IsFractionRing.injective (B K) (E K)
    change f (pderiv i p * q) = f (pderiv i q * p)
    simp only [map_mul]
    calc
      f (pderiv i p) * f q = (z * f (pderiv i q)) * f q := by rw [hdiff]
      _ = f (pderiv i q) * (z * f q) := by ring
      _ = f (pderiv i q) * f p := by rw [hmul]
  have hqzero (i : Fin 3) : pderiv i q = 0 := by
    apply transverse_pderiv_zero_of_dvd q i hq
    apply hcop.dvd_of_dvd_mul_right
    refine ⟨pderiv i p, ?_⟩
    rw [← hcross i, mul_comm]
  have hpzero (i : Fin 3) : pderiv i p = 0 := by
    apply IsFractionRing.injective (B K) (E K)
    change f (pderiv i p) = f 0
    rw [← hdiff i, hqzero i, map_zero, mul_zero]
  have hpC := transverse_eq_C_of_all_pderiv_zero p hpzero
  have hqC := transverse_eq_C_of_all_pderiv_zero q hqzero
  refine ⟨p.coeff 0 / q.coeff 0, ?_⟩
  have hc (c : K) : f (MvPolynomial.C c) = algebraMap K (E K) c :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes c
  calc
    z = f p / f q := hrepr.symm
    _ = f (MvPolynomial.C (p.coeff 0)) / f (MvPolynomial.C (q.coeff 0)) := by
      conv_lhs => rw [hpC, hqC]
    _ = algebraMap K (E K) (p.coeff 0 / q.coeff 0) := by
      rw [hc, hc, map_div₀]

/-- A constant left-kernel vector of the velocity Jacobian integrates
to an affine dependence with a ground-field constant. -/
theorem rationalCharacteristic_affine_of_constant_leftKernel
    (V : I → E K) (b : Fin 3 → K)
    (hb : (fun i => algebraMap K (E K) (b i)) ᵥ*
      rationalCharacteristicJacobian V = 0) :
    ∃ c : K, (∑ i : Fin 3, algebraMap K (E K) (b i) * V (.inr i)) =
      algebraMap K (E K) c := by
  apply rationalCharacteristicPartial_constants
  intro j
  have h := congrFun hb j
  change (∑ i : Fin 3, algebraMap K (E K) (b i) *
    rationalCharacteristicPartial j (V (.inr i))) = 0 at h
  rw [map_sum]
  simp only [Derivation.leibniz, Derivation.map_algebraMap, smul_eq_mul,
    mul_zero, add_zero]
  exact h

/-- A zero velocity Jacobian forces all transverse velocity
components to be ground-field constants. -/
theorem rationalCharacteristic_constant_of_jacobian_zero
    (V : I → E K) (hN : rationalCharacteristicJacobian V = 0) :
    ∃ c : Fin 3 → K, ∀ i : Fin 3, V (.inr i) = algebraMap K (E K) (c i) := by
  classical
  have h (i : Fin 3) : ∃ c : K, V (.inr i) = algebraMap K (E K) c := by
    apply rationalCharacteristicPartial_constants
    intro j
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (E K) => M i j) hN
  choose c hc using h
  exact ⟨c, hc⟩

/-- Convert an affine relation on the transverse velocity into the
constant four-dimensional annihilator required by the adjugate bridge. -/
theorem rationalCharacteristic_exists_annihilator_of_constant_leftKernel
    (V : I → E K) (hV : V (.inl ()) = 1)
    (b : Fin 3 → K) (hb0 : b ≠ 0)
    (hb : (fun i => algebraMap K (E K) (b i)) ᵥ*
      rationalCharacteristicJacobian V = 0) :
    ∃ d : I → K, d ≠ 0 ∧ ∑ i : I, algebraMap K (E K) (d i) * V i = 0 := by
  obtain ⟨c, hc⟩ := rationalCharacteristic_affine_of_constant_leftKernel V b hb
  let d : I → K := Sum.elim (fun _ => -c) b
  refine ⟨d, ?_, ?_⟩
  · intro hd
    apply hb0
    funext i
    exact congrFun hd (.inr i)
  · simp only [Fintype.sum_sum_type, Fintype.sum_unique, d, Sum.elim_inl,
      Sum.elim_inr, hV, mul_one, map_neg, hc, neg_add_cancel]

/-- Rank-zero characteristic case of the constant-annihilator theorem.
This is the global polynomial conclusion, not merely a relation at
the reference slice. -/
theorem rationalCharacteristic_rankZero_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hN : rationalCharacteristicJacobian V = 0) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  let b : Fin 3 → K := fun _ => 1
  have hb0 : b ≠ 0 := by
    intro hz
    have h := congrFun hz (0 : Fin 3)
    exact one_ne_zero h
  obtain ⟨d, hd0, hd⟩ := rationalCharacteristic_exists_annihilator_of_constant_leftKernel
    V hV b hb0 (by rw [hN, Matrix.vecMul_zero])
  exact ⟨d, hd0, rationalCharacteristic_adjugate_annihilator a L V d hdet hV hreg hgrad hd⟩

end
end HC4.Polynomial.RankThreeCubic
