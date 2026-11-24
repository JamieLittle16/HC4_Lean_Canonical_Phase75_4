import HC4.Polynomial.TransverseLeadingLinearClassification
import HC4.Polynomial.RankThreeCubicLinearSquareAssembly
import Mathlib.Tactic

/-!
# Fixed directional power for arbitrary homogeneous leading layers

The last nonzero power of a nonzero nilpotent transverse velocity
has rank one. Self-adjointness for the reference Hessian and homogeneous
Euler rigidity give a fixed linear form power in the corresponding
direction. The injective polynomial shear carries that identity back
to the original leading layer. No assertion about lower source grades
or the determinant of a nonlinearly transformed full potential is made.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

theorem power_pullback_of_transport [CharZero K]
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (P U : MvPolynomial (Unit ⊕ Fin 3) K)
    (Q V : MvPolynomial (Fin 3) K) (c : K) (n : ℕ)
    (hP : linearLineEval a N P = _root_.Polynomial.C Q)
    (hU : linearLineEval a N U = _root_.Polynomial.C V)
    (hsq : Q = MvPolynomial.C c * V ^ n) :
    P = MvPolynomial.C c * U ^ n := by
  have hc : linearLineEval a N (MvPolynomial.C c) =
      _root_.Polynomial.C (MvPolynomial.C c) := by
    simp [linearLineEval, lineEval,
      IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
        (_root_.Polynomial (MvPolynomial (Fin 3) K)),
      _root_.Polynomial.algebraMap_eq]
  apply linearLineEval_injective_of_cube_zero a N hN
  calc
    linearLineEval a N P = _root_.Polynomial.C Q := hP
    _ = _root_.Polynomial.C (MvPolynomial.C c) *
        (_root_.Polynomial.C V) ^ n := by rw [hsq, map_mul, map_pow]
    _ = linearLineEval a N (MvPolynomial.C c * U ^ n) := by
        rw [map_mul, map_pow, hU, hc]

theorem source_power_of_linear_characteristic [CharZero K]
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (d l : Fin 3 → K) (c : K) (n : ℕ)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (hl : l ᵥ* N = 0)
    (hsq : constantDirectional d (referenceSlice a L) =
      MvPolynomial.C c * constantLinearForm l ^ n) :
    (∑ i : Fin 3,
      (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
        pderiv (.inr i) L) =
      MvPolynomial.C c *
        (∑ i : Fin 3,
          (MvPolynomial.C (l i) : MvPolynomial (Unit ⊕ Fin 3) K) *
          X (.inr i)) ^ n := by
  have hdir :
      linearLineEval a N
        (∑ i : Fin 3,
          (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
            pderiv (.inr i) L) =
        _root_.Polynomial.C (constantDirectional d (referenceSlice a L)) := by
    have hc (r : K) :
        linearLineEval a N (MvPolynomial.C r) =
          _root_.Polynomial.C (MvPolynomial.C r) := by
      simp [linearLineEval, lineEval,
        IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
          (_root_.Polynomial (MvPolynomial (Fin 3) K)),
        _root_.Polynomial.algebraMap_eq]
    calc
      _ = ∑ i : Fin 3,
            linearLineEval a N (MvPolynomial.C (d i)) *
              linearLineEval a N (pderiv (.inr i) L) := by
              simp only [map_sum, map_mul]
      _ = ∑ i : Fin 3,
            _root_.Polynomial.C (MvPolynomial.C (d i)) *
              _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hc, hgrad i]
      _ = _root_.Polynomial.C (constantDirectional d (referenceSlice a L)) := by
              simp [constantDirectional, referenceSlice_pderiv, map_sum, map_mul]
  exact power_pullback_of_transport a N hN _ _ _ _ c n hdir
    (linearLineEval_invariant_transverseForm a N l hl) hsq

private theorem powerExtraction_symmetric_mul_square
    {A : Type*} [CommRing A]
    (H N : Matrix (Fin 3) (Fin 3) A)
    (hH : H.transpose = H)
    (hHN : (H * N).transpose = H * N) :
    (H * N ^ 2).transpose = H * N ^ 2 := by
  have hcomm : N.transpose * H = H * N := by
    simpa [Matrix.transpose_mul, hH] using hHN
  calc
    (H * N ^ 2).transpose = ((H * N) * N).transpose := by rw [pow_two, Matrix.mul_assoc]
    _ = N.transpose * (H * N).transpose := by rw [Matrix.transpose_mul]
    _ = N.transpose * (H * N) := by rw [hHN]
    _ = (H * N) * N := by rw [← Matrix.mul_assoc, hcomm]
    _ = H * N ^ 2 := by rw [pow_two, Matrix.mul_assoc]

private theorem powerExtraction_reference_hessian_eq_mapped_transverse
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K) :
    (referenceSlice a).toRingHom.mapMatrix
        ((hessian L).submatrix Sum.inr Sum.inr) =
      hessian (referenceSlice a L) := by
  apply Matrix.ext
  intro i j
  change referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L)) =
    pderiv j (pderiv i (referenceSlice a L))
  rw [referenceSlice_pderiv a i, referenceSlice_pderiv a j]

theorem exists_reference_power_of_nonzero_linear_characteristic
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K) (n : ℕ)
    (hNnonzero : N ≠ 0)
    (hreg : referenceSlice a
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hq : (referenceSlice a L).IsHomogeneous (n + 1))
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    ∃ (d l : Fin 3 → K) (c : K),
      d ≠ 0 ∧ l ≠ 0 ∧ c ≠ 0 ∧
      N *ᵥ d = 0 ∧ l ᵥ* N = 0 ∧
      (∑ i : Fin 3, d i * l i) = 0 ∧
      constantDirectional d (referenceSlice a L) =
        MvPolynomial.C c * constantLinearForm l ^ n := by
  classical
  have hdetN := det_linearCharacteristic_eq_one a N L hreg hgrad
  have hnil := matrix_pow_card_eq_zero_of_det_linear_eq_one N hdetN
  have h3 : N ^ 3 = 0 := by simpa using hnil
  obtain ⟨r, d, l, hr, hd, hl, hfac, hNd, hlN⟩ :=
    exists_nilpotent_rankOnePower N hNnonzero h3
  let q := referenceSlice a L
  let H := hessian q
  let A := N.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
  have hqdet : H.det ≠ 0 := by
    have he := congrArg Matrix.det (powerExtraction_reference_hessian_eq_mapped_transverse a L)
    have he' : referenceSlice a
        ((hessian L).submatrix Sum.inr Sum.inr).det = H.det := by
      simpa only [← RingHom.map_det] using he
    exact he' ▸ hreg
  have hH : H.transpose = H := by
    ext i j
    simp only [Matrix.transpose_apply, H, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have hHN : (H * A).transpose = H * A :=
    reference_hessian_selfAdjoint_of_linear_transport a N L hgrad
  have hpower : (H * A ^ r).transpose = H * A ^ r := by
    rcases hr with hr | hr
    · subst r
      simpa using hHN
    · subst r
      exact powerExtraction_symmetric_mul_square H A hH hHN
  let T : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K) :=
    Matrix.vecMulVec (fun i => MvPolynomial.C (d i))
      (fun i => MvPolynomial.C (l i))
  have hmap (i j : Fin 3) :
      (A ^ r) i j = MvPolynomial.C ((N ^ r) i j) := by
    rcases hr with hr | hr
    · subst r
      simp [A]
    · subst r
      simp only [pow_two, A, Matrix.mul_apply, Matrix.map_apply,
        map_sum, map_mul]
  have hfac' : A ^ r = T := by
    apply Matrix.ext
    intro i j
    rw [hmap, hfac]
    simp [T, Matrix.vecMulVec]
  have hsquare : ∀ i j : Fin 3,
      (H * T) i j = (H * T) j i := by
    intro i j
    rw [← hfac']
    exact (congrArg (fun M : Matrix (Fin 3) (Fin 3)
      (MvPolynomial (Fin 3) K) => M i j) hpower).symm
  obtain ⟨c, hc, hsq⟩ :=
    reference_directional_eq_power_of_rankOne n q hq hqdet d l hd hl hsquare
  have hkill : N ^ r *ᵥ d = 0 := by
    rcases hr with hr | hr
    · simpa [hr] using hNd
    · rw [hr, pow_two, ← Matrix.mulVec_mulVec, hNd, Matrix.mulVec_zero]
  rw [hfac] at hkill
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by contrapose! hd; exact funext hd
  have he := congrFun hkill i
  change (∑ j : Fin 3, (d i * l j) * d j) = 0 at he
  have hz : d i * (∑ j : Fin 3, d j * l j) = 0 := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ j : Fin 3, (d i * l j) * d j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := he
  exact ⟨d, l, c, hd, hl, hc, hNd, hlN,
    (mul_eq_zero.mp hz).resolve_left hi, hsq⟩

theorem exists_source_power_of_nonzero_linear_characteristic
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K) (n : ℕ)
    (hNnonzero : N ≠ 0)
    (hreg : referenceSlice a
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hq : (referenceSlice a L).IsHomogeneous (n + 1))
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    ∃ (d l : Fin 3 → K) (c : K),
      d ≠ 0 ∧ l ≠ 0 ∧ c ≠ 0 ∧
      N *ᵥ d = 0 ∧ l ᵥ* N = 0 ∧
      (∑ i : Fin 3,
        (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
          pderiv (.inr i) L) =
        MvPolynomial.C c *
          (∑ i : Fin 3,
            (MvPolynomial.C (l i) : MvPolynomial (Unit ⊕ Fin 3) K) *
              X (.inr i)) ^ n := by
  obtain ⟨d, l, c, hd, hl, hc, hNd, hlN, _, hsq⟩ :=
    exists_reference_power_of_nonzero_linear_characteristic a N L n hNnonzero hreg hq hgrad
  have hdetN := det_linearCharacteristic_eq_one a N L hreg hgrad
  have h3 : N ^ 3 = 0 := by
    simpa using matrix_pow_card_eq_zero_of_det_linear_eq_one N hdetN
  refine ⟨d, l, c, hd, hl, hc, hNd, hlN, ?_⟩
  exact source_power_of_linear_characteristic a N h3 L d l c n hgrad hlN hsq

/-- For the true leading grade of a constant-determinant source, a
nonzero linear characteristic gives a fixed directional power of
degree m-1. The homogeneous reference-slice hypothesis is derived
from the actual transverse weight, not supplied independently. -/
theorem sourceLeading_fixedPower_of_nonzero_linear
    (F : MvPolynomial (Unit ⊕ Fin 3) K) (n : ℕ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (hN : N ≠ 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight ((n : ℤ) + 2) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N
        (pderiv (.inr i) (initialForm transverseCubicWeight ((n : ℤ) + 2) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv (.inr i) (initialForm transverseCubicWeight ((n : ℤ) + 2) F)))) :
    let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
    ∃ (d l : Fin 3 → K) (c : K),
      d ≠ 0 ∧ l ≠ 0 ∧ c ≠ 0 ∧
      N *ᵥ d = 0 ∧ l ᵥ* N = 0 ∧
      (∑ i : Fin 3,
        (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
          pderiv (.inr i) L) =
        MvPolynomial.C c *
          (∑ i : Fin 3,
            (MvPolynomial.C (l i) : MvPolynomial (Unit ⊕ Fin 3) K) *
              X (.inr i)) ^ (n + 1) := by
  let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
  have hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 2) :=
    initialForm_isWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 2) F
  have hq : (referenceSlice a L).IsHomogeneous (n + 1 + 1) := by
    apply referenceSlice_isHomogeneous_of_transverseWeight
    have he : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by
      push_cast
      <;> ring
    rw [he]
    exact hL
  exact exists_source_power_of_nonzero_linear_characteristic a N L (n + 1)
    hN hreg hq hgrad



/-! ## Repeated determinant factor in the nonstationary cubic branch -/

/-- If a symmetric matrix sends a constant direction to a multiple
of an orthogonal covector, the determinant contains that multiple
twice. The chosen coordinate is a unit, so row and column operations
introduce no nonunit factor. -/
theorem symmetric_det_square_dvd_of_isotropic_direction
    {R : Type*} [CommRing R]
    (H : Matrix (Fin 3) (Fin 3) R) (d l : Fin 3 → R) (p e : R)
    (k : Fin 3) (hk : d k * e = 1)
    (hSym : ∀ i j, H i j = H j i)
    (hHd : H *ᵥ d = fun i => p * l i)
    (horth : ∑ i : Fin 3, d i * l i = 0) :
    p^2 ∣ H.det := by
  classical
  let B := H.updateCol k (H *ᵥ d)
  let A := B.updateRow k (d ᵥ* B)
  have hBdet : B.det = d k * H.det := by
    simpa only [B, Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
      using Matrix.det_updateCol_sum H k d
  have hAdet : A.det = d k * B.det := by
    simpa only [A, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using Matrix.det_updateRow_sum B k d
  have hBcol (i : Fin 3) : B i k = p * l i := by
    have he := congrFun hHd i
    change (H *ᵥ d) i = p * l i at he
    simpa [B, Matrix.updateCol_apply] using he
  have hBother (i j : Fin 3) (hj : j ≠ k) : B i j = H i j := by
    simp [B, Matrix.updateCol_apply, hj]
  have hAcol (i : Fin 3) (hi : i ≠ k) : A i k = p * l i := by
    simp [A, Matrix.updateRow_apply, hi, hBcol]
  have hArow (j : Fin 3) (hj : j ≠ k) : A k j = p * l j := by
    have he : A k j = (d ᵥ* B) j := by simp [A, Matrix.updateRow_apply]
    rw [he]
    change (∑ i : Fin 3, d i * B i j) = _
    calc
      _ = ∑ i : Fin 3, H j i * d i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hBother i j hj, hSym i j, mul_comm]
      _ = _ := congrFun hHd j
  have hAkk : A k k = 0 := by
    have he : A k k = (d ᵥ* B) k := by simp [A, Matrix.updateRow_apply]
    rw [he]
    change (∑ i : Fin 3, d i * B i k) = 0
    calc
      _ = ∑ i : Fin 3, p * (d i * l i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hBcol]
        ring
      _ = 0 := by rw [← Finset.mul_sum, horth, mul_zero]
  have hdiv : p^2 ∣ A.det := by
    have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkcases with hk0 | hk1 | hk2
    · subst k
      refine ⟨-l 1*l 1*A 2 2 + l 1*A 1 2*l 2 +
        l 2*l 1*A 2 1 - l 2*A 1 1*l 2, ?_⟩
      rw [Matrix.det_fin_three, hAkk, hArow 1 (by decide), hArow 2 (by decide),
        hAcol 1 (by decide), hAcol 2 (by decide)]
      ring
    · subst k
      refine ⟨-A 0 0*l 2*l 2 - l 0*l 0*A 2 2 +
        l 0*l 2*A 2 0 + A 0 2*l 0*l 2, ?_⟩
      rw [Matrix.det_fin_three, hAkk, hArow 0 (by decide), hArow 2 (by decide),
        hAcol 0 (by decide), hAcol 2 (by decide)]
      ring
    · subst k
      refine ⟨-A 0 0*l 1*l 1 + A 0 1*l 1*l 0 +
        l 0*A 1 0*l 1 - l 0*A 1 1*l 0, ?_⟩
      rw [Matrix.det_fin_three, hAkk, hArow 0 (by decide), hArow 1 (by decide),
        hAcol 0 (by decide), hAcol 1 (by decide)]
      ring
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨e^2*q, ?_⟩
  calc
    H.det = e^2 * A.det := by
      rw [hAdet, hBdet]
      calc
        H.det = (d k * e)^2 * H.det := by rw [hk]; ring
        _ = _ := by ring
    _ = p^2 * (e^2*q) := by rw [hq]; ring

/-- Nonzero nilpotent linear transport of a regular cubic leading
layer forces a repeated nonconstant linear factor of the actual
reference transverse Hessian determinant. Thus squarefreeness is
not a generic assumption available in this branch. -/
theorem reference_cubic_det_linearSquare_dvd_of_nonzero_characteristic
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hN : N ≠ 0)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hq : (referenceSlice a L).IsHomogeneous 3)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    ∃ l : Fin 3 → K, l ≠ 0 ∧
      (∀ b : K, constantLinearForm l ≠ MvPolynomial.C b) ∧
      constantLinearForm l ^ 2 ∣
        referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det := by
  classical
  obtain ⟨d, l, c, hd, hl, hc, _, _, horth, hpow⟩ :=
    exists_reference_power_of_nonzero_linear_characteristic a N L 2 hN hreg hq hgrad
  let q := referenceSlice a L
  let H := hessian q
  let D : Fin 3 → MvPolynomial (Fin 3) K := fun i => MvPolynomial.C (d i)
  let E : Fin 3 → MvPolynomial (Fin 3) K := fun i => MvPolynomial.C (2*c*l i)
  let p := constantLinearForm l
  have hH (i j : Fin 3) : H i j = H j i := by
    change pderiv j (pderiv i q) = pderiv i (pderiv j q)
    rw [HC4.Newton.pderiv_comm_backport]
  have hD : H *ᵥ D = fun i => p * E i := by
    funext i
    change (H *ᵥ D) i = p * E i
    have he : (H *ᵥ D) i = pderiv i (constantDirectional d q) := by
      simp only [H, D, constantDirectional, map_sum, pderiv_C_mul,
        Matrix.mulVec, dotProduct, hessian_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [HC4.Newton.pderiv_comm_backport i j, mul_comm]
    rw [he, show constantDirectional d q = MvPolynomial.C c * p^2 from hpow]
    rw [pderiv_C_mul, pow_two, Derivation.leibniz, smul_eq_mul,
      show pderiv i p = MvPolynomial.C (l i) from pderiv_constantLinearForm l i]
    simp only [E, map_mul, map_ofNat]
    ring
  have hDE : ∑ i : Fin 3, D i * E i = 0 := by
    calc
      _ = ∑ i : Fin 3, MvPolynomial.C (2*c*(d i*l i)) := by
        apply Finset.sum_congr rfl
        intro i _
        change MvPolynomial.C (d i) * MvPolynomial.C (2*c*l i) = _
        rw [← map_mul]
        congr 1
        ring
      _ = 0 := by rw [← map_sum, ← Finset.mul_sum, horth, mul_zero, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, d k ≠ 0 := by contrapose! hd; exact funext hd
  have hunit : D k * MvPolynomial.C ((d k)⁻¹) = 1 := by
    change MvPolynomial.C (d k) * MvPolynomial.C ((d k)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  have hdiv := symmetric_det_square_dvd_of_isotropic_direction H D E p
    (MvPolynomial.C ((d k)⁻¹)) k hunit hH hD hDE
  have hdet : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det = H.det := by
    change (referenceSlice a).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = H.det
    rw [RingHom.map_det]
    exact congrArg Matrix.det (powerExtraction_reference_hessian_eq_mapped_transverse a L)
  refine ⟨l, hl, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by contrapose! hl; exact funext hl
    have he := congrArg (pderiv i) hb
    rw [pderiv_constantLinearForm, pderiv_C] at he
    exact hi (MvPolynomial.C_eq_zero.mp he)
  · rw [hdet]
    exact hdiv


end
end HC4.Polynomial.RankThreeCubic
