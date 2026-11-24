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
  refine ⟨d, l, c, hd, hl, hc, hNd, hlN, ?_⟩
  exact source_power_of_linear_characteristic a N h3 L d l c n
    hgrad hlN hsq

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
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hL
  exact exists_source_power_of_nonzero_linear_characteristic a N L (n + 1)
    hN hreg hq hgrad

end
end HC4.Polynomial.RankThreeCubic
