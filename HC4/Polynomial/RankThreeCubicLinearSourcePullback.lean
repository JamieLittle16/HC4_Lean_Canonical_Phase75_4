import HC4.Polynomial.RankThreeCubicLinearTransport
import HC4.Polynomial.RankThreeCubicNilpotentSquare
import Mathlib.Tactic

/-!
# Source pullback for nilpotent linear cubic characteristics

The substitution `x ↦ a+t, y ↦ (I+tN)y` is injective for `N^3=0`.
Its polynomial left inverse uses `I-tN+t²N²`.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private theorem nilpotent_shear_inverse_matrix
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (t : K) :
    (1 + t • N) * (1 - t • N + (t • N) ^ 2) = 1 := by
  let A : Matrix (Fin 3) (Fin 3) K := t • N
  have hpow : A ^ 3 = 0 := by
    change (t • N) ^ 3 = 0
    rw [smul_pow, hN, smul_zero]
  change (1 + A) * (1 - A + A ^ 2) = 1
  calc
    (1 + A) * (1 - A + A ^ 2) = 1 + A ^ 3 := by noncomm_ring
    _ = 1 := by rw [hpow, add_zero]

private theorem nilpotent_shear_inverse_mulVec
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (t : K)
    (v : Fin 3 → K) :
    (1 + t • N) *ᵥ ((1 - t • N + (t • N) ^ 2) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, nilpotent_shear_inverse_matrix N hN t,
    Matrix.one_mulVec]

/-- Injectivity of the actual three-transverse-variable characteristic
substitution, without choosing a Jordan basis. -/
theorem linearLineEval_injective_of_cube_zero [CharZero K]
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) :
    Function.Injective
      (linearLineEval a N : MvPolynomial (Unit ⊕ Fin 3) K →
        _root_.Polynomial (MvPolynomial (Fin 3) K)) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro b
  let t : K := b (.inl ()) - a
  let v : Fin 3 → K := fun j => b (.inr j)
  let z : Fin 3 → K := (1 - t • N + (t • N) ^ 2) *ᵥ v
  let B := MvPolynomial (Fin 3) K
  let e : B →ₐ[K] K := MvPolynomial.aeval z
  let ev : _root_.Polynomial B →ₐ[K] K :=
    e.comp ((_root_.Polynomial.aeval (MvPolynomial.C t) :
      _root_.Polynomial B →ₐ[B] B).restrictScalars K)
  have hz : (1 + t • N) *ᵥ z = v :=
    nilpotent_shear_inverse_mulVec N hN t v
  have hcoords (i : Fin 3) : z i + t * ∑ j, N i j * z j = v i := by
    have h' : z + t • (N *ᵥ z) = v := by
      simpa only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] using hz
    have hi := congrFun h' i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct] using hi
  have h : ev.comp (linearLineEval a N) = MvPolynomial.aeval b := by
    ext i
    have hC (r : K) : e (MvPolynomial.C r) = r := e.commutes r
    have hX (j : Fin 3) : e (X j) = z j := MvPolynomial.aeval_X z j
    have heval (r s : B) :
        ev (_root_.Polynomial.C r + _root_.Polynomial.C s * _root_.Polynomial.X) =
          e r + e s * t := by
      change e (_root_.Polynomial.eval (MvPolynomial.C t)
        (_root_.Polynomial.C r + _root_.Polynomial.C s * _root_.Polynomial.X)) = _
      rw [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_C,
        _root_.Polynomial.eval_X, map_add, map_mul, hC]
    have hL (j : Unit ⊕ Fin 3) : linearLineEval a N (X j) =
        _root_.Polynomial.C (Sum.elim (fun _ : Unit => MvPolynomial.C a) X j) +
        _root_.Polynomial.C
          (Sum.elim (fun _ : Unit => (1 : B))
            (fun k : Fin 3 => ∑ m, MvPolynomial.C (N k m) * X m) j) *
          _root_.Polynomial.X :=
      MvPolynomial.aeval_X _ j
    have hf (j : Unit ⊕ Fin 3) : ev (linearLineEval a N (X j)) = b j := by
      rw [hL, heval]
      cases j with
      | inl u =>
        cases u
        simp [hC, t]
      | inr k =>
        have hsum : e (∑ m, MvPolynomial.C (N k m) * X m) =
            ∑ m, N k m * z m := by simp [map_sum, map_mul, hC, hX]
        simpa [hX, hsum, hC, v, mul_comm] using hcoords k
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hf i
  have he := congrArg ev hpq
  change (ev.comp (linearLineEval a N)) p =
    (ev.comp (linearLineEval a N)) q at he
  rw [h] at he
  exact he

/-- An invariant square on the reference characteristic pulls back to
an identity on the original source polynomial. -/
theorem square_pullback_of_transport [CharZero K]
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (P U : MvPolynomial (Unit ⊕ Fin 3) K)
    (Q V : MvPolynomial (Fin 3) K) (c : K)
    (hP : linearLineEval a N P = _root_.Polynomial.C Q)
    (hU : linearLineEval a N U = _root_.Polynomial.C V)
    (hsq : Q = MvPolynomial.C c * V ^ 2) :
    P = MvPolynomial.C c * U ^ 2 := by
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
        (_root_.Polynomial.C V) ^ 2 := by rw [hsq, map_mul, map_pow]
    _ = linearLineEval a N (MvPolynomial.C c * U ^ 2) := by
        rw [map_mul, map_pow, hU, hc]

/-- A transverse linear form is invariant under the characteristic shear
when its coefficient row annihilates the velocity matrix. -/
theorem linearLineEval_invariant_transverseForm
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (l : Fin 3 → K) (hl : l ᵥ* N = 0) :
    linearLineEval a N
      (∑ i : Fin 3, (MvPolynomial.C (l i) :
        MvPolynomial (Unit ⊕ Fin 3) K) * X (.inr i)) =
      _root_.Polynomial.C (constantLinearForm l) := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hzero (j : Fin 3) : ∑ i : Fin 3, l i * N i j = 0 := by
    simpa [Matrix.vecMul, dotProduct] using congrFun hl j
  have hcore : (∑ i : Fin 3, MvPolynomial.C (l i) *
      (∑ j : Fin 3, MvPolynomial.C (N i j) * (X j : B))) = 0 := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          MvPolynomial.C (l i * N i j) * (X j : B) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, ← map_mul]
      _ = ∑ j : Fin 3, ∑ i : Fin 3,
          MvPolynomial.C (l i * N i j) * (X j : B) := by rw [Finset.sum_comm]
      _ = ∑ j : Fin 3, MvPolynomial.C (∑ i : Fin 3, l i * N i j) * X j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_mul, map_sum]
      _ = 0 := by simp [hzero]
  have heval :
      linearLineEval a N
        (∑ i : Fin 3, (MvPolynomial.C (l i) :
          MvPolynomial (Unit ⊕ Fin 3) K) * X (.inr i)) =
        ∑ i : Fin 3, _root_.Polynomial.C (MvPolynomial.C (l i)) *
          (_root_.Polynomial.C (X i : B) +
            _root_.Polynomial.C (∑ j : Fin 3, MvPolynomial.C (N i j) * X j) *
              _root_.Polynomial.X) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  rw [heval]
  calc
    _ = _root_.Polynomial.C (constantLinearForm l) +
        _root_.Polynomial.C
          (∑ i : Fin 3, MvPolynomial.C (l i) *
            (∑ j : Fin 3, MvPolynomial.C (N i j) * (X j : B))) *
          _root_.Polynomial.X := by
            simp [constantLinearForm, map_sum, map_mul, Finset.sum_add_distrib,
              Finset.sum_mul, mul_add, mul_assoc]
    _ = _root_.Polynomial.C (constantLinearForm l) := by simp [hcore]

/-- The fixed-square identity on the reference cubic pulls back to the
actual cubic polynomial along a nilpotent linear characteristic. -/
theorem source_square_of_linear_characteristic [CharZero K]
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (d l : Fin 3 → K) (c : K)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (hl : l ᵥ* N = 0)
    (hsq : constantDirectional d (referenceSlice a L) =
      MvPolynomial.C c * constantLinearForm l ^ 2) :
    (∑ i : Fin 3,
      (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
        pderiv (.inr i) L) =
      MvPolynomial.C c *
        (∑ i : Fin 3,
          (MvPolynomial.C (l i) : MvPolynomial (Unit ⊕ Fin 3) K) *
          X (.inr i)) ^ 2 := by
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
  exact square_pullback_of_transport a N hN _ _ _ _ c hdir
    (linearLineEval_invariant_transverseForm a N l hl) hsq

end
end HC4.Polynomial.RankThreeCubic
