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
  have hpow : (t • N) ^ 3 = 0 := by
    rw [smul_pow, hN, smul_zero]
  calc
    (1 + t • N) * (1 - t • N + (t • N) ^ 2) = 1 + (t • N) ^ 3 := by
      noncomm_ring
    _ = 1 := by rw [hpow, add_zero]

private theorem nilpotent_shear_inverse_mulVec
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (t : K)
    (v : Fin 3 → K) :
    (1 + t • N) *ᵥ ((1 - t • N + (t • N) ^ 2) *ᵥ v) = v := by
  rw [← Matrix.mulVec_mulVec, nilpotent_shear_inverse_matrix N hN t,
    Matrix.one_mulVec]

/-- Injectivity of the actual three-transverse-variable characteristic
substitution, without choosing a Jordan basis. -/
theorem linearLineEval_injective_of_cube_zero
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
    have h := congrFun hz i
    simpa [Matrix.mulVec, dotProduct, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      using h
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
        simpa [hX, hsum, v] using hcoords k
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hf i
  have he := congrArg ev hpq
  change (ev.comp (linearLineEval a N)) p =
    (ev.comp (linearLineEval a N)) q at he
  rw [h] at he
  exact he

end
end HC4.Polynomial.RankThreeCubic
