import HC4.Polynomial.RationalCharacteristicAdjugate
import HC4.Polynomial.RankThreeCubicLinearSourcePullback
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Injectivity of anchored rational characteristic substitution

Use the already established stationary longitudinal chart to separate
the time variable from the transverse polynomial coefficients. A
polynomial time substitution fixing time is injective when reduction
modulo time is injective on the coefficient ring.

This argument does not require a rational inverse, nilpotence, or any
degree bound on the transverse velocity.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section TimeAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]

/-- A time-preserving polynomial homomorphism is injective if its
coefficient map is injective after taking the time-zero coefficient. -/
theorem polynomial_timeHom_injective
    (f : _root_.Polynomial R →+* _root_.Polynomial A)
    (g : R →+* A) (hg : Function.Injective g)
    (hx : f _root_.Polynomial.X = _root_.Polynomial.X)
    (hc : ∀ b : R, (f (_root_.Polynomial.C b)).coeff 0 = g b) :
    Function.Injective f := by
  have hz : ∀ (n : ℕ) (p : _root_.Polynomial R), p.natDegree ≤ n →
      f p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hp h
      have he : p = _root_.Polynomial.C (p.coeff 0) :=
        _root_.Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)
      have hh : f (_root_.Polynomial.C (p.coeff 0)) = 0 := by
        rwa [← he]
      have h0 := congrArg (fun q : _root_.Polynomial A => q.coeff 0) hh
      rw [hc, _root_.Polynomial.coeff_zero] at h0
      have hcoeff : p.coeff 0 = 0 := hg (h0.trans g.map_zero.symm)
      rw [he, hcoeff, map_zero]
    | succ n ih =>
      intro p hp h
      have hsplit := congrArg f (_root_.Polynomial.divX_mul_X_add p)
      rw [map_add, map_mul, hx, h] at hsplit
      have h0 := congrArg (fun q : _root_.Polynomial A => q.coeff 0) hsplit
      simp only [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_mul_X_zero,
        zero_add, hc, _root_.Polynomial.coeff_zero] at h0
      have hcoeff : p.coeff 0 = 0 := hg (h0.trans g.map_zero.symm)
      rw [hcoeff, map_zero, map_zero, add_zero] at hsplit
      have hdiv : f p.divX = 0 :=
        (mul_eq_zero.mp hsplit).resolve_right _root_.Polynomial.X_ne_zero
      have hdeg : p.divX.natDegree ≤ n := by
        rw [_root_.Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        omega
      have hq := ih p.divX hdeg hdiv
      have hh := _root_.Polynomial.divX_mul_X_add p
      rw [hq, hcoeff, zero_mul, map_zero, add_zero] at hh
      exact hh.symm
  intro p q hpq
  apply sub_eq_zero.mp
  apply hz (p - q).natDegree (p - q) le_rfl
  rw [map_sub, hpq, sub_self]

end TimeAlgebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev I := Unit ⊕ Fin 3
private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- The normalized rational line substitution is injective on the
original polynomial source. Only the longitudinal normalization is
needed; the transverse velocities are arbitrary rational functions. -/
theorem rationalLineEval_injective
    (a : K) (V : I → E K) (hV : V (.inl ()) = 1) :
    Function.Injective (lineEval (K := K) (transverseGenericPoint a) V) := by
  classical
  let g : B K →+* E K := algebraMap (B K) (E K)
  let z : Fin 3 → E K := fun i => g (X i)
  let v : Fin 3 → E K := fun i => V (.inr i)
  let phi : B K →ₐ[K] _root_.Polynomial (E K) := lineEval z v
  let f : _root_.Polynomial (B K) →+* _root_.Polynomial (E K) :=
    _root_.Polynomial.eval₂RingHom phi.toRingHom _root_.Polynomial.X
  have hphi0 (b : B K) : (phi b).coeff 0 = g b := by
    change (lineEval z v b).coeff 0 = g b
    rw [cubic_lineEval_coeff_zero]
    have he : (MvPolynomial.aeval z : B K →ₐ[K] E K).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro r
        calc
          MvPolynomial.aeval z (MvPolynomial.C r) = algebraMap K (E K) r :=
            (MvPolynomial.aeval z).commutes r
          _ = g (MvPolynomial.C r) :=
            ((IsScalarTower.toAlgHom K (B K) (E K)).commutes r).symm
      · intro i
        exact MvPolynomial.aeval_X z i
    exact RingHom.congr_fun he b
  have hfC (b : B K) : f (_root_.Polynomial.C b) = phi b := by
    change (_root_.Polynomial.C b).eval₂ phi.toRingHom _root_.Polynomial.X = phi b
    rw [_root_.Polynomial.eval₂_C]
  have hfX : f _root_.Polynomial.X = _root_.Polynomial.X := by
    change (_root_.Polynomial.X : _root_.Polynomial (B K)).eval₂
      phi.toRingHom _root_.Polynomial.X = _root_.Polynomial.X
    rw [_root_.Polynomial.eval₂_X]
  have hf : Function.Injective f :=
    polynomial_timeHom_injective f g (IsFractionRing.injective (B K) (E K))
      hfX (fun b => by rw [hfC, hphi0])
  let N : Matrix (Fin 3) (Fin 3) K := 0
  let e0 := linearLineEval a N
  let e := lineEval (K := K) (transverseGenericPoint a) V
  have hN : N ^ 3 = 0 := by simp [N]
  have he0 : Function.Injective e0 :=
    linearLineEval_injective_of_cube_zero a N hN
  have hphiC (r : K) : phi (MvPolynomial.C r) =
      _root_.Polynomial.C (algebraMap K (E K) r) := by
    simp [phi, lineEval, IsScalarTower.algebraMap_apply K (E K)
      (_root_.Polynomial (E K)), _root_.Polynomial.algebraMap_eq]
  have hcomp : f.comp e0.toRingHom = e.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (e0 (MvPolynomial.C r)) = e (MvPolynomial.C r)
      have hc : e0 (MvPolynomial.C r) =
          _root_.Polynomial.C (MvPolynomial.C r : B K) := by
        simp [e0, linearLineEval, lineEval, IsScalarTower.algebraMap_apply K (B K)
          (_root_.Polynomial (B K)), _root_.Polynomial.algebraMap_eq]
      rw [hc, hfC, hphiC]
      simp [e, lineEval, IsScalarTower.algebraMap_apply K (E K)
        (_root_.Polynomial (E K)), _root_.Polynomial.algebraMap_eq]
    · intro i
      change f (e0 (X i)) = e (X i)
      cases i with
      | inl u =>
        cases u
        have hx : e0 (X (.inl ())) =
            _root_.Polynomial.C (MvPolynomial.C a : B K) + _root_.Polynomial.X := by
          simp [e0, linearLineEval, lineEval]
        rw [hx, map_add, hfC, hphiC, hfX]
        simp [e, lineEval, transverseGenericPoint, hV]
      | inr j =>
        have hx : e0 (X (.inr j)) = _root_.Polynomial.C (X j : B K) := by
          simp [e0, linearLineEval, lineEval, N]
        rw [hx, hfC]
        simp [phi, e, lineEval, transverseGenericPoint, z, v, g]
  intro p q hpq
  apply he0
  apply hf
  change (f.comp e0.toRingHom) p = (f.comp e0.toRingHom) q
  rw [hcomp]
  exact hpq

/-- The constant annihilator of a normalized rational characteristic
lifts to an identity on the original source adjugate, with no
additional injectivity hypothesis. -/
theorem rationalCharacteristic_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K) (d : I → K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hd : ∑ i : I, algebraMap K (E K) (d i) * V i = 0) :
    (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 :=
  rationalCharacteristic_adjugate_annihilator_of_injective
    a L V d hdet hV hreg hgrad hd (rationalLineEval_injective a V hV)

end
end HC4.Polynomial.RankThreeCubic
