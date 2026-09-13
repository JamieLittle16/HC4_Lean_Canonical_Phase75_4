import HC4.Polynomial.CodimensionTwoWeightedDeparturePencil
import HC4.Polynomial.NestedPolynomialPowerInflation
import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.Tactic

/-!
# Honest trinomial to codimension-two departure pencil

This file connects the abstract exponent-core pencil to an actual polynomial.
For

    v = (p,D-p,0,0),
    u = (a,D-m-a,m,0),
    w = (c,D-n-c,0,n),

and nonzero or arbitrary coefficients `C,A,B`, form the honest trinomial

    C x^v + A x^u + B x^w.

The Euler-scaled Hessian of a monomial is the same monomial times its exponent
core `M(d)=d dᵀ-diag(d)`.  Under the nested specialisation

    x0,x1 |-> 1,
    x2    |-> s,
    x3    |-> t,

this becomes

    C M(v) + A s^m M(u) + B t^n M(w).

That matrix is exactly the positive-power inflation of the abstract weighted
pencil.  Therefore, for `m,n>0`, singularity of the honest trinomial implies
singularity of the abstract weighted pencil by injectivity of nested power
inflation.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators
open MvPolynomial

noncomputable section

/-- Four-coordinate finitely supported exponent. -/
def fourExponentFinsupp
    (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) a +
    Finsupp.single (1 : Fin 4) b +
    Finsupp.single (2 : Fin 4) c +
    Finsupp.single (3 : Fin 4) d

@[simp] theorem fourExponentFinsupp_apply
    (a b c d : ℕ) (i : Fin 4) :
    fourExponentFinsupp a b c d i = ![a,b,c,d] i := by
  fin_cases i <;> simp [fourExponentFinsupp]

/-- Honest three-monomial carrier used by the codimension-two local algebra. -/
noncomputable def codimensionTwoTrinomial
    {K : Type*} [CommRing K]
    (D p a m c n : ℕ) (C A B : K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.monomial
      (fourExponentFinsupp p (D-p) 0 0) C +
    MvPolynomial.monomial
      (fourExponentFinsupp a (D-m-a) m 0) A +
    MvPolynomial.monomial
      (fourExponentFinsupp c (D-n-c) 0 n) B

/-- Euler differentiation of an arbitrary monomial multiplies by its exponent. -/
theorem mvEuler_monomial_general
    {K : Type*} [Field K] [CharZero K]
    (d : Fin 4 →₀ ℕ) (c : K) (i : Fin 4) :
    mvEuler i (MvPolynomial.monomial d c) =
      MvPolynomial.C ((d i : ℕ) : K) * MvPolynomial.monomial d c := by
  unfold mvEuler
  rw [MvPolynomial.X_mul_pderiv_monomial]
  simp [nsmul_eq_mul]

/-- Euler-scaled Hessian of a monomial is its exponent Hessian core times the
same monomial. -/
theorem eulerScaledHessian_monomial_general
    {K : Type*} [Field K] [CharZero K]
    (d : Fin 4 →₀ ℕ) (c : K) (i j : Fin 4) :
    eulerScaledHessian (MvPolynomial.monomial d c) i j =
      MvPolynomial.C
        (vectorHessianCore (K := K) (fun k => ((d k : ℕ) : K)) i j) *
        MvPolynomial.monomial d c := by
  change
    mvEuler i (mvEuler j (MvPolynomial.monomial d c)) -
        (if i = j then mvEuler i (MvPolynomial.monomial d c) else 0) = _
  rw [mvEuler_monomial_general]
  rw [mvEuler_C_mul]
  rw [mvEuler_monomial_general]
  by_cases hij : i = j
  · subst j
    simp [vectorHessianCore, MvPolynomial.C_mul]
    ring
  · simp [hij, vectorHessianCore, MvPolynomial.C_mul]
    ring

/-- Base-coefficient embedding into `K[t][s]`. -/
def nestedCoefficientHom
    {K : Type*} [CommRing K] :
    K →+* Polynomial (Polynomial K) :=
  (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
    (Polynomial.C : K →+* Polynomial K)

/-- Specialisation `x0=x1=1`, `x2=s`, `x3=t` into the nested polynomial
ring `K[t][s]`. -/
noncomputable def codimensionTwoSTSpecialisation
    {K : Type*} [CommRing K] :
    MvPolynomial (Fin 4) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom nestedCoefficientHom
    ![(1 : Polynomial (Polynomial K)),
      1,
      Polynomial.X,
      Polynomial.C Polynomial.X]

@[simp] theorem codimensionTwoSTSpecialisation_C
    {K : Type*} [CommRing K] (c : K) :
    codimensionTwoSTSpecialisation (K := K) (MvPolynomial.C c) =
      Polynomial.C (Polynomial.C c) := by
  simp [codimensionTwoSTSpecialisation, nestedCoefficientHom]

/-- Exact specialisation of one four-variable monomial. -/
theorem codimensionTwoSTSpecialisation_monomial
    {K : Type*} [CommRing K]
    (a b c d : ℕ) (z : K) :
    codimensionTwoSTSpecialisation (K := K)
        (MvPolynomial.monomial (fourExponentFinsupp a b c d) z) =
      Polynomial.C (Polynomial.C z) *
        Polynomial.X ^ c *
        Polynomial.C (Polynomial.X ^ d) := by
  rw [MvPolynomial.eval₂_monomial]
  simp [codimensionTwoSTSpecialisation, nestedCoefficientHom,
    fourExponentFinsupp, Finsupp.prod_fintype, Fin.prod_univ_four]
  ring

/-- Specialised Euler-Hessian of the honest trinomial is exactly the
positive-power inflation of the coefficient-weighted abstract pencil. -/
theorem codimensionTwoSTSpecialisation_eulerScaledHessian_trinomial
    {K : Type*} [Field K] [CharZero K]
    (D p a m c n : ℕ) (C A B : K) :
    (codimensionTwoSTSpecialisation (K := K)).mapMatrix
        (eulerScaledHessian
          (codimensionTwoTrinomial D p a m c n C A B)) =
      (nestedPolynomialPowerInflation (K := K) m n).mapMatrix
        (codimensionTwoWeightedDeparturePencil
          (D : K) (p : K) (a : K) (m : K)
          (c : K) (n : K) C A B) := by
  ext i j
  simp only [Matrix.map_apply]
  unfold codimensionTwoTrinomial
  have hadd (P Q : MvPolynomial (Fin 4) K) :
      eulerScaledHessian (P + Q) i j =
        eulerScaledHessian P i j + eulerScaledHessian Q i j := by
    simp [eulerScaledHessian, mvEuler]
    ring
  rw [hadd, hadd]
  rw [eulerScaledHessian_monomial_general,
    eulerScaledHessian_monomial_general,
    eulerScaledHessian_monomial_general]
  simp only [map_add, map_mul, codimensionTwoSTSpecialisation_C]
  rw [codimensionTwoSTSpecialisation_monomial,
    codimensionTwoSTSpecialisation_monomial,
    codimensionTwoSTSpecialisation_monomial]
  fin_cases i <;> fin_cases j <;>
    simp [codimensionTwoWeightedDeparturePencil,
      nestedPolynomialPowerInflation, innerPowerInflation,
      vectorHessianCore] <;> ring

/-- **Honest trinomial singularity implies singularity of the abstract
coefficient-weighted departure pencil.** -/
theorem det_codimensionTwoWeightedDeparturePencil_eq_zero_of_trinomial_hessian_zero
    {K : Type*} [Field K] [CharZero K]
    {D p a m c n : ℕ} {C A B : K}
    (hm : 0 < m) (hn : 0 < n)
    (hzero :
      hessianDeterminant
        (codimensionTwoTrinomial D p a m c n C A B) = 0) :
    (codimensionTwoWeightedDeparturePencil
      (D : K) (p : K) (a : K) (m : K)
      (c : K) (n : K) C A B).det = 0 := by
  let F := codimensionTwoTrinomial D p a m c n C A B
  let phi := codimensionTwoSTSpecialisation (K := K)
  let ram := nestedPolynomialPowerInflation (K := K) m n
  let Q := codimensionTwoWeightedDeparturePencil
    (D : K) (p : K) (a : K) (m : K)
    (c : K) (n : K) C A B

  have hEulerDet : (eulerScaledHessian F).det = 0 := by
    rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
    rw [hzero]
    simp
  have hmapped : (phi.mapMatrix (eulerScaledHessian F)).det = 0 := by
    rw [← phi.map_det]
    rw [hEulerDet]
    simp
  have hmatrix :
      phi.mapMatrix (eulerScaledHessian F) = ram.mapMatrix Q := by
    simpa [F, phi, ram, Q] using
      codimensionTwoSTSpecialisation_eulerScaledHessian_trinomial
        (K := K) D p a m c n C A B
  rw [hmatrix] at hmapped
  have hramdet : ram Q.det = 0 := by
    rw [ram.map_det]
    exact hmapped
  exact
    (nestedPolynomialPowerInflation_injective
      (K := K) hm hn)
      (by simpa [ram, Q] using hramdet)

end

end HC4.Polynomial
