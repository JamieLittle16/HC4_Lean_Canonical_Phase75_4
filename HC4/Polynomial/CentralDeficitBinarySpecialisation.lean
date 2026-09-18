import HC4.Newton.PreterminalFirstDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreMaximalHomogeneous
import Mathlib.Tactic

/-!
# Binary specialisation of a central codimension-two source layer

The central finite-staircase calculation only needs the two deficit
coordinates.  This file records the literal ring homomorphism

    (x0,x1,x2,x3) |-> (1,U,V,1)

from four-variable source polynomials to honest binary polynomials.

The two binary partial derivatives commute exactly with source partials in
coordinates `1` and `2`.  Consequently the binary Hessian determinant is
the specialisation of the ambient `(1,2)` Hessian principal minor.

No HC4 state or valuation data occur here.
-/

namespace HC4.Polynomial

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Source-to-binary specialisation `x0=x3=1, x1=U, x2=V`. -/
noncomputable def centralDeficitBinarySpecialisation :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![(1 : MvPolynomial (Fin 2) K),
      MvPolynomial.X (0 : Fin 2),
      MvPolynomial.X (1 : Fin 2),
      1]

@[simp] theorem centralDeficitBinarySpecialisation_C
    (z : K) :
    centralDeficitBinarySpecialisation (K := K) (MvPolynomial.C z) =
      MvPolynomial.C z := by
  simp [centralDeficitBinarySpecialisation]

@[simp] theorem centralDeficitBinarySpecialisation_X_zero :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (0 : Fin 4)) = 1 := by
  simp [centralDeficitBinarySpecialisation]

@[simp] theorem centralDeficitBinarySpecialisation_X_one :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (1 : Fin 4)) =
      MvPolynomial.X (0 : Fin 2) := by
  simp [centralDeficitBinarySpecialisation]

@[simp] theorem centralDeficitBinarySpecialisation_X_two :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (2 : Fin 4)) =
      MvPolynomial.X (1 : Fin 2) := by
  simp [centralDeficitBinarySpecialisation]

@[simp] theorem centralDeficitBinarySpecialisation_X_three :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (3 : Fin 4)) = 1 := by
  simp [centralDeficitBinarySpecialisation]

/-- First binary partial is the specialised source partial in coordinate 1. -/
theorem pderiv_zero_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv (0 : Fin 2)
        (centralDeficitBinarySpecialisation (K := K) F) =
      centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.pderiv (1 : Fin 4) F) := by
  apply MvPolynomial.induction_on F
  · intro z
    simp [centralDeficitBinarySpecialisation]
  · intro P Q hP hQ
    simp [hP, hQ]
  · intro P i hP
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    fin_cases i <;>
      simp [centralDeficitBinarySpecialisation,
        MvPolynomial.pderiv_mul] <;> ring

/-- Second binary partial is the specialised source partial in coordinate 2. -/
theorem pderiv_one_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv (1 : Fin 2)
        (centralDeficitBinarySpecialisation (K := K) F) =
      centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
  apply MvPolynomial.induction_on F
  · intro z
    simp [centralDeficitBinarySpecialisation]
  · intro P Q hP hQ
    simp [hP, hQ]
  · intro P i hP
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    fin_cases i <;>
      simp [centralDeficitBinarySpecialisation,
        MvPolynomial.pderiv_mul] <;> ring

/-- The binary `00` Hessian entry is the specialised source `11` entry. -/
theorem hessian_zero_zero_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (centralDeficitBinarySpecialisation (K := K) F) 0 0 =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 1) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_zero_centralDeficitBinarySpecialisation,
    pderiv_zero_centralDeficitBinarySpecialisation]

/-- The binary `11` Hessian entry is the specialised source `22` entry. -/
theorem hessian_one_one_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (centralDeficitBinarySpecialisation (K := K) F) 1 1 =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 2 2) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_one_centralDeficitBinarySpecialisation,
    pderiv_one_centralDeficitBinarySpecialisation]

/-- Mixed binary Hessian entry is the specialised source `12` entry. -/
theorem hessian_zero_one_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (centralDeficitBinarySpecialisation (K := K) F) 0 1 =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 2) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_one_centralDeficitBinarySpecialisation,
    pderiv_zero_centralDeficitBinarySpecialisation]

/-- Companion mixed entry. -/
theorem hessian_one_zero_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (centralDeficitBinarySpecialisation (K := K) F) 1 0 =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 2 1) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_zero_centralDeficitBinarySpecialisation,
    pderiv_one_centralDeficitBinarySpecialisation]

/-- **Exact binary Hessian transport.** -/
theorem binaryHessianDet_centralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
        (centralDeficitBinarySpecialisation (K := K) F) =
      centralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 1 *
            HC4.Polynomial.hessian F 2 2 -
          HC4.Polynomial.hessian F 1 2 *
            HC4.Polynomial.hessian F 2 1) := by
  unfold binaryDirectionalHessianDet
  simp only [← HC4.Polynomial.hessian_apply]
  rw [hessian_zero_zero_centralDeficitBinarySpecialisation,
    hessian_one_one_centralDeficitBinarySpecialisation,
    hessian_zero_one_centralDeficitBinarySpecialisation,
    hessian_one_zero_centralDeficitBinarySpecialisation]
  simp

/-- Exact image of one source monomial. -/
theorem centralDeficitBinarySpecialisation_monomial
    (e : Fin 4 →₀ ℕ) (z : K) :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.monomial e z) =
      MvPolynomial.C z *
        (MvPolynomial.X (0 : Fin 2)) ^ e 1 *
        (MvPolynomial.X (1 : Fin 2)) ^ e 2 := by
  rw [MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_four]
    simp [centralDeficitBinarySpecialisation,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    simp


/-- A monomial with zero exponents in the two deficit coordinates becomes,
after Hessian formation and binary specialisation, exactly its all-ones
exponent Hessian core embedded as constants. -/
theorem centralDeficitBinarySpecialisation_hessian_monomial_of_deficits_zero
    (e : Fin 4 →₀ ℕ) (z : K)
    (h1 : e 1 = 0) (h2 : e 2 = 0) :
    (centralDeficitBinarySpecialisation (K := K)).mapMatrix
        (HC4.Polynomial.hessian (MvPolynomial.monomial e z)) =
      (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
        (z • exponentHessianCore (K := K) e) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial,
      centralDeficitBinarySpecialisation_monomial,
      exponentHessianCore, h1, h2,
      Finsupp.single_apply, natCast_mul_pred] <;> ring

end

end HC4.Polynomial
