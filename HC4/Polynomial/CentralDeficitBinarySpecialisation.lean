import HC4.Newton.PreterminalFirstDeparture
import HC4.Polynomial.MonomialHessian
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
    simpa only [map_add, hP, hQ]
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
    simpa only [map_add, hP, hQ]
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
  rfl

/-- Exact image of one source monomial. -/
theorem centralDeficitBinarySpecialisation_monomial
    (e : Fin 4 →₀ ℕ) (z : K) :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.monomial e z) =
      MvPolynomial.C z *
        (MvPolynomial.X (0 : Fin 2)) ^ e 1 *
        (MvPolynomial.X (1 : Fin 2)) ^ e 2 := by
  unfold centralDeficitBinarySpecialisation
  rw [MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_four]
    simp [centralDeficitBinarySpecialisation,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    simp



/-- Binary exponent retaining exactly source coordinates `1,2`. -/
def binaryDeficitExponent (e : Fin 4 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (e 1) +
    Finsupp.single (1 : Fin 2) (e 2)

@[simp] theorem binaryDeficitExponent_zero
    (e : Fin 4 →₀ ℕ) :
    binaryDeficitExponent e (0 : Fin 2) = e 1 := by
  simp [binaryDeficitExponent, Finsupp.single_apply]

@[simp] theorem binaryDeficitExponent_one
    (e : Fin 4 →₀ ℕ) :
    binaryDeficitExponent e (1 : Fin 2) = e 2 := by
  simp [binaryDeficitExponent, Finsupp.single_apply]

theorem binaryDeficitExponent_degree
    (e : Fin 4 →₀ ℕ) :
    (binaryDeficitExponent e).degree = e 1 + e 2 := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [binaryDeficitExponent, Finsupp.single_apply, Fin.sum_univ_two]
  · intro i
    simp

/-- Monomial form of the binary specialisation. -/
theorem centralDeficitBinarySpecialisation_monomial_eq
    (e : Fin 4 →₀ ℕ) (z : K) :
    centralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.monomial e z) =
      MvPolynomial.monomial (binaryDeficitExponent e) z := by
  rw [centralDeficitBinarySpecialisation_monomial]
  rw [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_two]
    simp [binaryDeficitExponent, Finsupp.single_apply,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    simp

/-- Coefficient preservation under an injective deficit projection. -/
theorem coeff_centralDeficitBinarySpecialisation_of_mem
    (F : MvPolynomial (Fin 4) K)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ F.support)
    (hinj :
      ∀ f ∈ F.support,
        binaryDeficitExponent f = binaryDeficitExponent e → f = e) :
    MvPolynomial.coeff (binaryDeficitExponent e)
        (centralDeficitBinarySpecialisation (K := K) F) =
      MvPolynomial.coeff e F := by
  classical
  have hsum :
      centralDeficitBinarySpecialisation (K := K) F =
        ∑ f ∈ F.support,
          MvPolynomial.monomial (binaryDeficitExponent f)
            (MvPolynomial.coeff f F) := by
    have has := MvPolynomial.as_sum F
    calc
      centralDeficitBinarySpecialisation (K := K) F =
          centralDeficitBinarySpecialisation (K := K)
            (∑ f ∈ F.support,
              MvPolynomial.monomial f (MvPolynomial.coeff f F)) := by
            exact congrArg
              (centralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum, centralDeficitBinarySpecialisation_monomial_eq]
  rw [hsum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    rw [MvPolynomial.coeff_monomial]
    have hproj : binaryDeficitExponent f ≠ binaryDeficitExponent e := by
      intro h
      exact hfe (hinj f hf h)
    simp [hproj]
  · intro hnot
    exact (hnot he).elim

/-- Deficit-injective support prevents cancellation under binary
specialisation. -/
theorem centralDeficitBinarySpecialisation_ne_zero_of_injective
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hinj :
      ∀ e ∈ F.support, ∀ f ∈ F.support,
        binaryDeficitExponent f = binaryDeficitExponent e → f = e) :
    centralDeficitBinarySpecialisation (K := K) F ≠ 0 := by
  rcases MvPolynomial.support_nonempty.mpr hF with ⟨e, he⟩
  have hc := MvPolynomial.mem_support_iff.mp he
  intro hz
  have hcoeff :=
    coeff_centralDeficitBinarySpecialisation_of_mem
      F he (fun f hf h => hinj e he f hf h)
  rw [hz] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact hc hcoeff.symm

/-- A source layer of constant total deficit becomes a homogeneous binary
polynomial of exactly that degree. -/
theorem centralDeficitBinarySpecialisation_isHomogeneous
    (F : MvPolynomial (Fin 4) K)
    (q : ℕ)
    (hdeg : ∀ e ∈ F.support, e 1 + e 2 = q) :
    (centralDeficitBinarySpecialisation (K := K) F).IsHomogeneous q := by
  classical
  intro d hd
  have hsum :
      centralDeficitBinarySpecialisation (K := K) F =
        ∑ e ∈ F.support,
          MvPolynomial.monomial (binaryDeficitExponent e)
            (MvPolynomial.coeff e F) := by
    have has := MvPolynomial.as_sum F
    calc
      centralDeficitBinarySpecialisation (K := K) F =
          centralDeficitBinarySpecialisation (K := K)
            (∑ e ∈ F.support,
              MvPolynomial.monomial e (MvPolynomial.coeff e F)) := by
            exact congrArg
              (centralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum, centralDeficitBinarySpecialisation_monomial_eq]
  have hdSum : d ∈
      (∑ e ∈ F.support,
        MvPolynomial.monomial (binaryDeficitExponent e)
          (MvPolynomial.coeff e F)).support := by
    rw [← hsum]
    exact MvPolynomial.mem_support_iff.mpr hd
  have hdUnion := MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨e, he, hde⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hde
  rw [MvPolynomial.coeff_monomial] at hcoeff
  split at hcoeff
  · next hEq =>
      have hdEq : d = binaryDeficitExponent e := hEq.symm
      subst d
      have hdegree := binaryDeficitExponent_degree e
      rw [Finsupp.degree_eq_weight_one] at hdegree
      exact hdegree.trans (hdeg e he)
  · exact (hcoeff rfl).elim

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
  have hpred (n : ℕ) :
      (n : MvPolynomial (Fin 2) K) *
          ((n - 1 : ℕ) : MvPolynomial (Fin 2) K) =
        (n : MvPolynomial (Fin 2) K) ^ 2 -
          (n : MvPolynomial (Fin 2) K) :=
    HC4.Polynomial.natCast_mul_pred
      (K := MvPolynomial (Fin 2) K) n
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_monomial,
      centralDeficitBinarySpecialisation_monomial,
      HC4.Polynomial.exponentHessianCore, h1, h2,
      Finsupp.single_apply, mul_assoc, hpred] <;> ring

end

end HC4.Polynomial
