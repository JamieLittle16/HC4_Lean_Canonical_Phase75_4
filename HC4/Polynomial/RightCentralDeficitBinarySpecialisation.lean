import HC4.Polynomial.CentralDeficitBinarySpecialisation
import Mathlib.Tactic

/-!
# Binary specialisation for the mirrored central deficit pair

The right `(V,1)` central staircase uses source deficit coordinates `1,3`.
This file is the state-free mirror of `CentralDeficitBinarySpecialisation`:

    (x0,x1,x2,x3) |-> (1,U,1,V).

It records exact derivative/Hessian transport, the literal exponent projection
`(e₁,e₃)`, coefficient preservation under deficit-injective support, and the
homogeneous/monomial facts needed by the source-honest first-layer argument.
-/

namespace HC4.Polynomial

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- Source-to-binary specialisation `x0=x2=1, x1=U, x3=V`. -/
noncomputable def rightCentralDeficitBinarySpecialisation :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![(1 : MvPolynomial (Fin 2) K),
      MvPolynomial.X (0 : Fin 2),
      1,
      MvPolynomial.X (1 : Fin 2)]

@[simp] theorem rightCentralDeficitBinarySpecialisation_C
    (z : K) :
    rightCentralDeficitBinarySpecialisation (K := K) (MvPolynomial.C z) =
      MvPolynomial.C z := by
  simp [rightCentralDeficitBinarySpecialisation]

@[simp] theorem rightCentralDeficitBinarySpecialisation_X_zero :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (0 : Fin 4)) = 1 := by
  simp [rightCentralDeficitBinarySpecialisation]

@[simp] theorem rightCentralDeficitBinarySpecialisation_X_one :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (1 : Fin 4)) =
      MvPolynomial.X (0 : Fin 2) := by
  simp [rightCentralDeficitBinarySpecialisation]

@[simp] theorem rightCentralDeficitBinarySpecialisation_X_two :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (2 : Fin 4)) = 1 := by
  simp [rightCentralDeficitBinarySpecialisation]

@[simp] theorem rightCentralDeficitBinarySpecialisation_X_three :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.X (3 : Fin 4)) =
      MvPolynomial.X (1 : Fin 2) := by
  simp [rightCentralDeficitBinarySpecialisation]

/-- First binary partial is source partial in coordinate `1`. -/
theorem pderiv_zero_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv (0 : Fin 2)
        (rightCentralDeficitBinarySpecialisation (K := K) F) =
      rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.pderiv (1 : Fin 4) F) := by
  apply MvPolynomial.induction_on F
  · intro z
    simp [rightCentralDeficitBinarySpecialisation]
  · intro P Q hP hQ
    simpa only [map_add, hP, hQ]
  · intro P i hP
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    fin_cases i <;>
      simp [rightCentralDeficitBinarySpecialisation,
        MvPolynomial.pderiv_mul] <;> ring

/-- Second binary partial is source partial in coordinate `3`. -/
theorem pderiv_one_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv (1 : Fin 2)
        (rightCentralDeficitBinarySpecialisation (K := K) F) =
      rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.pderiv (3 : Fin 4) F) := by
  apply MvPolynomial.induction_on F
  · intro z
    simp [rightCentralDeficitBinarySpecialisation]
  · intro P Q hP hQ
    simpa only [map_add, hP, hQ]
  · intro P i hP
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    fin_cases i <;>
      simp [rightCentralDeficitBinarySpecialisation,
        MvPolynomial.pderiv_mul] <;> ring

theorem hessian_zero_zero_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (rightCentralDeficitBinarySpecialisation (K := K) F) 0 0 =
      rightCentralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 1) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_zero_rightCentralDeficitBinarySpecialisation,
    pderiv_zero_rightCentralDeficitBinarySpecialisation]

theorem hessian_one_one_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (rightCentralDeficitBinarySpecialisation (K := K) F) 1 1 =
      rightCentralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 3 3) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_one_rightCentralDeficitBinarySpecialisation,
    pderiv_one_rightCentralDeficitBinarySpecialisation]

theorem hessian_zero_one_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (rightCentralDeficitBinarySpecialisation (K := K) F) 0 1 =
      rightCentralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 3) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_zero_rightCentralDeficitBinarySpecialisation,
    pderiv_one_rightCentralDeficitBinarySpecialisation]

theorem hessian_one_zero_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (rightCentralDeficitBinarySpecialisation (K := K) F) 1 0 =
      rightCentralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 3 1) := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_one_rightCentralDeficitBinarySpecialisation,
    pderiv_zero_rightCentralDeficitBinarySpecialisation]

/-- Exact binary Hessian transport for the right deficit pair. -/
theorem binaryHessianDet_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K) :
    binaryDirectionalHessianDet (0 : Fin 2) 1
        (rightCentralDeficitBinarySpecialisation (K := K) F) =
      rightCentralDeficitBinarySpecialisation (K := K)
        (HC4.Polynomial.hessian F 1 1 *
            HC4.Polynomial.hessian F 3 3 -
          HC4.Polynomial.hessian F 1 3 *
            HC4.Polynomial.hessian F 3 1) := by
  have hsym :
      HC4.Polynomial.hessian F 1 3 =
        HC4.Polynomial.hessian F 3 1 := by
    simp only [HC4.Polynomial.hessian_apply]
    exact pderiv_comm_backport (3 : Fin 4) (1 : Fin 4) F
  unfold binaryDirectionalHessianDet directionalSecondDerivative
    directionalMixedDerivative
  simp only [← HC4.Polynomial.hessian_apply]
  rw [hessian_zero_zero_rightCentralDeficitBinarySpecialisation,
    hessian_one_one_rightCentralDeficitBinarySpecialisation,
    hessian_one_zero_rightCentralDeficitBinarySpecialisation]
  simp only [map_sub, map_mul, hsym, pow_two]

/-- Exact image of one source monomial. -/
theorem rightCentralDeficitBinarySpecialisation_monomial
    (e : Fin 4 →₀ ℕ) (z : K) :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.monomial e z) =
      MvPolynomial.C z *
        (MvPolynomial.X (0 : Fin 2)) ^ e 1 *
        (MvPolynomial.X (1 : Fin 2)) ^ e 3 := by
  unfold rightCentralDeficitBinarySpecialisation
  rw [MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_four]
    simp [rightCentralDeficitBinarySpecialisation,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    simp

/-- Binary exponent retaining exactly source coordinates `1,3`. -/
def rightBinaryDeficitExponent (e : Fin 4 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (e 1) +
    Finsupp.single (1 : Fin 2) (e 3)

@[simp] theorem rightBinaryDeficitExponent_zero
    (e : Fin 4 →₀ ℕ) :
    rightBinaryDeficitExponent e (0 : Fin 2) = e 1 := by
  simp [rightBinaryDeficitExponent, Finsupp.single_apply]

@[simp] theorem rightBinaryDeficitExponent_one
    (e : Fin 4 →₀ ℕ) :
    rightBinaryDeficitExponent e (1 : Fin 2) = e 3 := by
  simp [rightBinaryDeficitExponent, Finsupp.single_apply]

theorem rightBinaryDeficitExponent_degree
    (e : Fin 4 →₀ ℕ) :
    (rightBinaryDeficitExponent e).degree = e 1 + e 3 := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [rightBinaryDeficitExponent, Finsupp.single_apply, Fin.sum_univ_two]
  · intro i
    simp

theorem rightCentralDeficitBinarySpecialisation_monomial_eq
    (e : Fin 4 →₀ ℕ) (z : K) :
    rightCentralDeficitBinarySpecialisation (K := K)
        (MvPolynomial.monomial e z) =
      MvPolynomial.monomial (rightBinaryDeficitExponent e) z := by
  rw [rightCentralDeficitBinarySpecialisation_monomial]
  rw [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_two]
    simp [rightBinaryDeficitExponent, Finsupp.single_apply,
      mul_assoc, mul_left_comm, mul_comm]
  · intro i
    simp

theorem coeff_rightCentralDeficitBinarySpecialisation_of_mem
    (F : MvPolynomial (Fin 4) K)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ F.support)
    (hinj :
      ∀ f ∈ F.support,
        rightBinaryDeficitExponent f = rightBinaryDeficitExponent e → f = e) :
    MvPolynomial.coeff (rightBinaryDeficitExponent e)
        (rightCentralDeficitBinarySpecialisation (K := K) F) =
      MvPolynomial.coeff e F := by
  classical
  have hsum :
      rightCentralDeficitBinarySpecialisation (K := K) F =
        ∑ f ∈ F.support,
          MvPolynomial.monomial (rightBinaryDeficitExponent f)
            (MvPolynomial.coeff f F) := by
    have has := MvPolynomial.as_sum F
    calc
      rightCentralDeficitBinarySpecialisation (K := K) F =
          rightCentralDeficitBinarySpecialisation (K := K)
            (∑ f ∈ F.support,
              MvPolynomial.monomial f (MvPolynomial.coeff f F)) := by
            exact congrArg
              (rightCentralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum,
          rightCentralDeficitBinarySpecialisation_monomial_eq]
  rw [hsum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    rw [MvPolynomial.coeff_monomial]
    have hproj :
        rightBinaryDeficitExponent f ≠ rightBinaryDeficitExponent e := by
      intro h
      exact hfe (hinj f hf h)
    simp [hproj]
  · intro hnot
    exact (hnot he).elim

theorem rightCentralDeficitBinarySpecialisation_ne_zero_of_injective
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hinj :
      ∀ e ∈ F.support, ∀ f ∈ F.support,
        rightBinaryDeficitExponent f = rightBinaryDeficitExponent e → f = e) :
    rightCentralDeficitBinarySpecialisation (K := K) F ≠ 0 := by
  rcases MvPolynomial.support_nonempty.mpr hF with ⟨e, he⟩
  have hc := MvPolynomial.mem_support_iff.mp he
  intro hz
  have hcoeff :=
    coeff_rightCentralDeficitBinarySpecialisation_of_mem
      F he (fun f hf h => hinj e he f hf h)
  rw [hz] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact hc hcoeff.symm

theorem exists_source_support_of_mem_rightCentralDeficitBinarySpecialisation
    (F : MvPolynomial (Fin 4) K)
    {d : Fin 2 →₀ ℕ}
    (hd :
      d ∈ (rightCentralDeficitBinarySpecialisation (K := K) F).support) :
    ∃ e ∈ F.support, rightBinaryDeficitExponent e = d := by
  classical
  have hsum :
      rightCentralDeficitBinarySpecialisation (K := K) F =
        ∑ e ∈ F.support,
          MvPolynomial.monomial (rightBinaryDeficitExponent e)
            (MvPolynomial.coeff e F) := by
    have has := MvPolynomial.as_sum F
    calc
      rightCentralDeficitBinarySpecialisation (K := K) F =
          rightCentralDeficitBinarySpecialisation (K := K)
            (∑ e ∈ F.support,
              MvPolynomial.monomial e (MvPolynomial.coeff e F)) := by
            exact congrArg
              (rightCentralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum,
          rightCentralDeficitBinarySpecialisation_monomial_eq]
  have hdSum :
      d ∈
        (∑ e ∈ F.support,
          MvPolynomial.monomial (rightBinaryDeficitExponent e)
            (MvPolynomial.coeff e F)).support := by
    rw [← hsum]
    exact hd
  have hdUnion := MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨e, he, hde⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hde
  rw [MvPolynomial.coeff_monomial] at hcoeff
  split at hcoeff
  · next hEq =>
      exact ⟨e, he, hEq⟩
  · exact (hcoeff rfl).elim

theorem rightCentralDeficitBinarySpecialisation_isHomogeneous
    (F : MvPolynomial (Fin 4) K)
    (q : ℕ)
    (hdeg : ∀ e ∈ F.support, e 1 + e 3 = q) :
    (rightCentralDeficitBinarySpecialisation (K := K) F).IsHomogeneous q := by
  classical
  intro d hd
  have hsum :
      rightCentralDeficitBinarySpecialisation (K := K) F =
        ∑ e ∈ F.support,
          MvPolynomial.monomial (rightBinaryDeficitExponent e)
            (MvPolynomial.coeff e F) := by
    have has := MvPolynomial.as_sum F
    calc
      rightCentralDeficitBinarySpecialisation (K := K) F =
          rightCentralDeficitBinarySpecialisation (K := K)
            (∑ e ∈ F.support,
              MvPolynomial.monomial e (MvPolynomial.coeff e F)) := by
            exact congrArg
              (rightCentralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum,
          rightCentralDeficitBinarySpecialisation_monomial_eq]
  have hdSum : d ∈
      (∑ e ∈ F.support,
        MvPolynomial.monomial (rightBinaryDeficitExponent e)
          (MvPolynomial.coeff e F)).support := by
    rw [← hsum]
    exact MvPolynomial.mem_support_iff.mpr hd
  have hdUnion := MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨e, he, hde⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hde
  rw [MvPolynomial.coeff_monomial] at hcoeff
  split at hcoeff
  · next hEq =>
      have hdEq : d = rightBinaryDeficitExponent e := hEq.symm
      subst d
      have hdegree := rightBinaryDeficitExponent_degree e
      rw [Finsupp.degree_eq_weight_one] at hdegree
      exact hdegree.trans (hdeg e he)
  · exact (hcoeff rfl).elim

/-- A monomial with zero exponents in right deficit coordinates `1,3`
specialises after Hessian formation to its all-ones exponent Hessian core. -/
theorem rightCentralDeficitBinarySpecialisation_hessian_monomial_of_deficits_zero
    (e : Fin 4 →₀ ℕ) (z : K)
    (h1 : e 1 = 0) (h3 : e 3 = 0) :
    (rightCentralDeficitBinarySpecialisation (K := K)).mapMatrix
        (HC4.Polynomial.hessian (MvPolynomial.monomial e z)) =
      (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
        (z • exponentHessianCore (K := K) e) := by
  have heval :=
    HC4.Polynomial.eval_one_hessian_monomial (K := K) e z
  calc
    (rightCentralDeficitBinarySpecialisation (K := K)).mapMatrix
        (HC4.Polynomial.hessian (MvPolynomial.monomial e z)) =
      (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
        ((MvPolynomial.eval fun _ : Fin 4 => (1 : K)).mapMatrix
          (HC4.Polynomial.hessian (MvPolynomial.monomial e z))) := by
            apply Matrix.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [HC4.Polynomial.hessian_apply,
                MvPolynomial.pderiv_monomial,
                rightCentralDeficitBinarySpecialisation_monomial,
                MvPolynomial.eval_monomial, Finsupp.prod, h1, h3]
    _ = (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K).mapMatrix
        (z • exponentHessianCore (K := K) e) := by
          rw [heval]

end

end HC4.Polynomial
