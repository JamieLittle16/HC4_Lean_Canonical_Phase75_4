import HC4.Polynomial.RankThreeCubicSquarefreePoleDerivativeObstruction
import Mathlib.Tactic

/-!
# No squarefree pole for an actual cubic source characteristic

This is the characteristic-zero closure of the independent
source-derived Cramer/Jacobi obstruction. The key is an elementary
multivariate differentiation lemma: an irreducible polynomial over a
characteristic-zero field cannot divide every one of its partial
derivatives. No separability or external geometric classification is
assumed.

**Compilation status:** to be confirmed by the real Lean build.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Differentiation lowers degree in the differentiated variable
whenever that variable occurs with positive degree. -/
theorem degreeOf_pderiv_lt_of_degreeOf_pos
    (p : B3 K) (i : Fin 3) (hpos : 0 < p.degreeOf i) :
    (pderiv i p).degreeOf i < p.degreeOf i := by
  classical
  have hle : (pderiv i p).degreeOf i ≤ p.degreeOf i - 1 := by
    apply degreeOf_le_iff.mpr
    intro m hm
    have hc : (pderiv i p).coeff m ≠ 0 :=
      mem_support_iff.mp hm
    have hc' : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
      rw [coeff_pderiv] at hc
      exact (mul_ne_zero_iff.mp hc).1
    have hsupp : m + Finsupp.single i 1 ∈ p.support :=
      mem_support_iff.mpr hc'
    have hbound :=
      monomial_le_degreeOf i hsupp
    have heq : (m + Finsupp.single i 1) i = m i + 1 := by
      simp
    rw [heq] at hbound
    omega
  omega

/-- If a multivariate polynomial has a genuinely occurring variable,
its partial derivative in that variable is nonzero in characteristic zero. -/
theorem pderiv_ne_zero_of_mem_vars
    (p : B3 K) (i : Fin 3) (hi : i ∈ p.vars) :
    pderiv i p ≠ 0 := by
  classical
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hm0 : m i ≠ 0 := Finsupp.mem_support_iff.mp hmi
  have hc0 : p.coeff m ≠ 0 := mem_support_iff.mp hm
  have heq : (m - Finsupp.single i 1) i + 1 = m i := by
    have hh := Finsupp.sub_add_single_one_cancel hm0
    have heval := congrArg (fun n : Fin 3 →₀ ℕ => n i) hh
    simpa using heval
  have hcoef : (pderiv i p).coeff (m - Finsupp.single i 1) ≠ 0 := by
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hm0, heq]
    exact mul_ne_zero hc0 (Nat.cast_ne_zero.mpr hm0)
  intro hz
  apply hcoef
  rw [hz]
  simp

/-- An irreducible multivariate polynomial in characteristic zero does
not divide at least one of its first partial derivatives. -/
theorem exists_pderiv_not_dvd_of_irreducible
    (p : B3 K) (hp : Irreducible p) :
    ∃ i : Fin 3, ¬ p ∣ pderiv i p := by
  classical
  have hvars : p.vars ≠ ∅ := by
    intro hzero
    have hpC : p = MvPolynomial.C (p.coeff 0) :=
      (vars_eq_empty_iff_eq_C).mp hzero
    have hc : p.coeff 0 ≠ 0 := by
      intro hc0
      apply hp.ne_zero
      simp [hpC, hc0]
    have hu : IsUnit p := by
      rw [hpC]
      exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc)
    exact hp.not_isUnit hu
  obtain ⟨i, hi⟩ : p.vars.Nonempty :=
    Finset.ne_empty_iff_nonempty.mp hvars
  have hpos : 0 < p.degreeOf i :=
    Nat.pos_of_ne_zero ((mem_vars_iff_degreeOf_ne_zero).mp hi)
  have hder0 : pderiv i p ≠ 0 :=
    pderiv_ne_zero_of_mem_vars p i hi
  refine ⟨i, ?_⟩
  intro hdvd
  obtain ⟨u, hu⟩ := hdvd
  have hu0 : u ≠ 0 := by
    intro hzero
    apply hder0
    rw [hu, hzero, mul_zero]
  have hdeg :
      (pderiv i p).degreeOf i = p.degreeOf i + u.degreeOf i := by
    rw [hu]
    exact degreeOf_mul_eq hp.ne_zero hu0
  have hlt := degreeOf_pderiv_lt_of_degreeOf_pos p i hpos
  omega

/-- A squarefree polynomial cannot have an irreducible factor dividing
every partial derivative in characteristic zero. -/
theorem squarefree_irreducible_factor_not_all_pderivs
    (D p : B3 K)
    (hsq : Squarefree D)
    (hp : Irreducible p)
    (hpD : p ∣ D) :
    ∃ i : Fin 3, ¬ p ∣ pderiv i D := by
  classical
  obtain ⟨i, hpi⟩ := exists_pderiv_not_dvd_of_irreducible p hp
  refine ⟨i, ?_⟩
  intro hd
  obtain ⟨h, hh⟩ := hpD
  have hnot : ¬ p ∣ h := by
    intro hph
    have hpp : p * p ∣ D := by
      rw [hh]
      exact mul_dvd_mul (dvd_refl p) hph
    exact hp.not_isUnit (hsq p hpp)
  have hpder : p ∣ pderiv i (p * h) := by
    simpa only [hh] using hd
  rw [pderiv_mul] at hpder
  have hpsecond : p ∣ p * pderiv i h := by
    exact ⟨pderiv i h, rfl⟩
  have hpdiff := dvd_sub hpder hpsecond
  have hprod : p ∣ (pderiv i p) * h := by
    convert hpdiff using 1 <;> ring
  exact (hp.prime.not_dvd_mul hpi hnot) hprod

/-- The *actual source cubic* cannot have both a squarefree
transverse Hessian determinant and a nonpolynomial normalized
gradient characteristic. No extra terminal hypothesis. -/
theorem sourceCubic_squarefreePole_impossible
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hsq : Squarefree
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det)
    (hnonpoly : ∃ i : Fin 3, ∀ b : B3 K,
      algebraMap (B3 K) (F3 K) b ≠ V (.inr i)) :
    False := by
  obtain ⟨p, hp, hpdet, hall⟩ :=
    exists_sourceCubic_squarefreePole_factor_dvd_allJacobiDerivatives
      F a V hV hgrad hsq hnonpoly
  obtain ⟨i, hi⟩ :=
    squarefree_irreducible_factor_not_all_pderivs
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det
      p hsq hp hpdet
  exact hi (hall i)

end
end HC4.Polynomial.RankThreeCubic
