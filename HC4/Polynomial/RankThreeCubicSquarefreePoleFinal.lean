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

/-- Coefficient formula for multivariate partial differentiation,
backported explicitly for the repository's Mathlib v4.24.0 pin. -/
private theorem coeff_pderiv_at
    (i : Fin 3) (p : B3 K) (m : Fin 3 →₀ ℕ) :
    (pderiv i p).coeff m =
      p.coeff (m + Finsupp.single i 1) * (m i + 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, add_mul]
  | monomial n a =>
      rw [pderiv_monomial, coeff_monomial, coeff_monomial]
      by_cases h : n = m + Finsupp.single i 1
      · subst n
        simp
      · simp only [h, ↓reduceIte, zero_mul]
        by_cases hn : n i = 0
        · simp [hn]
        · have hne : n - Finsupp.single i 1 ≠ m := by
            intro hh
            apply h
            calc
              n = n - Finsupp.single i 1 + Finsupp.single i 1 :=
                (Finsupp.sub_add_single_one_cancel hn).symm
              _ = m + Finsupp.single i 1 := by rw [hh]
          simp [hne]

/-- Every first partial has strictly smaller total degree than a
nonconstant polynomial in characteristic zero (including a zero partial). -/
theorem totalDegree_pderiv_lt_of_totalDegree_pos
    (p : B3 K) (i : Fin 3) (hpos : 0 < p.totalDegree) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hle : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    change (pderiv i p).support.sup (fun m => m.sum (fun _ e => e)) ≤ _
    apply Finset.sup_le
    intro m hm
    have hc : (pderiv i p).coeff m ≠ 0 :=
      mem_support_iff.mp hm
    have hc' : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
      rw [coeff_pderiv_at] at hc
      exact (mul_ne_zero_iff.mp hc).1
    have hsupp : m + Finsupp.single i 1 ∈ p.support :=
      mem_support_iff.mpr hc'
    let d : Fin 3 →₀ ℕ := m + Finsupp.single i 1
    have hdi : d i ≠ 0 := by simp [d]
    have hsub : d - Finsupp.single i 1 = m := by simp [d]
    have hweight :
        m.sum (fun _ e => e) + 1 = d.sum (fun _ e => e) := by
      have hw := Finsupp.weight_sub_single_add
        (w := fun _ : Fin 3 => (1 : ℕ)) hdi
      simpa [Finsupp.weight_apply, hsub, smul_eq_mul] using hw
    have hbound : d.sum (fun _ e => e) ≤ p.totalDegree :=
      le_totalDegree hsupp
    omega
  omega

/-- A genuinely occurring variable has nonzero partial derivative in
characteristic zero. Uses the actual coefficient, not an assumed gradient. -/
theorem pderiv_ne_zero_of_mem_vars
    (p : B3 K) (i : Fin 3) (hi : i ∈ p.vars) :
    pderiv i p ≠ 0 := by
  classical
  obtain ⟨m, hm, hmi⟩ := (mem_vars i).mp hi
  have hm0 : m i ≠ 0 := Finsupp.mem_support_iff.mp hmi
  have hc0 : p.coeff m ≠ 0 := mem_support_iff.mp hm
  have hcoef : (pderiv i p).coeff (m - Finsupp.single i 1) ≠ 0 := by
    rw [coeff_pderiv_at, Finsupp.sub_add_single_one_cancel hm0]
    have hn : ((m - Finsupp.single i 1) i + 1 : ℕ) ≠ 0 :=
      Nat.succ_ne_zero _
    have hk : (((m - Finsupp.single i 1) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr hn
    exact mul_ne_zero hc0 (by
      simpa only [Nat.cast_add, Nat.cast_one] using hk)
  intro hz
  apply hcoef
  rw [hz]
  simp

/-- An irreducible multivariate polynomial in characteristic zero
cannot divide all of its first partial derivatives. -/
theorem exists_pderiv_not_dvd_of_irreducible
    (p : B3 K) (hp : Irreducible p) :
    ∃ i : Fin 3, ¬ p ∣ pderiv i p := by
  classical
  have hpos : 0 < p.totalDegree := by
    by_contra hn
    have hz : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hn
    have hconst : p = C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
    have hc0 : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp.ne_zero
      rw [hconst, hc, map_zero]
    have hu : IsUnit p :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
        ⟨isUnit_iff_ne_zero.mpr hc0, hz⟩
    exact hp.not_isUnit hu
  have hvars : p.vars ≠ ∅ := by
    intro hz
    have hdegrees : p.degrees = 0 := by
      have hd : p.degrees.toFinset = ∅ := by
        simpa only [vars_def] using hz
      simpa only [Multiset.toFinset_eq_empty] using hd
    have hdeg : p.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hdegrees] using p.totalDegree_le_degrees_card
    omega
  obtain ⟨i, hi⟩ : p.vars.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hvars
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
      (pderiv i p).totalDegree = p.totalDegree + u.totalDegree := by
    rw [hu]
    exact MvPolynomial.totalDegree_mul_of_isDomain hp.ne_zero hu0
  have hlt := totalDegree_pderiv_lt_of_totalDegree_pos p i hpos
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
