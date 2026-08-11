import HC4.Newton.FirstNonfacetContact
import HC4.Valuation.ParameterRamification
import HC4.Valuation.IntegralKernelBlowup
import HC4.Valuation.PointedShearContinuation
import HC4.Valuation.MovingCollisionRecentering
import Mathlib.Tactic

/-!
# Preservation of the nonlinear source-degree ceiling

`NonlinearDegreeBound` is a statement about source support only.  It is
therefore inherited by every family whose source support is contained in the
source support of the original family.  This file starts the preservation
library for the degree-adaptive restart architecture.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- On four source variables, `Finsupp.degree` is the explicit ordinary
degree used by the Newton layer. -/
theorem finsuppDegree_eq_ordinaryDegree4
    (d : Fin 4 →₀ ℕ) :
    d.degree = HC4.Polynomial.ordinaryDegree4 d := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  · intro i
    simp

/-- A nonlinear degree ceiling is inherited by source-support restriction. -/
theorem nonlinearDegreeBound_of_support_subset
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    {m : ℕ}
    {P : MvPolynomial (Fin 4) R}
    {Q : MvPolynomial (Fin 4) S}
    (hP : NonlinearDegreeBound m P)
    (hsub : Q.support ⊆ P.support) :
    NonlinearDegreeBound m Q := by
  intro d hd hnonlinear
  exact hP d (hsub hd) hnonlinear

/-- A source-ring homomorphism which sends every source monomial to a
homogeneous polynomial of the same ordinary degree preserves every nonlinear
degree ceiling.  This is the reusable assembly lemma for linear source
changes such as determinant-one shears. -/
theorem nonlinearDegreeBound_map_of_monomial_homogeneous
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) S)
    (P : MvPolynomial (Fin 4) R)
    (m : ℕ)
    (hP : NonlinearDegreeBound m P)
    (hmono :
      ∀ (n : Fin 4 →₀ ℕ) (c : R),
        (φ (MvPolynomial.monomial n c)).IsHomogeneous n.degree) :
    NonlinearDegreeBound m (φ P) := by
  classical
  intro d hd hnonlinear
  have hsum :
      φ P =
        ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
    calc
      φ P = φ (∑ n ∈ P.support,
          MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            exact congrArg φ (MvPolynomial.as_sum P)
      _ = ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            simp only [map_sum]
  have hdSum :
      d ∈ (∑ n ∈ P.support,
        φ (MvPolynomial.monomial n (MvPolynomial.coeff n P))).support := by
    rwa [← hsum]
  have hdUnion :
      d ∈ P.support.biUnion
        (fun n =>
          (φ (MvPolynomial.monomial n
            (MvPolynomial.coeff n P))).support) :=
    MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨n, hnP, hdn⟩
  have hdegree : d.degree = n.degree := by
    calc
      d.degree = Finsupp.weight (fun _ : Fin 4 => 1) d :=
        congrFun Finsupp.degree_eq_weight_one d
      _ = n.degree :=
        hmono n (MvPolynomial.coeff n P)
          (MvPolynomial.mem_support_iff.mp hdn)
  have hord :
      HC4.Polynomial.ordinaryDegree4 d =
        HC4.Polynomial.ordinaryDegree4 n := by
    rw [← finsuppDegree_eq_ordinaryDegree4,
      ← finsuppDegree_eq_ordinaryDegree4]
    exact hdegree
  rw [hord] at hnonlinear ⊢
  exact hP n hnP hnonlinear

/-- The explicit four-variable ordinary degree is the `Finsupp.sum` used by
`MvPolynomial.totalDegree`. -/
theorem finsuppSum_eq_ordinaryDegree4
    (d : Fin 4 →₀ ℕ) :
    d.sum (fun _ e => e) = HC4.Polynomial.ordinaryDegree4 d := by
  rw [Finsupp.sum_fintype]
  · simp [HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  · intro i
    simp

/-- A source substitution preserves a nonlinear degree ceiling whenever
the image of each input monomial has total degree at most the input ordinary
degree.  Unlike the homogeneous assembly lemma, this permits affine
translations and their lower-degree Taylor terms. -/
theorem nonlinearDegreeBound_map_of_monomial_totalDegree_le
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) S)
    (P : MvPolynomial (Fin 4) R)
    (m : ℕ)
    (hP : NonlinearDegreeBound m P)
    (hmono :
      ∀ (n : Fin 4 →₀ ℕ) (c : R),
        (φ (MvPolynomial.monomial n c)).totalDegree ≤
          HC4.Polynomial.ordinaryDegree4 n) :
    NonlinearDegreeBound m (φ P) := by
  classical
  intro d hd hnonlinear
  have hsum :
      φ P =
        ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
    calc
      φ P = φ (∑ n ∈ P.support,
          MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            exact congrArg φ (MvPolynomial.as_sum P)
      _ = ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            simp only [map_sum]
  have hdSum :
      d ∈ (∑ n ∈ P.support,
        φ (MvPolynomial.monomial n (MvPolynomial.coeff n P))).support := by
    rwa [← hsum]
  have hdUnion :
      d ∈ P.support.biUnion
        (fun n =>
          (φ (MvPolynomial.monomial n
            (MvPolynomial.coeff n P))).support) :=
    MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨n, hnP, hdn⟩
  have hdleTotal :
      HC4.Polynomial.ordinaryDegree4 d ≤
        (φ (MvPolynomial.monomial n
          (MvPolynomial.coeff n P))).totalDegree := by
    rw [← finsuppSum_eq_ordinaryDegree4]
    exact MvPolynomial.le_totalDegree hdn
  have hdle :
      HC4.Polynomial.ordinaryDegree4 d ≤
        HC4.Polynomial.ordinaryDegree4 n :=
    hdleTotal.trans (hmono n (MvPolynomial.coeff n P))
  exact hdle.trans (hP n hnP (hnonlinear.trans hdle))

/-- Affine substitution by source polynomials of total degree at most one
sends a monomial to total degree at most its original ordinary degree. -/
theorem totalDegree_eval₂Hom_monomial_le_ordinaryDegree4
    {S : Type*} [CommRing S]
    (g : Fin 4 → MvPolynomial (Fin 4) S)
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (n : Fin 4 →₀ ℕ)
    (c : S) :
    (MvPolynomial.eval₂Hom MvPolynomial.C g
      (MvPolynomial.monomial n c)).totalDegree ≤
      HC4.Polynomial.ordinaryDegree4 n := by
  classical
  rw [MvPolynomial.eval₂Hom_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hprod := MvPolynomial.totalDegree_finset_prod n.support
    (fun i => g i ^ n i)
  calc
    (MvPolynomial.C c).totalDegree +
        (n.prod fun i k => g i ^ k).totalDegree
        ≤ 0 + ∑ i ∈ n.support, (g i ^ n i).totalDegree := by
          apply Nat.add_le_add
          · simp
          · simpa [Finsupp.prod] using hprod
    _ ≤ ∑ i ∈ n.support, n i := by
      simp only [zero_add]
      exact Finset.sum_le_sum fun i hi =>
        (MvPolynomial.totalDegree_pow (g i) (n i)).trans
          (by simpa using Nat.mul_le_mul_left (n i) (hg i))
    _ = HC4.Polynomial.ordinaryDegree4 n := by
      rw [← finsuppSum_eq_ordinaryDegree4]
      simp [Finsupp.sum]

/-- Coefficientwise parameter ramification does not introduce a source
monomial, hence preserves every nonlinear source-degree ceiling. -/
theorem nonlinearDegreeBound_parameterRamification
    (m ramification : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m
      (parameterRamificationFamily
        (K := K) ramification P) := by
  apply nonlinearDegreeBound_of_support_subset hP
  exact MvPolynomial.support_map_subset _ _

/-- Integral kernel blow-up only divides coefficients and therefore
preserves the source-degree ceiling. -/
theorem nonlinearDegreeBound_integralKernelBlowup
    (m slope : ℕ)
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility kernel slope P) :
    NonlinearDegreeBound m
      (integralKernelBlowupFamily kernel slope P hdiv) := by
  apply nonlinearDegreeBound_of_support_subset hP
  exact support_integralKernelBlowupFamily_subset kernel slope P hdiv

/-- The integral Smith conformal reconstruction retains only source
exponents already supported by the input family. -/
theorem support_integralSmithConformalFamily_subset_degreeBound
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    (integralSmithConformalFamily theta1 theta2 P hdiv).support ⊆
      P.support := by
  classical
  intro d hd
  by_contra hnot
  have hzero :
      MvPolynomial.coeff d
          (integralSmithConformalFamily theta1 theta2 P hdiv) = 0 := by
    unfold integralSmithConformalFamily
    simp [MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hnot]
  exact (MvPolynomial.mem_support_iff.mp hd) hzero

/-- Integral Smith conformal exposure is diagonal in the source monomials
and preserves the nonlinear source-degree ceiling. -/
theorem nonlinearDegreeBound_integralSmithConformal
    (m theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P)
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    NonlinearDegreeBound m
      (integralSmithConformalFamily theta1 theta2 P hdiv) := by
  apply nonlinearDegreeBound_of_support_subset hP
  exact support_integralSmithConformalFamily_subset_degreeBound
    theta1 theta2 P hdiv

/-- An elementary determinant-one source shear preserves the nonlinear
degree ceiling because each source variable is replaced by a homogeneous
linear form. -/
theorem nonlinearDegreeBound_elementaryShear
    (m : ℕ)
    (k : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (elementaryShearHom (K := K) k c P) := by
  apply nonlinearDegreeBound_map_of_monomial_homogeneous
    (elementaryShearHom (K := K) k c) P m hP
  intro n r
  have hhom :
      (MvPolynomial.monomial n r).IsHomogeneous n.degree :=
    MvPolynomial.isHomogeneous_monomial r rfl
  exact elementaryShearHom_isHomogeneous k c
    (MvPolynomial.monomial n r) hhom

/-- Moving-section translation can create lower Taylor degrees but cannot
increase ordinary source degree, hence preserves the nonlinear ceiling. -/
theorem nonlinearDegreeBound_polynomialFamilyTranslationHom
    (m : ℕ)
    (a : Fin 4 → Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m
      (polynomialFamilyTranslationHom (K := K) a P) := by
  apply nonlinearDegreeBound_map_of_monomial_totalDegree_le
    (polynomialFamilyTranslationHom (K := K) a) P m hP
  intro n c
  apply totalDegree_eval₂Hom_monomial_le_ordinaryDegree4
  intro i
  unfold polynomialFamilyTranslationVariable
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

/-- Passing to the parameter special fibre can only remove source
monomials. -/
theorem nonlinearDegreeBound_polynomialFamilySpecialFiber
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (polynomialFamilySpecialFiber P) := by
  apply nonlinearDegreeBound_of_support_subset hP
  exact MvPolynomial.support_map_subset _ _

end

end HC4.Valuation
