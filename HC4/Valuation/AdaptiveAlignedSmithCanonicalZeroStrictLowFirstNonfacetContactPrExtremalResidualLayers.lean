import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalContactLayer
import Mathlib.Tactic

/-!
# A19.R18.32-R18.33: exact leading layers for the PR parameter residual

The first genuine PR coefficient calculation is the leading self pair.  Three
small finite facts are needed before expanding the exact parameter residual:

* exact parameter-layer extraction through the longitudinal Euler-Hessian
  gives the literal falling scalar `N(N-1)`;
* the retained order `qN` is the first honest-contact parameter order at
  longitudinal degree `N`; and
* no honest-contact layer has longitudinal index strictly above `N`.

The last two statements collapse the two-dimensional convolution at the
leading self pair to the unique split `(qN,N) + (qN,N)`.  These are local
consequences of the already-certified contact grading.  No Schur vanishing,
all-depth product clock, localization, or new geometric hypothesis is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- Exact parameter-layer extraction is additive over subtraction. -/
theorem familyParameterLayer_sub_exact
    (F G : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) :
    familyParameterLayer (F - G) q =
      familyParameterLayer F q - familyParameterLayer G q := by
  apply MvPolynomial.ext
  intro d
  simp [familyParameterLayer_coeff]

/-- On longitudinal coefficient `n`, the pure longitudinal Euler-Hessian
contributes exactly the falling scalar `n(n-1)` on every honest contact
parameter layer.  We calculate directly as `D₀D₀-D₀`; this avoids any
coefficient-ring coercion between the parameter polynomial and the source
Euler operators. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSourceHessianLayer_eq
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.eulerScaledHessian P.contactFamily
          (0 : Fin 4) 0) q)).coeff n =
      MvPolynomial.C ((n : K) * ((n : K) - 1)) *
        R.contactLongitudinalParameterLayer q n := by
  change
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.mvEuler (0 : Fin 4)
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) -
          HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) q)).coeff n = _
  rw [familyParameterLayer_sub_exact]
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.coeff_sub]
  rw [familyParameterLayer_coeff, familyParameterLayer_coeff,
    familyParameterLayer_coeff]
  rw [coeff_mvEuler, coeff_mvEuler]
  have h0 : (Finsupp.cons n m) (0 : Fin 4) = n := by
    simp
  rw [h0]
  simp
  ring

/-- The leading exposed source slice therefore sees the exact longitudinal
Hessian scalar `N(N-1)`. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingSourceHessianLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.eulerScaledHessian P.contactFamily
          (0 : Fin 4) 0) E.qN)).coeff E.next.N =
      MvPolynomial.C
          ((E.next.N : K) * ((E.next.N : K) - 1)) *
        E.leading.slice := by
  calc
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.eulerScaledHessian P.contactFamily
          (0 : Fin 4) 0) E.qN)).coeff E.next.N =
        MvPolynomial.C
            ((E.next.N : K) * ((E.next.N : K) - 1)) *
          R.contactLongitudinalParameterLayer E.qN E.next.N :=
      R.contactLongitudinalSourceHessianLayer_eq E.qN E.next.N
    _ = MvPolynomial.C
          ((E.next.N : K) * ((E.next.N : K) - 1)) *
        E.leading.slice := by
      rw [E.contactLeadingParameterLayer_eq]

/-- **R18.32 leading-order minimality.**  At the highest longitudinal profile
index, every honest-contact parameter layer strictly below `qN` vanishes.
Indeed such an order would require transverse degree strictly larger than the
maximal degree defining the retained leading slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterLayer_eq_zero_of_lt
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (q : ℕ)
    (hq : q < E.qN) :
    R.contactLongitudinalParameterLayer q E.next.N = 0 := by
  let t : ℕ :=
    T.topFace.degree - (q + P.profileWeight * E.next.N)
  have hbound :
      q + P.profileWeight * E.next.N ≤ T.topFace.degree := by
    have hgrade := E.leading_grade
    omega
  have hgrade :
      q + P.profileWeight * E.next.N + t = T.topFace.degree := by
    dsimp [t]
    omega
  have ht : E.leading.transverseDegree < t := by
    have hlead := E.leading_grade
    dsimp [t]
    omega
  rw [R.contactLongitudinalParameterLayer_eq_initialForm
    q E.next.N t hgrade]
  apply MvPolynomial.ext
  intro m
  rw [HC4.Polynomial.coeff_initialForm]
  by_cases hw :
      Finsupp.weight qsContactTransverseIntegerWeight m = (t : ℤ)
  · rw [if_pos hw]
    by_contra hm
    have hmTop :
        MvPolynomial.coeff m
          (R.profile.coeff R.profile.natDegree) ≠ 0 := by
      rw [← E.next.N_eq]
      exact hm
    have hmax := E.leading.transverseDegree_max m hmTop
    have hdegreeZ := hw
    rw [weight_qsContactTransverseIntegerWeight] at hdegreeZ
    have hdegree : qsContactTransverseDegree m = t := by
      exact_mod_cast hdegreeZ
    rw [hdegree] at hmax
    omega
  · rw [if_neg hw]
    simp

/-- **R18.33 top-longitudinal support ceiling.**  The honest contact Rees does
not create new source exponents.  Since `N` is the raw profile's natural
degree, every exact parameter layer has zero longitudinal coefficient above
`N`.  This is the source-direction half of the extremal self-pair
convolution collapse. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactParameterLayer_longitudinal_eq_zero_of_N_lt
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (q n : ℕ)
    (hn : E.next.N < n) :
    R.contactLongitudinalParameterLayer q n = 0 := by
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [P.contactFamily_longitudinal_transverse_coeff]
  rw [← R.profile_eq]
  have hdeg : R.profile.natDegree < n := by
    rw [← E.next.N_eq]
    exact hn
  have hzero : R.profile.coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact hdeg
  by_cases hcond :
      m.cons n ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support ∧
        T.topFace.degree -
            (qsContactTransverseDegree m + P.profileWeight * n) = q
  · rw [if_pos hcond, hzero]
    simp
  · rw [if_neg hcond]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
