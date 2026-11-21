import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberModes
import Mathlib.Tactic

/-!
# A19 exact common translated mode normal forms

The preceding support theorem already confines the common translated one-fibre
profile to one or two adjacent Euler modes.  This file converts those support
statements into literal polynomial equalities, retaining nonvanishing of the
active coefficient.

These equalities are representation plumbing for the remaining mixed Hessian
coefficient calculation; they add no new geometric hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

private theorem polynomial_eq_monomial_of_nonzero_support_singleton
    {p : Polynomial K} {m : ℕ}
    (hp : p ≠ 0) (hs : p.support ⊆ {m}) :
    p.coeff m ≠ 0 ∧ p = Polynomial.monomial m (p.coeff m) := by
  have hmmem : m ∈ p.support := by
    rcases Polynomial.support_nonempty.mpr hp with ⟨r, hr⟩
    have hrm := hs hr
    simp only [Finset.mem_singleton] at hrm
    simpa [hrm] using hr
  have hcoeff : p.coeff m ≠ 0 := Polynomial.mem_support_iff.mp hmmem
  refine ⟨hcoeff, ?_⟩
  apply Polynomial.ext
  intro r
  by_cases hrm : r = m
  · subst r
    simp
  · have hrnot : r ∉ p.support := by
      intro hr
      have := hs hr
      simp only [Finset.mem_singleton] at this
      exact hrm this
    have hzero : p.coeff r = 0 := Polynomial.notMem_support_iff.mp hrnot
    simp [hzero, Polynomial.coeff_monomial, hrm]

private theorem polynomial_eq_two_monomials_of_support_pair
    {p : Polynomial K} {m : ℕ}
    (hs : p.support ⊆ {m, m + 1}) :
    p = Polynomial.monomial m (p.coeff m) +
      Polynomial.monomial (m + 1) (p.coeff (m + 1)) := by
  apply Polynomial.ext
  intro r
  by_cases hrm : r = m
  · subst r
    simp
  by_cases hrm1 : r = m + 1
  · subst r
    simp [show m + 1 ≠ m by omega]
  · have hrnot : r ∉ p.support := by
      intro hr
      have h := hs hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hrm h
      · exact hrm1 h
    have hzero : p.coeff r = 0 := Polynomial.notMem_support_iff.mp hrnot
    simp [hzero, Polynomial.coeff_monomial, hrm, hrm1]

/-- Upper extreme `j=k`: the common translated source profile is literally one
nonzero monomial of degree `k`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_translatedProfile_eq_mode_k
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j = Alo.k) :
    let cLo : K :=
      MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1)
    let dLo : K :=
      MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K)
    let psi := HC4.Polynomial.translatePolynomial (-cLo / dLo)
      Alo.coefficientProfile
    psi.coeff Alo.k ≠ 0 ∧
      psi = Polynomial.monomial Alo.k (psi.coeff Alo.k) := by
  rcases F.oneFiber_mode_k_of_j_eq_k
      Alo Ahi hthree houtThree hext hdiag with ⟨hpsi, hs⟩
  exact polynomial_eq_monomial_of_nonzero_support_singleton hpsi hs

/-- Lower extreme `j+2=k`: the common translated source profile is literally
one nonzero monomial of degree `k-1`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_translatedProfile_eq_mode_k_pred
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 2 = Alo.k) :
    let cLo : K :=
      MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1)
    let dLo : K :=
      MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K)
    let psi := HC4.Polynomial.translatePolynomial (-cLo / dLo)
      Alo.coefficientProfile
    psi.coeff (Alo.k - 1) ≠ 0 ∧
      psi = Polynomial.monomial (Alo.k - 1) (psi.coeff (Alo.k - 1)) := by
  rcases F.oneFiber_mode_k_pred_of_j_add_two_eq_k
      Alo Ahi hthree houtThree hext hdiag with ⟨hpsi, hs⟩
  exact polynomial_eq_monomial_of_nonzero_support_singleton hpsi hs

/-- Middle diagonal `j+1=k`: the common translated profile is literally the
sum of its two adjacent modes.  At least one coefficient is nonzero because
the translated profile itself is nonzero. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_translatedProfile_eq_middle_twoMode
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (_hdiag : Alo.j + 1 = Alo.k) :
    let cLo : K :=
      MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1)
    let dLo : K :=
      MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K)
    let psi := HC4.Polynomial.translatePolynomial (-cLo / dLo)
      Alo.coefficientProfile
    (psi.coeff (Alo.k - 1) ≠ 0 ∨ psi.coeff Alo.k ≠ 0) ∧
      psi = Polynomial.monomial (Alo.k - 1) (psi.coeff (Alo.k - 1)) +
        Polynomial.monomial Alo.k (psi.coeff Alo.k) := by
  rcases F.oneFiber_commonTranslatedProfile_support
      Alo Ahi hthree houtThree hext with ⟨hpsi, hLo, _hHi⟩
  have hkpred : (Alo.k - 1) + 1 = Alo.k := by omega
  have heq :
      (HC4.Polynomial.translatePolynomial
        (-((MvPolynomial.coeff C.ray.facetExponent P.carrier *
              ((F.locked.ell : K) + 1)) /
            (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
              (F.locked.ell : K))))
        Alo.coefficientProfile) =
      Polynomial.monomial (Alo.k - 1)
          ((HC4.Polynomial.translatePolynomial
            (-((MvPolynomial.coeff C.ray.facetExponent P.carrier *
                  ((F.locked.ell : K) + 1)) /
                (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
                  (F.locked.ell : K))))
            Alo.coefficientProfile).coeff (Alo.k - 1)) +
        Polynomial.monomial Alo.k
          ((HC4.Polynomial.translatePolynomial
            (-((MvPolynomial.coeff C.ray.facetExponent P.carrier *
                  ((F.locked.ell : K) + 1)) /
                (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
                  (F.locked.ell : K))))
            Alo.coefficientProfile).coeff Alo.k) := by
    have := polynomial_eq_two_monomials_of_support_pair hLo
    simpa [hkpred] using this
  refine ⟨?_, heq⟩
  by_contra hboth
  push_neg at hboth
  apply hpsi
  rw [heq, hboth.1, hboth.2]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
