import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberRoot
import HC4.Polynomial.AffineEulerTwoRootRigidity
import Mathlib.Tactic

/-!
# A19 one-fibre common translated modes

Once the one-fibre endpoint roots have been proved equal, both endpoint Euler
laws act on the *same translated source profile*.  Therefore its support lies
simultaneously in

    {k-1,k}  and  {j,j+1}.

This is stronger than the earlier degree-only three-diagonal statement.  On
the two extreme diagonals the common translated profile is forced to a single
Euler mode:

* `j = k`      -> support only at `k`;
* `j + 2 = k`  -> support only at `k-1`.

Only the middle diagonal `j+1=k` can retain both adjacent modes.  These are the
three exact normal forms needed by the remaining determinant-variation step.
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

/-- In the one-fibre case, translating the common nonzero profile to the
locked/highest common affine root puts its support in both adjacent indicial
pairs simultaneously. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_commonTranslatedProfile_support
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
    (hext : Alo.k = Ahi.k) :
    let cLo : K :=
      MvPolynomial.coeff C.ray.facetExponent P.carrier *
        ((F.locked.ell : K) + 1)
    let dLo : K :=
      MvPolynomial.coeff C.ray.outsideExponent P.carrier *
        (F.locked.ell : K)
    let alpha : K := -cLo / dLo
    let psi := HC4.Polynomial.translatePolynomial alpha Alo.coefficientProfile
    psi ≠ 0 ∧
      psi.support ⊆ {Alo.k - 1, Alo.k} ∧
      psi.support ⊆ {Alo.j, Alo.j + 1} := by
  let cLo : K :=
    MvPolynomial.coeff C.ray.facetExponent P.carrier *
      ((F.locked.ell : K) + 1)
  let dLo : K :=
    MvPolynomial.coeff C.ray.outsideExponent P.carrier *
      (F.locked.ell : K)
  let cHi : K :=
    MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K)
  let dHi : K :=
    MvPolynomial.coeff F.highest.e1 S.slice *
      ((F.highest.n - 1 : ℕ) : K)
  let alpha : K := -cLo / dLo
  let psi : Polynomial K :=
    HC4.Polynomial.translatePolynomial alpha Alo.coefficientProfile

  have hb : MvPolynomial.coeff C.ray.outsideExponent P.carrier ≠ 0 :=
    F.locked.outside_provenance.carrier_coeff_ne
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hdLo : dLo ≠ 0 := by
    dsimp [dLo]
    exact mul_ne_zero hb hellK

  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have he1ne : MvPolynomial.coeff F.highest.e1 S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he1S
  have hnsub : F.highest.n - 1 ≠ 0 := by omega
  have hnsubK : ((F.highest.n - 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hnsub
  have hdHi : dHi ≠ 0 := by
    dsimp [dHi]
    exact mul_ne_zero he1ne hnsubK

  rcases F.oneFiber_commonProfile_dualEuler
      Alo Ahi hthree houtThree hext with ⟨hphi, hLoEuler, hHiEuler⟩

  have hroot : -cLo / dLo = -cHi / dHi := by
    simpa [cLo, dLo, cHi, dHi] using
      F.oneFiber_endpointRoots_eq Alo Ahi hthree houtThree hext

  have hLoSupport : psi.support ⊆ {Alo.k - 1, Alo.k} := by
    have h := HC4.Polynomial.translated_support_subset_of_affineTwoRoot
      cLo dLo (Alo.k - 1) Alo.coefficientProfile hdLo
      (by simpa [cLo, dLo] using hLoEuler)
    simpa [psi, alpha] using h

  have hHiSupport : psi.support ⊆ {Alo.j, Alo.j + 1} := by
    have h := HC4.Polynomial.translated_support_subset_of_affineTwoRoot
      cHi dHi Alo.j Alo.coefficientProfile hdHi
      (by simpa [cHi, dHi] using hHiEuler)
    rw [← hroot] at h
    simpa [psi, alpha] using h

  have hpsi : psi ≠ 0 := by
    intro hzero
    have hback := congrArg
      (HC4.Polynomial.translatePolynomial (-alpha)) hzero
    have hinv :
        HC4.Polynomial.translatePolynomial (-alpha) psi =
          Alo.coefficientProfile := by
      dsimp [psi]
      simp [HC4.Polynomial.translatePolynomial, Polynomial.comp_assoc]
    rw [hinv] at hback
    simp [HC4.Polynomial.translatePolynomial] at hback
    exact hphi hback

  exact ⟨hpsi, hLoSupport, hHiSupport⟩

/-- On the upper extreme diagonal `j=k`, the common translated profile is a
single pure mode of degree `k`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_mode_k_of_j_eq_k
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
    psi ≠ 0 ∧ psi.support ⊆ {Alo.k} := by
  rcases F.oneFiber_commonTranslatedProfile_support
      Alo Ahi hthree houtThree hext with ⟨hpsi, hLo, hHi⟩
  refine ⟨hpsi, ?_⟩
  intro m hm
  have hlo := hLo hm
  have hhi := hHi hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlo hhi ⊢
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

/-- On the lower extreme diagonal `j+2=k`, the common translated profile is a
single pure mode of degree `k-1`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_mode_k_pred_of_j_add_two_eq_k
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
    psi ≠ 0 ∧ psi.support ⊆ {Alo.k - 1} := by
  rcases F.oneFiber_commonTranslatedProfile_support
      Alo Ahi hthree houtThree hext with ⟨hpsi, hLo, hHi⟩
  refine ⟨hpsi, ?_⟩
  intro m hm
  have hlo := hLo hm
  have hhi := hHi hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlo hhi ⊢
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
