import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstVariation
import HC4.Polynomial.AffineEulerTwoRootRigidity
import Mathlib.Tactic

/-!
# A19 highest-end nonzero translated two-mode profile

This is the pair-Rees companion to the locked/contact-side two-mode theorem.
The source-honest highest-end first variation gives the affine Euler equation
with adjacent roots `j,j+1`. Translating to the root of the literal highest
binomial affine form therefore confines the actual highest surviving interior
profile to precisely those two possible Euler modes. Translation is
invertible, so the translated profile remains nonzero.
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

namespace QsOtherFacetPrPairReesData

/-- **Nonzero two-mode highest-interior normal form.** Under surviving strict
interior support, the pair-Rees selected highest interior profile, translated
to the root of the literal primitive-highest affine form, is supported in the
adjacent modes `j,j+1`, with at least one of those coefficients nonzero. -/
theorem exists_firstPositiveLayer_highestTranslatedTwoMode_nonzero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D,
      let c : K :=
        MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K)
      let d : K :=
        MvPolynomial.coeff F.highest.e1 S.slice *
          ((F.highest.n - 1 : ℕ) : K)
      let alpha : K := -(c / d)
      let psi := HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
      psi.support ⊆ {A.j, A.j + 1} ∧
        (psi.coeff A.j ≠ 0 ∨ psi.coeff (A.j + 1) ≠ 0) := by
  rcases D.exists_firstPositiveLayer_highestEulerEquation_left
      F hthree houtThree hnot with
    ⟨A, _hkgt, _hklt, _hjpos, _hjlt, hode⟩
  refine ⟨A, ?_⟩
  let c : K :=
    MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K)
  let d : K :=
    MvPolynomial.coeff F.highest.e1 S.slice *
      ((F.highest.n - 1 : ℕ) : K)
  let alpha : K := -(c / d)
  let psi : Polynomial K :=
    HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have he1ne : MvPolynomial.coeff F.highest.e1 S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he1S
  have hnsub : F.highest.n - 1 ≠ 0 := by
    omega
  have hnsubK : ((F.highest.n - 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hnsub
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero he1ne hnsubK
  have hsupport : psi.support ⊆ {A.j, A.j + 1} := by
    have hs := HC4.Polynomial.translated_support_subset_of_affineTwoRoot
      c d A.j A.coefficientProfile hd (by simpa [c, d] using hode)
    simpa [psi, alpha] using hs
  have hpsi : psi ≠ 0 := by
    intro hzero
    have hback := congrArg
      (HC4.Polynomial.translatePolynomial (-alpha)) hzero
    have hinv :
        HC4.Polynomial.translatePolynomial (-alpha) psi =
          A.coefficientProfile := by
      dsimp [psi]
      simp [HC4.Polynomial.translatePolynomial, Polynomial.comp_assoc]
    rw [hinv] at hback
    simp [HC4.Polynomial.translatePolynomial] at hback
    exact A.coefficientProfile_ne_zero hback
  refine ⟨hsupport, ?_⟩
  by_cases hj : psi.coeff A.j = 0
  · by_cases hj1 : psi.coeff (A.j + 1) = 0
    · exfalso
      apply hpsi
      apply Polynomial.ext
      intro m
      simp only [Polynomial.coeff_zero]
      by_cases hmj : m = A.j
      · subst m
        exact hj
      by_cases hmj1 : m = A.j + 1
      · subst m
        exact hj1
      have hmnot : m ∉ psi.support := by
        intro hm
        have ha := hsupport hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with h | h
        · exact hmj h
        · exact hmj1 h
      by_contra hcoeff
      exact hmnot (Polynomial.mem_support_iff.mpr hcoeff)
    · exact Or.inr hj1
  · exact Or.inl hj

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
