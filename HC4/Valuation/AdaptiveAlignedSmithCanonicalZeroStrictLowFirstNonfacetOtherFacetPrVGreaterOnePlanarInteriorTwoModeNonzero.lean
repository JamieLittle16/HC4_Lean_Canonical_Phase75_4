import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorTwoMode
import Mathlib.Tactic

/-!
# A19 nonzero translated mode of the first strict-interior profile

The first-variation equation only says that, after translation to the root of
the locked affine form, the first strict-interior profile is supported in the
two adjacent Euler modes `k-1,k`.  For the next Hessian-coefficient step we
also need to retain the fact that this translated profile is not the zero
polynomial.

Translation is inverted by the opposite translation, so the nonzero source
profile from the least positive actual layer remains nonzero.  Hence at least
one of the two allowed translated coefficients is nonzero.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- **Nonzero two-mode first-interior normal form.**  Under surviving strict
interior support, the canonically translated first positive profile is
supported in the adjacent modes `k-1,k`, and at least one of those two
coefficients is nonzero. -/
theorem exists_firstInteriorAffineLayer_translated_support_twoMode_nonzero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D,
      let alpha : K :=
        -((MvPolynomial.coeff C.ray.facetExponent P.carrier *
              ((F.locked.ell : K) + 1)) /
            (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
              (F.locked.ell : K)))
      let psi := HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
      psi.support ⊆ {A.k - 1, A.k} ∧
        (psi.coeff (A.k - 1) ≠ 0 ∨ psi.coeff A.k ≠ 0) := by
  rcases D.exists_firstInteriorAffineLayer_translated_support_twoMode
      hthree houtThree hnot with ⟨A, hsupport⟩
  refine ⟨A, ?_⟩
  let alpha : K :=
    -((MvPolynomial.coeff C.ray.facetExponent P.carrier *
          ((F.locked.ell : K) + 1)) /
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
          (F.locked.ell : K)))
  let psi : Polynomial K :=
    HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
  have hsupportPsi : psi.support ⊆ {A.k - 1, A.k} := by
    simpa [psi, alpha] using hsupport
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
  refine ⟨hsupportPsi, ?_⟩
  by_cases hlow : psi.coeff (A.k - 1) = 0
  · by_cases hhigh : psi.coeff A.k = 0
    · exfalso
      apply hpsi
      apply Polynomial.ext
      intro n
      simp only [Polynomial.coeff_zero]
      by_cases hnlow : n = A.k - 1
      · subst n
        exact hlow
      by_cases hnhigh : n = A.k
      · subst n
        exact hhigh
      have hnmem : n ∉ psi.support := by
        intro hn
        have hallowed := hsupportPsi hn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hallowed
        rcases hallowed with h | h
        · exact hnlow h
        · exact hnhigh h
      by_contra hcoeff
      exact hnmem (Polynomial.mem_support_iff.mpr hcoeff)
    · exact Or.inr hhigh
  · exact Or.inl hlow

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
