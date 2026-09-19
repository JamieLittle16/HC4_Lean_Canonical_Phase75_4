import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorTwoModeNonzero
import Mathlib.Tactic

/-!
# A19 exact translated two-mode normal form

The preceding module retains nonvanishing after translating the first
strict-interior coefficient profile to the root of the locked affine form.
This file packages the support statement into the literal polynomial normal
form consumed by the higher-order Hessian calculation:

    psi = p X^(k-1) + q X^k,

with `p != 0` or `q != 0`.
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

/-- **Literal nonzero two-mode normal form.**  Failure of endpoint-only support
produces a first strict-interior layer whose translated coefficient profile is
exactly a linear combination of the adjacent powers `X^(k-1)` and `X^k`, with
at least one nonzero coefficient. -/
theorem exists_firstInteriorAffineLayer_translated_eq_twoMode
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
    ∃ (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) (p q : K),
      let alpha : K :=
        -((MvPolynomial.coeff C.ray.facetExponent P.carrier *
              ((F.locked.ell : K) + 1)) /
            (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
              (F.locked.ell : K)))
      let psi := HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
      (p ≠ 0 ∨ q ≠ 0) ∧
        psi = Polynomial.C p * Polynomial.X ^ (A.k - 1) +
          Polynomial.C q * Polynomial.X ^ A.k := by
  rcases D.exists_firstInteriorAffineLayer_translated_support_twoMode_nonzero
      hthree houtThree hnot with ⟨A, hsupport, hmode⟩
  let alpha : K :=
    -((MvPolynomial.coeff C.ray.facetExponent P.carrier *
          ((F.locked.ell : K) + 1)) /
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
          (F.locked.ell : K)))
  let psi : Polynomial K :=
    HC4.Polynomial.translatePolynomial alpha A.coefficientProfile
  let p : K := psi.coeff (A.k - 1)
  let q : K := psi.coeff A.k
  have hsupportPsi : psi.support ⊆ {A.k - 1, A.k} := by
    simpa [psi, alpha] using hsupport
  have hmode' : p ≠ 0 ∨ q ≠ 0 := by
    simpa [p, q, psi, alpha] using hmode
  refine ⟨A, p, q, ?_⟩
  dsimp only
  refine ⟨hmode', ?_⟩
  change psi = Polynomial.C p * Polynomial.X ^ (A.k - 1) +
    Polynomial.C q * Polynomial.X ^ A.k
  apply Polynomial.ext
  intro n
  by_cases hlow : n = A.k - 1
  · subst n
    have hneq : A.k - 1 ≠ A.k := by omega
    simp [p, q, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hneq]
  by_cases hhigh : n = A.k
  · subst n
    have hneq : A.k ≠ A.k - 1 := by omega
    simp [p, q, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hneq]
  have hcoeff : psi.coeff n = 0 := by
    by_contra hn
    have hnmem : n ∈ psi.support := Polynomial.mem_support_iff.mpr hn
    have hallowed := hsupportPsi hnmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hallowed
    rcases hallowed with h | h
    · exact hlow h
    · exact hhigh h
  rw [hcoeff]
  simp [p, q, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hlow, hhigh]

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
