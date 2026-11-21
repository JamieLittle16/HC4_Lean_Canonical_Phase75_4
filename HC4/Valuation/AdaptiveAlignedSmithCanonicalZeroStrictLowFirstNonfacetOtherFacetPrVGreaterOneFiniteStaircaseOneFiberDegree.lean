import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseEndpointEuler
import HC4.Polynomial.AffineEulerTwoRootDegree
import Mathlib.Tactic

/-!
# A19 one-fibre degree coupling

When the two extremal Rees constructions select the same interior fibre, the
preceding source-honest identification gives one nonzero coefficient profile
satisfying both endpoint affine two-root Euler equations.

The state-free degree theorem then applies twice.  The ordinary degree of the
common profile lies in both adjacent sets

    {k-1,k}  and  {j,j+1}.

Hence the staircase coordinates are forced onto one of only three diagonals:

    j + 2 = k,   j + 1 = k,   or   j = k.

This does not assert degree one; in particular it retains the known
`k=j=2` affine-square diagnostic.
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

/-- In the one-fibre case, the common profile degree is constrained by both
endpoint indicial pairs. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_commonProfile_degree_pairs
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
    (Alo.coefficientProfile.natDegree = Alo.k - 1 ∨
      Alo.coefficientProfile.natDegree = Alo.k) ∧
    (Alo.coefficientProfile.natDegree = Alo.j ∨
      Alo.coefficientProfile.natDegree = Alo.j + 1) := by
  rcases F.oneFiber_commonProfile_dualEuler
      Alo Ahi hthree houtThree hext with ⟨hphi, hlo, hhi⟩

  let dlo : K :=
    MvPolynomial.coeff C.ray.outsideExponent P.carrier *
      (F.locked.ell : K)
  have hb : MvPolynomial.coeff C.ray.outsideExponent P.carrier ≠ 0 :=
    F.locked.outside_provenance.carrier_coeff_ne
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hdlo : dlo ≠ 0 := by
    dsimp [dlo]
    exact mul_ne_zero hb hellK
  have hloDegree := HC4.Polynomial.natDegree_eq_root_or_succ_of_affineTwoRoot
    (MvPolynomial.coeff C.ray.facetExponent P.carrier *
      ((F.locked.ell : K) + 1))
    dlo (Alo.k - 1) Alo.coefficientProfile hdlo hphi
    (by simpa [dlo] using hlo)
  have hkpred : (Alo.k - 1) + 1 = Alo.k := by omega
  have hloDegree' :
      Alo.coefficientProfile.natDegree = Alo.k - 1 ∨
        Alo.coefficientProfile.natDegree = Alo.k := by
    simpa [hkpred] using hloDegree

  let dhi : K :=
    MvPolynomial.coeff F.highest.e1 S.slice *
      ((F.highest.n - 1 : ℕ) : K)
  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have he1ne : MvPolynomial.coeff F.highest.e1 S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he1S
  have hnsub : F.highest.n - 1 ≠ 0 := by omega
  have hnsubK : ((F.highest.n - 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hnsub
  have hdhi : dhi ≠ 0 := by
    dsimp [dhi]
    exact mul_ne_zero he1ne hnsubK
  have hhiDegree := HC4.Polynomial.natDegree_eq_root_or_succ_of_affineTwoRoot
    (MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K))
    dhi Alo.j Alo.coefficientProfile hdhi hphi
    (by simpa [dhi] using hhi)

  exact ⟨hloDegree', hhiDegree⟩

/-- Therefore a one-fibre staircase can occur only on three adjacent
`(k,j)` diagonals. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_three_diagonals
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
    Alo.j + 2 = Alo.k ∨ Alo.j + 1 = Alo.k ∨ Alo.j = Alo.k := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi
  · right
    left
    omega
  · left
    omega
  · right
    right
    omega
  · right
    left
    omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
