import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseEndpointEuler
import HC4.Polynomial.AffineEulerTwoRootDistinctRoots
import Mathlib.Tactic

/-!
# A19 one-fibre endpoint roots must coincide

For a contact-side affine staircase package, the retained quotient wall gives
its exact arithmetic relation

    (n - 1) * j = ell * (n - k).

In the one-fibre case the same nonzero source profile satisfies both endpoint
Euler equations.  If their affine roots were distinct, the state-free
multiplicity theorem would force

    k - 1 = 1,   j = 1,

hence `k=2`.  The wall would then read

    n - 1 = ell * (n - 2).

But the live contact separation gives `n <= ell`, while strict interiority of
`k=2` gives `3 <= n`; the displayed equality is impossible.  Therefore the
two literal endpoint affine roots coincide.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- Every honest contact-side affine package lies on the exact finite
staircase wall. -/
theorem wallSlope_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ((F.highest.n : ℤ) - 1) * (A.j : ℤ) =
      (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (A.k : ℤ)) := by
  have hLne :
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer) ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero D.family D.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, _heOrder⟩
  rcases A.coordinates e he with ⟨hpair, hfirst, _hsecond⟩
  have hs := F.support_staircase_equations hthree houtThree heP
  dsimp only at hs
  have hpairQ :
      (rankThreeQuotientCoordinate 1 F.V e).pair = A.k := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hpair
  have hfirstQ :
      (rankThreeQuotientCoordinate 1 F.V e).firstTransverse = A.j + 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hfirst
  have hwall := hs.1
  rw [hpairQ, hfirstQ] at hwall
  push_cast at hwall
  nlinarith

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- **One-fibre root coupling.**  The locked-end and primitive-highest affine
forms have the same root on the unique surviving interior source profile. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_endpointRoots_eq
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
    -((MvPolynomial.coeff C.ray.facetExponent P.carrier *
          ((F.locked.ell : K) + 1)) /
        (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
          (F.locked.ell : K))) =
      -((MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K)) /
        (MvPolynomial.coeff F.highest.e1 S.slice *
          ((F.highest.n - 1 : ℕ) : K))) := by
  let clo : K :=
    MvPolynomial.coeff C.ray.facetExponent P.carrier *
      ((F.locked.ell : K) + 1)
  let dlo : K :=
    MvPolynomial.coeff C.ray.outsideExponent P.carrier *
      (F.locked.ell : K)
  let chi : K :=
    MvPolynomial.coeff F.highest.e0 S.slice * (F.highest.n : K)
  let dhi : K :=
    MvPolynomial.coeff F.highest.e1 S.slice *
      ((F.highest.n - 1 : ℕ) : K)

  have hb : MvPolynomial.coeff C.ray.outsideExponent P.carrier ≠ 0 :=
    F.locked.outside_provenance.carrier_coeff_ne
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hdlo : dlo ≠ 0 := by
    dsimp [dlo]
    exact mul_ne_zero hb hellK
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

  rcases F.oneFiber_commonProfile_dualEuler
      Alo Ahi hthree houtThree hext with ⟨hphi, hlo, hhi⟩
  have hlo' :
      affineTwoRootEulerOperator clo dlo (Alo.k - 1)
        Alo.coefficientProfile = 0 := by
    simpa [clo, dlo] using hlo
  have hhi' :
      affineTwoRootEulerOperator chi dhi Alo.j
        Alo.coefficientProfile = 0 := by
    simpa [chi, dhi] using hhi

  by_contra hne
  have hones := HC4.Polynomial.lowerRoots_eq_one_of_distinct_affineTwoRoot
    clo dlo chi dhi (Alo.k - 1) Alo.j Alo.coefficientProfile
    hdlo hdhi (by omega) Alo.j_pos hphi hlo' hhi'
    (by simpa [clo, dlo, chi, dhi] using hne)
  have hk : Alo.k = 2 := by omega
  have hj : Alo.j = 1 := hones.2
  have hwall := Alo.wallSlope_eq hthree houtThree
  rw [hk, hj] at hwall
  norm_num at hwall
  have hnleell : F.highest.n ≤ F.locked.ell := by
    omega
  have hnthree : 3 ≤ F.highest.n := by
    rw [hk] at Alo.k_lt_highest
    omega
  have hleft : (F.highest.n : ℤ) - 1 > 0 := by
    exact_mod_cast (show 1 < F.highest.n by omega)
  have hellZ : (F.highest.n : ℤ) ≤ (F.locked.ell : ℤ) := by
    exact_mod_cast hnleell
  have hn2Z : (0 : ℤ) < (F.highest.n : ℤ) - 2 := by
    exact_mod_cast (show 2 < F.highest.n by omega)
  nlinarith

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
