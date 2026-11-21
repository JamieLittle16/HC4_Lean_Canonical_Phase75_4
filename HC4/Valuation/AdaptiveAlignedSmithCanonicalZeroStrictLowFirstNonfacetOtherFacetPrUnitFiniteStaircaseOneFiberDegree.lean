import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseEndpointEuler
import HC4.Polynomial.AffineEulerTwoRootDegree
import Mathlib.Tactic

/-!
# A19 unit one-fibre degree coupling

When the two unit extremal selectors choose the same strict-interior pair
fibre, the common nonzero source coefficient profile satisfies both endpoint
affine two-root Euler equations.  The state-free degree theorem then places its
ordinary degree in both adjacent indicial pairs

    {k-1,k}  and  {j,j+1},

forcing one of the three adjacent staircase diagonals

    j + 2 = k,   j + 1 = k,   or   j = k.
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

/-- In the unit one-fibre case, the common profile degree is constrained by
both endpoint indicial pairs. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_commonProfile_degree_pairs
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
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
  have hkpred : (Alo.k - 1) + 1 = Alo.k := by
    exact Nat.sub_add_cancel (Nat.le_of_lt Alo.k_gt_one)
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
  have hn_gt_one : 1 < F.highest.n :=
    lt_trans Ahi.k_gt_one Ahi.k_lt_highest
  have hnsub : F.highest.n - 1 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt hn_gt_one)
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

/-- Therefore a unit one-fibre staircase can occur only on three adjacent
`(k,j)` diagonals. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_three_diagonals
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k) :
    Alo.j + 2 = Alo.k ∨ Alo.j + 1 = Alo.k ∨ Alo.j = Alo.k := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  have hkone : 1 ≤ Alo.k := Nat.le_of_lt Alo.k_gt_one
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
