import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairRees
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 unit locked endpoint as the terminal pair-Rees layer

For the unit pair-degree reverse Rees, pair degree one occurs at parameter
order `n-1`.  Quotient-fibre rigidity identifies that whole source fibre with
the two literal locked source monomials.  Consequently the terminal layer is
exactly the locked binomial and its specialised Euler Hessian is the existing
`V = 1` locked-binomial moment Hessian.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- A unit left carrier monomial of pair degree one is literally one of the
two retained locked source exponents. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.eq_locked_of_support_pair_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hpair : (rankThreeQuotientCoordinate 1 1 e).pair = 1) :
    e = C.ray.facetExponent ∨ e = C.ray.outsideExponent := by
  have hpairNat : e 0 + e 1 = 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hpair
  have hpairE : qsOtherFacetPairDegree .pr e = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree]
    exact_mod_cast hpairNat
  have hpairF :
      qsOtherFacetPairDegree .pr C.ray.facetExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.facet_zero, F.locked.facet_one]
  have hqEF :
      rankThreeQuotientCoordinate 1 1 e =
        rankThreeQuotientCoordinate 1 1 C.ray.facetExponent :=
    F.quotient.pair_fiber he F.locked.facet_provenance.carrier_mem
      (hpairE.trans hpairF.symm)
  have hpairO :
      qsOtherFacetPairDegree .pr C.ray.outsideExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.outside_zero, F.locked.outside_one]
  have hqFO :
      rankThreeQuotientCoordinate 1 1 C.ray.facetExponent =
        rankThreeQuotientCoordinate 1 1 C.ray.outsideExponent :=
    F.quotient.pair_fiber
      F.locked.facet_provenance.carrier_mem
      F.locked.outside_provenance.carrier_mem
      (hpairF.trans hpairO.symm)
  have he0cases : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases he0cases with he0 | he0
  · left
    exact HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
      1 1 e C.ray.facetExponent hqEF (by
        rw [he0, F.locked.facet_zero])
  · right
    exact HC4.Polynomial.eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
      1 1 e C.ray.outsideExponent (hqEF.trans hqFO) (by
        rw [he0, F.locked.outside_zero])

namespace QsOtherFacetPrPairReesData

/-- Exact support of the terminal locked unit pair-Rees layer. -/
theorem lockedLayer_support_eq_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    (familyParameterLayer D.family (F.highest.n - 1)).support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
  classical
  have hn2 := F.highest.n_two_le
  rw [D.parameterLayer_support]
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hgap⟩
    have hpairNat : e 0 + e 1 = 1 := by omega
    have hpair : (rankThreeQuotientCoordinate 1 1 e).pair = 1 := by
      simpa [rankThreeQuotientCoordinate] using hpairNat
    exact F.eq_locked_of_support_pair_eq_one he hpair
  · intro heq
    rcases heq with rfl | rfl
    · refine ⟨F.locked.facet_provenance.carrier_mem, ?_⟩
      rw [F.locked.facet_zero, F.locked.facet_one]
      omega
    · refine ⟨F.locked.outside_provenance.carrier_mem, ?_⟩
      rw [F.locked.outside_zero, F.locked.outside_one]
      omega

/-- The terminal unit pair-Rees layer is the literal locked source binomial. -/
theorem lockedLayer_eq_locked_pair_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    familyParameterLayer D.family (F.highest.n - 1) =
      MvPolynomial.monomial C.ray.facetExponent
          (MvPolynomial.coeff C.ray.facetExponent P.carrier) +
        MvPolynomial.monomial C.ray.outsideExponent
          (MvPolynomial.coeff C.ray.outsideExponent P.carrier) := by
  classical
  let L := familyParameterLayer D.family (F.highest.n - 1)
  have hsupp : L.support =
      {C.ray.facetExponent, C.ray.outsideExponent} := by
    dsimp [L]
    exact D.lockedLayer_support_eq_unitLeft F
  have hne : C.ray.facetExponent ≠ C.ray.outsideExponent := by
    intro h
    have h0 := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
    rw [F.locked.facet_zero, F.locked.outside_zero] at h0
    omega
  have hfacetCoeff :
      MvPolynomial.coeff C.ray.facetExponent L =
        MvPolynomial.coeff C.ray.facetExponent P.carrier := by
    dsimp [L]
    rw [D.parameterLayer_coeff]
    simp [F.locked.facet_provenance.carrier_mem,
      F.locked.facet_zero, F.locked.facet_one]
  have houtCoeff :
      MvPolynomial.coeff C.ray.outsideExponent L =
        MvPolynomial.coeff C.ray.outsideExponent P.carrier := by
    dsimp [L]
    rw [D.parameterLayer_coeff]
    simp [F.locked.outside_provenance.carrier_mem,
      F.locked.outside_zero, F.locked.outside_one]
  have hsum := MvPolynomial.as_sum L
  rw [hsupp] at hsum
  rw [Finset.sum_insert] at hsum
  · simp only [Finset.sum_singleton] at hsum
    rw [hfacetCoeff, houtCoeff] at hsum
    exact hsum
  · simpa using hne

/-- Exact locked terminal-layer moment identification for the unit pair-Rees. -/
theorem lockedLayer_specialisedEulerHessian_eq_lockedBinomialMomentHessian_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) :
    let a := MvPolynomial.coeff C.ray.facetExponent P.carrier
    let b := MvPolynomial.coeff C.ray.outsideExponent P.carrier
    (fun r s =>
      rankThreeLineSpecialisation
        (eulerScaledHessian
          (familyParameterLayer D.family (F.highest.n - 1)) r s)) =
      lockedBinomialMomentHessian 1 F.locked.ell a b := by
  classical
  let a : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let phi : Polynomial K := Polynomial.C a + Polynomial.C b * Polynomial.X
  have ha : a ≠ 0 := by
    dsimp [a]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hphiSupport : phi.support = {0, 1} := by
    ext n
    simp only [Polynomial.mem_support_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hn
      by_cases hn0 : n = 0
      · exact Or.inl hn0
      by_cases hn1 : n = 1
      · exact Or.inr hn1
      exfalso
      apply hn
      simp [phi, hn0, hn1]
    · intro hn
      rcases hn with rfl | rfl
      · simp [phi, ha]
      · simp [phi, hb]
  let exponent : ℕ → (Fin 4 →₀ ℕ) := fun n =>
    if n = 0 then C.ray.facetExponent else C.ray.outsideExponent
  let L : RankThreeAffineLineData
      1 (F.locked.ell + 1) (1 * (F.locked.ell + 1)) 1
      (-1 : K) (-1 : K) (-1 : K) phi := {
    exponent := exponent
    affine := by
      intro n hn
      rw [hphiSupport] at hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · funext i
        fin_cases i <;>
          simp [exponent, rankThreeLogBaseExponent, rankThreeLogDirection,
            F.locked.facet_zero, F.locked.facet_one,
            F.locked.facet_two, F.locked.facet_three]
      · funext i
        fin_cases i <;>
          simp [exponent, rankThreeLogBaseExponent, rankThreeLogDirection,
            F.locked.outside_zero, F.locked.outside_one,
            F.locked.outside_two, F.locked.outside_three] <;> ring
  }
  have hpoly :
      L.polynomial = familyParameterLayer D.family (F.highest.n - 1) := by
    have hL :
        L.polynomial =
          MvPolynomial.monomial C.ray.facetExponent a +
            MvPolynomial.monomial C.ray.outsideExponent b := by
      simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
      rw [hphiSupport]
      rw [Finset.sum_insert]
      · simp only [Finset.sum_singleton]
        rw [L.term_eq_monomial, L.term_eq_monomial]
        simp [L, exponent, phi]
      · simp
    rw [hL]
    symm
    simpa [a, b] using D.lockedLayer_eq_locked_pair_unitLeft F
  have hm := L.specialisation_eulerScaledHessian
  rw [hpoly] at hm
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun hm r) s
  simpa [lockedBinomialMomentHessian, phi] using hrs

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
