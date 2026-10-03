import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineLayer
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 exact affine-line realisation of the first strict-interior layer

The first strict-interior layer now has an injective longitudinal coordinate
and an exact coefficient profile.  This file packages it as the generic
`RankThreeAffineLineData` already used by the rank-three moment machinery and
proves that the resulting multivariate polynomial is literally the selected
parameter layer.

No Hessian-singularity or profile-degree hypothesis is added here.
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

/-- Every actual first-layer support exponent contributes its coordinate-zero
index to the extracted profile. -/
theorem coefficientProfile_mem_of_layer_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    e 0 ∈ A.coefficientProfile.support := by
  rw [Polynomial.mem_support_iff]
  rw [A.coeff_coefficientProfile_of_mem he]
  exact MvPolynomial.mem_support_iff.mp he

/-- Conversely, every supported profile index is realised by an actual
first-layer source exponent. -/
theorem exists_layerExponent_of_coefficientProfile_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    {n : ℕ} (hn : n ∈ A.coefficientProfile.support) :
    ∃ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
      e 0 = n := by
  classical
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  by_contra hnone
  have hzero : A.coefficientProfile.coeff n = 0 := by
    unfold coefficientProfile
    dsimp only [L]
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    have hne : e 0 ≠ n := by
      intro h
      apply hnone
      exact ⟨e, by simpa [L] using he, h⟩
    simp [Polynomial.coeff_monomial, hne, Ne.symm hne]
  exact (Polynomial.mem_support_iff.mp hn) hzero

/-- Canonical exponent chosen above a supported coefficient-profile index. -/
noncomputable def exponentAt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if hn : n ∈ A.coefficientProfile.support then
    Classical.choose (A.exists_layerExponent_of_coefficientProfile_mem hn)
  else 0

/-- The chosen exponent is an actual first-layer support point and has the
requested coordinate-zero index. -/
theorem exponentAt_spec
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    {n : ℕ} (hn : n ∈ A.coefficientProfile.support) :
    A.exponentAt n ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support ∧
      A.exponentAt n 0 = n := by
  unfold exponentAt
  rw [dif_pos hn]
  exact Classical.choose_spec
    (A.exists_layerExponent_of_coefficientProfile_mem hn)

/-- The selected first layer is an honest instance of the generic affine
rank-three line, with base `(0,k,j+1,V(k+j))` and direction
`(1,-1,-1,-V)`. -/
noncomputable def affineLineData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    HC4.Polynomial.RankThreeAffineLineData
      A.k (A.j + 1) (F.V * (A.k + A.j)) 1
      (-1 : K) (-1 : K) (-(F.V : K)) A.coefficientProfile where
  exponent := A.exponentAt
  affine := by
    intro n hn
    have hs := A.exponentAt_spec hn
    rcases A.coordinates (A.exponentAt n) hs.1 with ⟨hpair, hfirst, hsecond⟩
    have haff := D.firstPositiveLayer_affine_cast
      (K := K) hpair hfirst hsecond
    rw [hs.2] at haff
    simpa only [Nat.cast_one] using haff

/-- The generic affine-line realisation reconstructs the selected first layer
exactly, so all later moment identities remain source-honest. -/
theorem affineLineData_polynomial_eq_layer
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    A.affineLineData.polynomial =
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer) := by
  classical
  let G := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  let L := A.affineLineData
  change L.polynomial = G
  apply MvPolynomial.ext
  intro d
  simp only [HC4.Polynomial.RankThreeAffineLineData.polynomial,
    Polynomial.sum_def]
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ G.support
  · have hidx : d 0 ∈ A.coefficientProfile.support :=
      A.coefficientProfile_mem_of_layer_mem (by simpa [G] using hd)
    have hexp : L.exponent (d 0) = d := by
      have hs := A.exponentAt_spec hidx
      change A.exponentAt (d 0) = d
      exact A.eq_of_zeroCoordinate_eq hs.1 (by simpa [G] using hd) hs.2
    have hcoeff : A.coefficientProfile.coeff (d 0) =
        MvPolynomial.coeff d G := by
      simpa [G] using
        A.coeff_coefficientProfile_of_mem (by simpa [G] using hd)
    rw [Finset.sum_eq_single (d 0)]
    · rw [L.term_eq_monomial]
      simp [hexp, hcoeff]
    · intro n hn hnd
      have hne : L.exponent n ≠ d := by
        intro heq
        have h0 := congrArg (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) heq
        have hn0 : L.exponent n (0 : Fin 4) = n := by
          have hz := L.exponent_zero_eq hn
          simpa using hz
        rw [hn0] at h0
        exact hnd h0
      rw [L.term_eq_monomial]
      simp [hne]
    · intro hnot
      exact (hnot hidx).elim
  · have hd0 : MvPolynomial.coeff d G = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hd0]
    apply Finset.sum_eq_zero
    intro n hn
    have hs := A.exponentAt_spec hn
    have hLmem : L.exponent n ∈ G.support := by
      change A.exponentAt n ∈ G.support
      simpa [G] using hs.1
    have hne : L.exponent n ≠ d := by
      intro heq
      apply hd
      simpa [heq] using hLmem
    rw [L.term_eq_monomial]
    simp [hne]

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
