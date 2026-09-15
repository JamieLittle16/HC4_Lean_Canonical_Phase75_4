import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInteriorAffineLayer
import HC4.Polynomial.HighestBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 moment realisation of the first positive pair-Rees interior layer

The selected first positive pair-Rees layer is now a literal affine staircase
fibre with an injective coordinate-zero parameter and unchanged source-carrier
coefficients.  This file reconstructs that exact layer as
`RankThreeAffineLineData` and identifies its specialised Euler-scaled Hessian
with `parallelStaircaseMomentHessian`.
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

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- Every actual selected-layer support exponent contributes its coordinate-zero
index to the extracted profile. -/
theorem coefficientProfile_mem_of_layer_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support) :
    e 0 ∈ A.coefficientProfile.support := by
  rw [Polynomial.mem_support_iff]
  rw [A.coeff_coefficientProfile_of_mem he]
  exact MvPolynomial.mem_support_iff.mp he

/-- Conversely every supported profile index is realised by an actual source
exponent of the selected pair-Rees layer. -/
theorem exists_layerExponent_of_coefficientProfile_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    {n : ℕ} (hn : n ∈ A.coefficientProfile.support) :
    ∃ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support,
      e 0 = n := by
  classical
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
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

/-- Canonical source exponent over a supported coefficient-profile index. -/
noncomputable def exponentAt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if hn : n ∈ A.coefficientProfile.support then
    Classical.choose (A.exists_layerExponent_of_coefficientProfile_mem hn)
  else 0

/-- The canonical exponent is in the selected layer and has the requested
coordinate-zero value. -/
theorem exponentAt_spec
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    {n : ℕ} (hn : n ∈ A.coefficientProfile.support) :
    A.exponentAt n ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support ∧
      A.exponentAt n 0 = n := by
  unfold exponentAt
  rw [dif_pos hn]
  exact Classical.choose_spec
    (A.exists_layerExponent_of_coefficientProfile_mem hn)

/-- Exact affine-line realisation of the selected pair-Rees layer. -/
noncomputable def affineLineData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
    HC4.Polynomial.RankThreeAffineLineData
      A.k (A.j + 1) (F.V * (A.k + A.j)) 1
      (-1 : K) (-1 : K) (-(F.V : K)) A.coefficientProfile where
  exponent := A.exponentAt
  affine := by
    intro n hn
    have hs := A.exponentAt_spec hn
    rcases A.coordinates (A.exponentAt n) hs.1 with ⟨hpair, hfirst, hsecond⟩
    have hpairK :
        (A.exponentAt n 0 : K) + (A.exponentAt n 1 : K) = (A.k : K) := by
      exact_mod_cast hpair
    have hfirstK :
        (A.exponentAt n 0 : K) + (A.exponentAt n 2 : K) =
          ((A.j + 1 : ℕ) : K) := by
      exact_mod_cast hfirst
    have hsecondK :
        (F.V : K) * (A.exponentAt n 0 : K) +
            (A.exponentAt n 3 : K) =
          (F.V : K) * ((A.k + A.j : ℕ) : K) := by
      exact_mod_cast hsecond
    funext i
    fin_cases i
    · simp [HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection, hs.2]
    · simp [HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection, hs.2]
      linear_combination hpairK
    · simp [HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection, hs.2]
      push_cast at hfirstK
      linear_combination hfirstK
    · simp [HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection, hs.2]
      push_cast at hsecondK
      linear_combination hsecondK

/-- The affine-line polynomial is literally the selected pair-Rees layer. -/
theorem affineLineData_polynomial_eq_layer
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
    A.affineLineData.polynomial =
      familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer) := by
  classical
  let G := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
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
          change A.exponentAt n (0 : Fin 4) = n
          exact (A.exponentAt_spec hn).2
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

/-- **Exact first positive pair-Rees moment identification.** -/
theorem specialisedEulerHessian_eq_parallelStaircaseMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family
            (firstPositiveActualParameterOrder D.family D.positiveLayer))
          r s)) =
      HC4.Polynomial.parallelStaircaseMomentHessian
        F.V A.k A.j A.coefficientProfile := by
  have h := A.affineLineData.specialisation_eulerScaledHessian
  rw [A.affineLineData_polynomial_eq_layer] at h
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun h r) s
  simpa [HC4.Polynomial.parallelStaircaseMomentHessian] using hrs

end QsOtherFacetPrPairFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
