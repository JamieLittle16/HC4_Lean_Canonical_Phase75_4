import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarInteriorAffineLayer
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic

/-!
# A19 moment realisation of the first unit contact interior layer

The selected first positive unit contact layer is an exact affine staircase
fibre with injective longitudinal coordinate and literal source coefficients.
This file packages it as `RankThreeAffineLineData` and identifies its
specialised Euler-scaled Hessian with the `V = 1` parallel staircase moment
Hessian used by the generic first-variation bridge.
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

namespace QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

/-- Every selected-layer support exponent contributes its longitudinal index to
its coefficient profile. -/
theorem coefficientProfile_mem_of_layer_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    e 0 ∈ A.coefficientProfile.support := by
  rw [Polynomial.mem_support_iff]
  rw [A.coeff_coefficientProfile_of_mem he]
  exact MvPolynomial.mem_support_iff.mp he

/-- Conversely, every supported profile index is realised by an actual exponent
of the selected unit contact layer. -/
theorem exists_layerExponent_of_coefficientProfile_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
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

/-- Canonical source exponent above a supported profile index. -/
noncomputable def exponentAt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if hn : n ∈ A.coefficientProfile.support then
    Classical.choose (A.exists_layerExponent_of_coefficientProfile_mem hn)
  else 0

/-- The canonical exponent is in the selected layer and has the requested
longitudinal index. -/
theorem exponentAt_spec
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    {n : ℕ} (hn : n ∈ A.coefficientProfile.support) :
    A.exponentAt n ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support ∧
      A.exponentAt n 0 = n := by
  unfold exponentAt
  rw [dif_pos hn]
  exact Classical.choose_spec
    (A.exists_layerExponent_of_coefficientProfile_mem hn)

/-- Exact affine-line realisation of the selected unit contact layer. -/
noncomputable def affineLineData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) :
    HC4.Polynomial.RankThreeAffineLineData
      A.k (A.j + 1) (A.k + A.j) 1
      (-1 : K) (-1 : K) (-1 : K) A.coefficientProfile where
  exponent := A.exponentAt
  affine := by
    intro n hn
    have hs := A.exponentAt_spec hn
    rcases A.coordinates (A.exponentAt n) hs.1 with ⟨hpair, hfirst, hsecond⟩
    have hzeroK : (A.exponentAt n 0 : K) = (n : K) := by
      exact_mod_cast hs.2
    have hpairK :
        (A.exponentAt n 0 : K) + (A.exponentAt n 1 : K) = (A.k : K) := by
      exact_mod_cast hpair
    have hfirstK :
        (A.exponentAt n 0 : K) + (A.exponentAt n 2 : K) =
          ((A.j + 1 : ℕ) : K) := by
      exact_mod_cast hfirst
    have hsecondK :
        (A.exponentAt n 0 : K) + (A.exponentAt n 3 : K) =
          ((A.k + A.j : ℕ) : K) := by
      exact_mod_cast hsecond
    have h1K :
        (A.exponentAt n 1 : K) = (A.k : K) - (n : K) := by
      linear_combination hpairK - hzeroK
    push_cast at hfirstK
    have h2K :
        (A.exponentAt n 2 : K) = (A.j : K) + 1 - (n : K) := by
      linear_combination hfirstK - hzeroK
    push_cast at hsecondK
    have h3K :
        (A.exponentAt n 3 : K) = (A.k : K) + (A.j : K) - (n : K) := by
      linear_combination hsecondK - hzeroK
    funext i
    fin_cases i <;>
      simp [HC4.Polynomial.rankThreeLogBaseExponent,
        HC4.Polynomial.rankThreeLogDirection,
        hzeroK, h1K, h2K, h3K] <;> ring

/-- The affine-line polynomial is literally the selected unit contact layer. -/
theorem affineLineData_polynomial_eq_layer
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) :
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
        have h0 : L.exponent n (0 : Fin 4) = d 0 :=
          congrArg (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) heq
        have hn0 : L.exponent n (0 : Fin 4) = n := by
          change A.exponentAt n (0 : Fin 4) = n
          exact (A.exponentAt_spec hn).2
        have hnd0 : n = d 0 := by
          calc
            n = L.exponent n (0 : Fin 4) := hn0.symm
            _ = d 0 := h0
        exact hnd hnd0
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

/-- Exact first positive unit contact moment identification. -/
theorem specialisedEulerHessian_eq_parallelStaircaseMomentHessian
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) :
    (fun r s =>
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer D.family
            (firstPositiveActualParameterOrder D.family D.hasPositiveLayer))
          r s)) =
      HC4.Polynomial.parallelStaircaseMomentHessian
        1 A.k A.j A.coefficientProfile := by
  have h := A.affineLineData.specialisation_eulerScaledHessian
  rw [A.affineLineData_polynomial_eq_layer] at h
  apply Matrix.ext
  intro r s
  have hrs := congrFun (congrFun h r) s
  simpa [HC4.Polynomial.parallelStaircaseMomentHessian] using hrs

end QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
