import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerFiber
import Mathlib.Tactic

/-!
# A19 affine coordinates for every nonzero planar-contact layer

The first-interior development constructed affine source coordinates only for
the least positive actual layer.  The all-depth singular-family argument needs
the same source-honest description at an arbitrary nonzero exact parameter
layer.

The preceding exact-layer quotient-fibre theorem supplies the missing uniform
input.  Choosing one supported monomial fixes the pair degree `k` and staircase
height `j`; every other supported monomial has the same quotient coordinate,
so the retained staircase equations put the whole layer on the affine line

    (t, k-t, j+1-t, V*(k+j-t)).

No new support or degree assumption is introduced.
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

/-- **Uniform exact-layer affine coordinates.**  Every nonzero exact layer of
the singular planar-contact family is supported on one literal affine
rank-three line, with exact coefficients inherited from the planar carrier. -/
theorem exists_parameterLayer_affineCoordinates
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q : ℕ}
    (hLayer : familyParameterLayer D.family q ≠ 0) :
    ∃ k j : ℕ,
      1 ≤ k ∧ k ≤ F.highest.n ∧ j ≤ F.locked.ell ∧
      ∀ e ∈ (familyParameterLayer D.family q).support,
        e 0 + e 1 = k ∧
        e 0 + e 2 = j + 1 ∧
        F.V * e 0 + e 3 = F.V * (k + j) ∧
        MvPolynomial.coeff e (familyParameterLayer D.family q) =
          MvPolynomial.coeff e P.carrier := by
  classical
  rcases MvPolynomial.support_nonempty.mpr hLayer with ⟨e, he⟩
  have heP : e ∈ P.carrier.support :=
    (D.parameterLayer_support_source_and_order he).1
  rcases F.support_staircase_classification hthree houtThree heP with
    ⟨j, hj, hkn, hjell, _hj0, _hjellEq⟩
  let k := (rankThreeQuotientCoordinate 1 F.V e).pair
  have hkpos : 1 ≤ k := by
    dsimp [k]
    exact F.support_pair_pos hthree houtThree heP
  have hkle : k ≤ F.highest.n := by
    dsimp [k]
    exact hkn
  refine ⟨k, j, hkpos, hkle, hjell, ?_⟩
  intro f hf
  have hq :
      rankThreeQuotientCoordinate 1 F.V f =
        rankThreeQuotientCoordinate 1 F.V e :=
    D.parameterLayer_quotient_fiber hthree houtThree hf he
  have hpair :
      (rankThreeQuotientCoordinate 1 F.V f).pair = k := by
    rw [hq]
    rfl
  have hfirst :
      (rankThreeQuotientCoordinate 1 F.V f).firstTransverse = j + 1 := by
    rw [hq]
    exact hj
  have hpairNat : f 0 + f 1 = k := by
    simpa [rankThreeQuotientCoordinate] using hpair
  have hfirstNat : f 0 + f 2 = j + 1 := by
    simpa [rankThreeQuotientCoordinate] using hfirst
  have hfP : f ∈ P.carrier.support :=
    (D.parameterLayer_support_source_and_order hf).1
  have hstair := F.support_staircase_equations hthree houtThree hfP
  dsimp only at hstair
  have hsecondZ := hstair.2
  change
    ((F.V * f 0 + f 3 : ℕ) : ℤ) =
      (F.V : ℤ) *
        (((f 0 + f 1 : ℕ) : ℤ) + ((f 0 + f 2 : ℕ) : ℤ) - 1)
    at hsecondZ
  rw [hpairNat, hfirstNat] at hsecondZ
  have hsecond : F.V * f 0 + f 3 = F.V * (k + j) := by
    have hsecondZ' :
        ((F.V * f 0 + f 3 : ℕ) : ℤ) =
          ((F.V * (k + j) : ℕ) : ℤ) := by
      push_cast at hsecondZ ⊢
      nlinarith
    exact_mod_cast hsecondZ'
  exact ⟨hpairNat, hfirstNat, hsecond,
    D.parameterLayer_coeff_eq_carrier_of_mem hf⟩

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
