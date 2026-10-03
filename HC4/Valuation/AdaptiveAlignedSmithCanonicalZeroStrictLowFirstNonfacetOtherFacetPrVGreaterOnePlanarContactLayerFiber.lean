import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorFirstLayer
import Mathlib.Tactic

/-!
# A19 planar-contact exact-layer quotient fibres

The first-positive-layer development only needed fibre rigidity at the least
positive actual Rees order.  The finite staircase/profile closure needs the
same fact uniformly at every exact parameter order.

The retained source contact interpolation makes this immediate.  Two carrier
monomials in the same exact reverse-Rees layer have the same contact order;
the interpolation formula then gives the same pair degree.  The two affine
carrier equations upgrade equality of pair degree to equality of the full
rank-three quotient coordinate.
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

/-- Exact layer-index form of the retained contact interpolation law.  A
monomial supported in parameter layer `q` has pair degree `k` satisfying

    `(n - 1) * q = B * (k - 1)`,

where `B = (V+1)(ell+1-n)` is the positive locked-to-highest contact step. -/
theorem parameterLayer_contactOrder_interpolation
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q : ℕ} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support) :
    (F.highest.n - 1) * q =
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
        ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) := by
  rcases D.parameterLayer_support_source_and_order he with ⟨heP, heOrder⟩
  have hinterp := F.contactOrder_interpolation hthree houtThree heP
  rw [← D.reverseOrder_eq_quotientContactOrder hthree houtThree e,
    heOrder] at hinterp
  exact hinterp

/-- Every exact planar-contact Rees layer has one pair degree.  This is the
all-depth form of the first-positive-layer pair-fibre statement. -/
theorem parameterLayer_pair_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q : ℕ} {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support)
    (hf : f ∈ (familyParameterLayer D.family q).support) :
    (rankThreeQuotientCoordinate 1 F.V e).pair =
      (rankThreeQuotientCoordinate 1 F.V f).pair := by
  have heInterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree he
  have hfInterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree hf
  have hprod :
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) =
        (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 F.V f).pair - 1) := by
    calc
      (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) =
        (F.highest.n - 1) * q := heInterp.symm
      _ = (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
          ((rankThreeQuotientCoordinate 1 F.V f).pair - 1) := hfInterp
  have hfactor :
      0 < (F.V + 1) * (F.locked.ell + 1 - F.highest.n) := by
    exact Nat.mul_pos (by omega)
      (by have := F.highest_n_lt_locked_height hthree houtThree; omega)
  have hsub :
      (rankThreeQuotientCoordinate 1 F.V e).pair - 1 =
        (rankThreeQuotientCoordinate 1 F.V f).pair - 1 := by
    exact Nat.eq_of_mul_eq_mul_left hfactor hprod
  have heP := (D.parameterLayer_support_source_and_order he).1
  have hfP := (D.parameterLayer_support_source_and_order hf).1
  have hePos := F.support_pair_pos hthree houtThree heP
  have hfPos := F.support_pair_pos hthree houtThree hfP
  calc
    (rankThreeQuotientCoordinate 1 F.V e).pair =
        ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) + 1 :=
      (Nat.sub_add_cancel hePos).symm
    _ = ((rankThreeQuotientCoordinate 1 F.V f).pair - 1) + 1 := by
      rw [hsub]
    _ = (rankThreeQuotientCoordinate 1 F.V f).pair :=
      Nat.sub_add_cancel hfPos

/-- Every exact planar-contact Rees layer is in fact a single full quotient
fibre.  The retained pair-fibre injectivity of the two affine carrier
constraints supplies the transverse coordinates once the pair degree agrees. -/
theorem parameterLayer_quotient_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q : ℕ} {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family q).support)
    (hf : f ∈ (familyParameterLayer D.family q).support) :
    rankThreeQuotientCoordinate 1 F.V e =
      rankThreeQuotientCoordinate 1 F.V f := by
  have hp := D.parameterLayer_pair_fiber hthree houtThree he hf
  apply F.quotient.pair_fiber
    (D.parameterLayer_support_source_and_order he).1
    (D.parameterLayer_support_source_and_order hf).1
  change e 0 + e 1 = f 0 + f 1 at hp
  change (e 0 : ℤ) + (e 1 : ℤ) = (f 0 : ℤ) + (f 1 : ℤ)
  exact_mod_cast hp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation