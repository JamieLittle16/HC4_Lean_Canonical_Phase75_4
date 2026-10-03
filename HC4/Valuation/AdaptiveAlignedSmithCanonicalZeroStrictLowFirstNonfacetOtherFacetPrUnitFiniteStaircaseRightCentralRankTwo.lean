import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseRightSourceDeficits
import HC4.Polynomial.UniqueMaximalInitialMonomial
import HC4.Polynomial.MonomialHessianPrincipalMinor
import Mathlib.Tactic

/-!
# Rank-two geometry at a mirrored central unit finite-staircase point
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton HC4.Polynomial HC4.Toric
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData (K := K) state}

/-- A right-unit central `e₁=e₃=0` source point exposes an honest monomial
coordinate-`0` face with nonzero principal `(0,2)` Hessian minor. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.central_coordinateMax_face_rankTwo
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {c : Fin 4 →₀ ℕ}
    (hc : c ∈ P.carrier.support) (hc1 : c 1 = 0) (hc3 : c 3 = 0) :
    ∃ D : HC4.Newton.CoordinateMaxInitialData P.carrier (0 : Fin 4),
      D.level = c 0 ∧
      D.face = MvPolynomial.monomial c (MvPolynomial.coeff c P.carrier) ∧
      HC4.Polynomial.hessianDeterminant D.face = 0 ∧
      HC4.Polynomial.hessianPrincipalMinor D.face (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
  classical
  have hPne : P.carrier ≠ 0 := MvPolynomial.support_nonempty.mp ⟨c, hc⟩
  let D := HC4.Newton.coordinateMaxInitialData P.carrier hPne (0 : Fin 4)
  have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by exact_mod_cast F.locked.ell_pos
  have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
  have hnNat : 1 < F.highest.n := by omega
  have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by exact_mod_cast hnNat
  have hnOneZ : (0 : ℤ) < (F.highest.n : ℤ) - 1 := by omega
  have hcoefZ : (0 : ℤ) < (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
    omega
  have hcChord := F.support_deficit_chord hthree houtThree hc
  rw [hc1, hc3] at hcChord
  norm_num at hcChord

  have hmax0 : ∀ e ∈ P.carrier.support, e 0 ≤ c 0 := by
    intro e he
    have heChord := F.support_deficit_chord hthree houtThree he
    have hleft :
        (0 : ℤ) ≤ (F.locked.ell : ℤ) * (e 1 : ℤ) +
          ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) := by positivity
    have hdiff :
        ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
            ((c 0 : ℤ) - (e 0 : ℤ)) =
          (F.locked.ell : ℤ) * (e 1 : ℤ) +
            ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) := by
      nlinarith only [hcChord, heChord]
    have hdiffNonneg : (0 : ℤ) ≤ (c 0 : ℤ) - (e 0 : ℤ) := by
      by_contra hnot
      have hneg : (c 0 : ℤ) - (e 0 : ℤ) < 0 := lt_of_not_ge hnot
      have hprodNeg :
          ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
              ((c 0 : ℤ) - (e 0 : ℤ)) < 0 :=
        mul_neg_of_pos_of_neg hcoefZ hneg
      rw [hdiff] at hprodNeg
      exact (not_lt_of_ge hleft) hprodNeg
    have h0Z : (e 0 : ℤ) ≤ (c 0 : ℤ) := by linarith
    exact_mod_cast h0Z

  have hunique0 : ∀ e ∈ P.carrier.support, e 0 = c 0 → e = c := by
    intro e he he0
    have heChord := F.support_deficit_chord hthree houtThree he
    rw [he0] at heChord
    have hsum :
        (F.locked.ell : ℤ) * (e 1 : ℤ) +
          ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) = 0 := by
      nlinarith only [hcChord, heChord]
    have hterm1 : (0 : ℤ) ≤ (F.locked.ell : ℤ) * (e 1 : ℤ) := by positivity
    have hterm3 : (0 : ℤ) ≤ ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) := by positivity
    have hterm1Zero : (F.locked.ell : ℤ) * (e 1 : ℤ) = 0 := by
      nlinarith only [hsum, hterm1, hterm3]
    have hterm3Zero : ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) = 0 := by
      nlinarith only [hsum, hterm1, hterm3]
    have he1Z0 : (e 1 : ℤ) = 0 :=
      (mul_eq_zero.mp hterm1Zero).resolve_left (ne_of_gt hellZ)
    have he3Z0 : (e 3 : ℤ) = 0 :=
      (mul_eq_zero.mp hterm3Zero).resolve_left (ne_of_gt hnOneZ)
    have he1 : e 1 = 0 := by exact_mod_cast he1Z0
    have he3 : e 3 = 0 := by exact_mod_cast he3Z0
    exact F.support_eq_of_deficits_eq hthree houtThree he hc
      (by simpa [hc1] using he1) (by simpa [hc3] using he3)

  have hlevel : D.level = c 0 := by
    have hcLe : c 0 ≤ D.level := D.maximal c hc
    have hwLe : D.witness 0 ≤ c 0 := hmax0 D.witness D.witness_mem
    have hwEq : D.witness 0 = D.level := D.witness_coordinate
    omega
  have hcWeight :
      Finsupp.weight (HC4.Newton.coordinateMaxWeight (0 : Fin 4)) c = (D.level : ℤ) := by
    rw [HC4.Newton.weight_coordinateMaxWeight, hlevel]
  have huniqWeight :
      ∀ e ∈ P.carrier.support,
        Finsupp.weight (HC4.Newton.coordinateMaxWeight (0 : Fin 4)) e = (D.level : ℤ) → e = c := by
    intro e he hw
    rw [HC4.Newton.weight_coordinateMaxWeight, hlevel] at hw
    have h0 : e 0 = c 0 := by exact_mod_cast hw
    exact hunique0 e he h0
  have hmono : D.face = MvPolynomial.monomial c (MvPolynomial.coeff c P.carrier) := by
    rw [D.face_eq]
    exact HC4.Polynomial.initialForm_eq_monomial_of_unique_max
      (HC4.Newton.coordinateMaxWeight (0 : Fin 4)) (D.level : ℤ)
      P.carrier c hc hcWeight D.weight_bound huniqWeight

  have hcWall := F.support_deficit_wall hthree houtThree hc
  rw [hc1, hc3] at hcWall
  norm_num at hcWall
  have hc0GtOne : 1 < c 0 := by
    by_contra hnot
    have hc0Le : c 0 ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (c 0) with hc0Zero | hc0PosNat
    · rw [hc0Zero] at hcWall
      norm_num at hcWall
      have hnPosZ : (0 : ℤ) < (F.highest.n : ℤ) := by omega
      have hrightPos : (0 : ℤ) < (F.locked.ell : ℤ) * (F.highest.n : ℤ) :=
        mul_pos hellZ hnPosZ
      nlinarith only [hcWall, hnOneZ, hrightPos]
    · have hc0Eq : c 0 = 1 := by omega
      rw [hc0Eq] at hcWall
      norm_num at hcWall
      rcases hcWall with hellZero | hnOneZero
      · exact (Nat.ne_of_gt F.locked.ell_pos) hellZero
      · exact (ne_of_gt hnOneZ) hnOneZero
  have hc0Pos : 0 < c 0 := by omega

  have hcurve := (F.support_staircase_equations hthree houtThree hc).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse, one_mul] at hcurve
  push_cast at hcurve
  rw [hc1, hc3] at hcurve
  norm_num at hcurve
  have hc2Z : (c 2 : ℤ) = (c 0 : ℤ) - 1 := by nlinarith only [hcurve]
  have hc0GtOneZ : (1 : ℤ) < (c 0 : ℤ) := by exact_mod_cast hc0GtOne
  have hc2ZPos : (0 : ℤ) < (c 2 : ℤ) := by
    rw [hc2Z]
    omega
  have hc2Pos : 0 < c 2 := by exact_mod_cast hc2ZPos

  have hcoeff : MvPolynomial.coeff c P.carrier ≠ 0 := MvPolynomial.mem_support_iff.mp hc
  have hminorMono :
      HC4.Polynomial.hessianPrincipalMinor
          (MvPolynomial.monomial c (MvPolynomial.coeff c P.carrier))
          (0 : Fin 4) (2 : Fin 4) ≠ 0 :=
    HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      hcoeff (by decide) hc0Pos hc2Pos
  have hminor : HC4.Polynomial.hessianPrincipalMinor D.face (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
    rw [hmono]
    exact hminorMono
  refine ⟨D, hlevel, hmono, ?_, hminor⟩
  exact D.hessian_zero P.hessian_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation