import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitSecondMissingOpening
import Mathlib.Tactic

/-!
# The central reflected line must depart before the finite staircase endpoint

The first three source-honest missing-coordinate openings have total-deficit
orders

    q, J, 2*J-q,

so they lie on the affine order line

    q + m * (J-q),   m = 0,1,2.

This line cannot continue to the literal finite-staircase endpoint.  In the
left orientation the locked endpoint has missing exponent `ell` and total
deficit exactly `ell`; in the right orientation the primitive-highest
endpoint has missing exponent `n-1` and total deficit exactly `n-1`.
Since `q > 0` and `J-q > 0`, either endpoint lies strictly below the
continued reflected line.

Thus every central reflected packet has an honest later source point, with
missing-coordinate exponent at least three, below the first reflected line.
This is the finite-support departure witness needed by the next determinant
coefficient step.  No auxiliary clock or singular-subpolynomial claim is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- A literal source point strictly below the affine order line determined by
the first two missing-coordinate openings. -/
inductive FirstDeficitReflectedLineDepartureData : Prop
  | left
      (q J : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_missing_three_le : 3 ≤ depart 2)
      (depart_below :
        depart 1 + depart 2 < q + depart 2 * (J - q))
  | right
      (q J : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_missing_three_le : 3 ≤ depart 1)
      (depart_below :
        depart 1 + depart 2 < q + depart 1 * (J - q))

/-- **Finite-staircase departure from the first reflected line.**

The endpoint itself supplies a point below the continuation of the
`q,J,2J-q` arithmetic progression.  The second-missing-opening endpoint
bound also forces its missing exponent to be at least three. -/
theorem firstDeficit_reflectedLineDeparture
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitReflectedLineDepartureData := by
  have hqTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  cases G.firstDeficit_secondMissingOpening hthree houtThree with
  | left first opposite q J Kord hq hJ hK
      hfirst hfirst1 hfirst2 hop hop2 hqJ hmin1 hmin2
      second hsecond hsecondOrder hsecond2 hsecondUnique hKle =>
      rcases F.locked_yRoof_mem with
        ⟨hlocked, _hlocked0, hlocked1, hlocked2, _hlocked3⟩
      have hqTwo' : 2 ≤ q := by
        rw [hq]
        exact hqTwo
      have hKFour : 4 ≤ Kord := by
        rw [hK]
        omega
      have hellFour : 4 ≤ F.locked.ell :=
        le_trans hKFour hKle
      have hdPos : 0 < J - q := Nat.sub_pos_of_lt hqJ
      have hdOne : 1 ≤ J - q := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hdPos)
      have hmul :
          F.locked.ell ≤ F.locked.ell * (J - q) := by
        simpa using Nat.mul_le_mul_left F.locked.ell hdOne
      have hbelow :
          C.ray.outsideExponent 1 + C.ray.outsideExponent 2 <
            q + C.ray.outsideExponent 2 * (J - q) := by
        rw [hlocked1, hlocked2]
        omega
      exact .left q J hq hqJ C.ray.outsideExponent hlocked
        (by rw [hlocked2]; omega) hbelow

  | right first opposite q J Kord hq hJ hK
      hfirst hfirst1 hfirst2 hop hop1 hqJ hmin1 hmin2
      second hsecond hsecondOrder hsecond1 hsecondUnique hKle =>
      rcases F.highest_zRoof_mem with
        ⟨hhigh, _hhigh0, hhigh1, hhigh2, _hhigh3⟩
      have hqTwo' : 2 ≤ q := by
        rw [hq]
        exact hqTwo
      have hKFour : 4 ≤ Kord := by
        rw [hK]
        omega
      have hnFour : 4 ≤ F.highest.n - 1 :=
        le_trans hKFour hKle
      have hdPos : 0 < J - q := Nat.sub_pos_of_lt hqJ
      have hdOne : 1 ≤ J - q := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hdPos)
      have hmul :
          F.highest.n - 1 ≤
            (F.highest.n - 1) * (J - q) := by
        simpa using Nat.mul_le_mul_left (F.highest.n - 1) hdOne
      have hbelow :
          F.highest.e1 1 + F.highest.e1 2 <
            q + F.highest.e1 1 * (J - q) := by
        rw [hhigh1, hhigh2]
        omega
      exact .right q J hq hqJ F.highest.e1 hhigh
        (by rw [hhigh1]; omega) hbelow


/-- The first source stratum that falls below the reflected order line.  The
minimality is only with respect to the missing-coordinate exponent; this is
exactly what is needed to know that every smaller missing stratum still lies
on or above the line. -/
inductive FirstDeficitMinimalReflectedLineDepartureData : Prop
  | left
      (q J m : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_missing : depart 2 = m)
      (m_three_le : 3 ≤ m)
      (depart_below :
        depart 1 + depart 2 < q + depart 2 * (J - q))
      (minimal :
        ∀ f ∈ P.carrier.support,
          3 ≤ f 2 →
          f 1 + f 2 < q + f 2 * (J - q) →
          m ≤ f 2)
  | right
      (q J m : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_missing : depart 1 = m)
      (m_three_le : 3 ≤ m)
      (depart_below :
        depart 1 + depart 2 < q + depart 1 * (J - q))
      (minimal :
        ∀ f ∈ P.carrier.support,
          3 ≤ f 1 →
          f 1 + f 2 < q + f 1 * (J - q) →
          m ≤ f 1)

/-- **Canonical first departure.**

Finite support is not needed explicitly here: well-ordering of the natural
missing-coordinate exponent selects the least stratum containing a source
point below the reflected line. -/
theorem firstDeficit_minimalReflectedLineDeparture
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitMinimalReflectedLineDepartureData := by
  cases G.firstDeficit_reflectedLineDeparture hthree houtThree with
  | left q J hq hqJ depart hdepart hm3 hbelow =>
      let pred : ℕ → Prop := fun m =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          f 2 = m ∧
          3 ≤ m ∧
          f 1 + f 2 < q + f 2 * (J - q)
      have hex : ∃ m, pred m := by
        refine ⟨depart 2, depart, hdepart, rfl, hm3, hbelow⟩
      let m := Nat.find hex
      have hmSpec : pred m := Nat.find_spec hex
      rcases hmSpec with ⟨f, hf, hf2, hm3', hfbelow⟩
      refine .left q J m hq hqJ f hf hf2 hm3' hfbelow ?_
      intro g hg hg3 hgbelow
      apply Nat.find_min' hex
      exact ⟨g, hg, rfl, hg3, hgbelow⟩

  | right q J hq hqJ depart hdepart hm3 hbelow =>
      let pred : ℕ → Prop := fun m =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          f 1 = m ∧
          3 ≤ m ∧
          f 1 + f 2 < q + f 1 * (J - q)
      have hex : ∃ m, pred m := by
        refine ⟨depart 1, depart, hdepart, rfl, hm3, hbelow⟩
      let m := Nat.find hex
      have hmSpec : pred m := Nat.find_spec hex
      rcases hmSpec with ⟨f, hf, hf1, hm3', hfbelow⟩
      refine .right q J m hq hqJ f hf hf1 hm3' hfbelow ?_
      intro g hg hg3 hgbelow
      apply Nat.find_min' hex
      exact ⟨g, hg, rfl, hg3, hgbelow⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
