import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitFiniteStaircase
import HC4.Valuation.StaggeredSingularSecondKernelInteraction
import Mathlib.Tactic

/-!
# Second missing-coordinate opening of the central reflected packet

The first source-honest staggered break gives more than the existence of the
reflected second monomial.  Its missing diagonal vanishes at every parameter
order strictly below `2*J-q`.  Since a source monomial with missing-coordinate
exponent at least two makes the corresponding second derivative nonzero, this
identifies `K = 2*J-q` as the *least* total-deficit order at which exponent
two can occur.

The literal locked/highest endpoints then bound this second opening by the
same finite staircase endpoint.  This is the induction-ready strengthening of
the reflected packet; no new clock or repair state is introduced.
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

/-- Source-facing statement that the exact reflected order `K = 2*J-q` is
the first possible layer carrying missing-coordinate exponent at least two. -/
inductive FirstDeficitSecondMissingOpeningData : Prop
  | left
      (first opposite : Fin 4 →₀ ℕ)
      (q J Kord : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (J_eq : J = opposite 1 + opposite 2)
      (K_eq : Kord = 2 * J - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = q)
      (first_two : first 2 = 0)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (q_lt_J : q < J)
      (first_missing_minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 → J ≤ f 1 + f 2)
      (second_missing_minimal :
        ∀ f ∈ P.carrier.support, 2 ≤ f 2 → Kord ≤ f 1 + f 2)
      (K_le_locked : Kord ≤ F.locked.ell)
  | right
      (first opposite : Fin 4 →₀ ℕ)
      (q J Kord : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (J_eq : J = opposite 1 + opposite 2)
      (K_eq : Kord = 2 * J - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = q)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (q_lt_J : q < J)
      (first_missing_minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 → J ≤ f 1 + f 2)
      (second_missing_minimal :
        ∀ f ∈ P.carrier.support, 2 ≤ f 1 → Kord ≤ f 1 + f 2)
      (K_le_highest : Kord ≤ F.highest.n - 1)

/-- The generic staggered kernel gap is exactly the missing-coordinate
minimality statement at the source level. -/
theorem firstDeficit_secondMissingOpening
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitSecondMissingOpeningData := by
  let O := G.firstDeficit_secondInteractionGeometry hthree houtThree
  cases O with
  | left first opposite B hfirst hfirst1 hfirst2 huniq hop hop2
      hstrict hminimal hB hlayer hmixed hsecond heq =>
      let q := G.firstDeficitOrder
      let J := opposite 1 + opposite 2
      let Kord := 2 * J - q
      rcases G.exists_leftStaggeredBreakData
          hthree houtThree
          hfirst hfirst1 hfirst2 huniq
          hop (by omega) hstrict hminimal with
        ⟨E, hblock, hactive, hkernel⟩
      have hmin2 :
          ∀ f ∈ P.carrier.support, 2 ≤ f 2 →
            Kord ≤ f 1 + f 2 := by
        intro f hf hf2
        let s := f 1 + f 2
        by_contra hnot
        have hslt : s < Kord := Nat.lt_of_not_ge hnot
        have hzE :
            E.block.z.coeff s = 0 := by
          apply E.kernelDiagonal_coeff_eq_zero_before_secondInteraction
          rw [hactive, hkernel]
          simpa [q, J, Kord, s] using hslt
        have hz :
            (parameterFirstHessian P.centralDeficitFamily
              (2 : Fin 4) 2).coeff s = 0 := by
          rw [hblock] at hzE
          simpa [firstDeficitLeftStaggeredBlock,
            firstDeficitLeftStaggeredMatrix,
            GeneralFourBlock.ofSymmetricMatrix] using hzE
        have hfLayer :
            f ∈ (familyParameterLayer P.centralDeficitFamily s).support := by
          rw [P.centralDeficitFamily_layer_mem_iff]
          exact ⟨hf, rfl⟩
        have hderiv :
            MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily s)) ≠ 0 :=
          pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (2 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily s)
            f hfLayer hf2
        have hcoeff :
            (parameterFirstHessian P.centralDeficitFamily
              (2 : Fin 4) 2).coeff s ≠ 0 := by
          rw [parameterFirstHessian_coeff]
          simpa [HC4.Polynomial.hessian_apply] using hderiv
        exact hcoeff hz
      rcases F.locked_yRoof_mem with
        ⟨hlocked, _hlocked0, hlocked1, hlocked2, _hlocked3⟩
      have hJle : J ≤ F.locked.ell := by
        have h := hminimal C.ray.outsideExponent hlocked
          (by rw [hlocked2]; exact F.locked.ell_pos)
        dsimp [J]
        rw [hlocked1, hlocked2] at h
        simpa using h
      have hqTwo : 2 ≤ q := by
        dsimp [q]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hellTwo : 2 ≤ F.locked.ell := by
        have hqJ : q < J := by
          simpa [q, J] using hstrict
        omega
      have hKle : Kord ≤ F.locked.ell := by
        have h := hmin2 C.ray.outsideExponent hlocked
          (by simpa [hlocked2] using hellTwo)
        rw [hlocked1, hlocked2] at h
        simpa using h
      exact .left first opposite q J Kord
        rfl rfl rfl hfirst
        (by simpa [q] using hfirst1) hfirst2
        hop hop2
        (by simpa [q, J] using hstrict)
        (by
          intro f hf hfpos
          simpa [J] using hminimal f hf hfpos)
        hmin2 hKle

  | right first opposite B hfirst hfirst1 hfirst2 huniq hop hop1
      hstrict hminimal hB hlayer hmixed hsecond heq =>
      let q := G.firstDeficitOrder
      let J := opposite 1 + opposite 2
      let Kord := 2 * J - q
      rcases G.exists_rightStaggeredBreakData
          hthree houtThree
          hfirst hfirst1 hfirst2 huniq
          hop (by omega) hstrict hminimal with
        ⟨E, hblock, hactive, hkernel⟩
      have hmin2 :
          ∀ f ∈ P.carrier.support, 2 ≤ f 1 →
            Kord ≤ f 1 + f 2 := by
        intro f hf hf1
        let s := f 1 + f 2
        by_contra hnot
        have hslt : s < Kord := Nat.lt_of_not_ge hnot
        have hzE :
            E.block.z.coeff s = 0 := by
          apply E.kernelDiagonal_coeff_eq_zero_before_secondInteraction
          rw [hactive, hkernel]
          simpa [q, J, Kord, s] using hslt
        have hz :
            (parameterFirstHessian P.centralDeficitFamily
              (1 : Fin 4) 1).coeff s = 0 := by
          rw [hblock] at hzE
          simpa [firstDeficitRightStaggeredBlock,
            firstDeficitRightStaggeredMatrix,
            GeneralFourBlock.ofSymmetricMatrix] using hzE
        have hfLayer :
            f ∈ (familyParameterLayer P.centralDeficitFamily s).support := by
          rw [P.centralDeficitFamily_layer_mem_iff]
          exact ⟨hf, rfl⟩
        have hderiv :
            MvPolynomial.pderiv (1 : Fin 4)
              (MvPolynomial.pderiv (1 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily s)) ≠ 0 :=
          pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (1 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily s)
            f hfLayer hf1
        have hcoeff :
            (parameterFirstHessian P.centralDeficitFamily
              (1 : Fin 4) 1).coeff s ≠ 0 := by
          rw [parameterFirstHessian_coeff]
          simpa [HC4.Polynomial.hessian_apply] using hderiv
        exact hcoeff hz
      rcases F.highest_zRoof_mem with
        ⟨hhigh, _hhigh0, hhigh1, hhigh2, _hhigh3⟩
      have hJle : J ≤ F.highest.n - 1 := by
        have hhighPos : 0 < F.highest.e1 1 := by
          have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
          rw [hhigh1]
          omega
        have h := hminimal F.highest.e1 hhigh hhighPos
        dsimp [J]
        rw [hhigh1, hhigh2] at h
        simpa using h
      have hqTwo : 2 ≤ q := by
        dsimp [q]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hhighTwo : 2 ≤ F.highest.n - 1 := by
        have hqJ : q < J := by
          simpa [q, J] using hstrict
        omega
      have hKle : Kord ≤ F.highest.n - 1 := by
        have h := hmin2 F.highest.e1 hhigh
          (by simpa [hhigh1] using hhighTwo)
        rw [hhigh1, hhigh2] at h
        simpa using h
      exact .right first opposite q J Kord
        rfl rfl rfl hfirst hfirst1
        (by simpa [q] using hfirst2)
        hop hop1
        (by simpa [q, J] using hstrict)
        (by
          intro f hf hfpos
          simpa [J] using hminimal f hf hfpos)
        hmin2 hKle

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
