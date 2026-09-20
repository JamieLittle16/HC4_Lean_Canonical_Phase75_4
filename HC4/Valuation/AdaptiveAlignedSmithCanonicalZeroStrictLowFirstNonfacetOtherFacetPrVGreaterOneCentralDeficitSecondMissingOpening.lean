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
      (second : Fin 4 →₀ ℕ)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = Kord)
      (second_two : second 2 = 2)
      (second_missing_unique :
        ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → 2 ≤ f 2 →
          f = second)
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
      (second : Fin 4 →₀ ℕ)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = Kord)
      (second_one : second 1 = 2)
      (second_missing_unique :
        ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → 2 ≤ f 1 →
          f = second)
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
      have hqTwo : 2 ≤ q := by
        dsimp [q]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hfirstKernel :
          MvPolynomial.pderiv (2 : Fin 4) G.firstDeficitLayer = 0 := by
        apply pderiv_eq_zero_of_all_supported_exponents_zero
        intro d hd
        rw [huniq d (MvPolynomial.mem_support_iff.mpr hd), hfirst2]
      have hA0 :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1) = 0 := by
        exact pderiv_hessian_diag_eq_zero_of_pderiv_eq_zero
          (K := K) (2 : Fin 4) (1 : Fin 4)
          G.firstDeficitLayer hfirstKernel
      have hLayerJ :
          familyParameterLayer P.centralDeficitFamily J =
            MvPolynomial.monomial opposite B := by
        simpa [J] using hlayer
      have hOppSecond :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily J)) = 0 := by
        rw [hLayerJ]
        exact pderiv_pderiv_monomial_eq_zero_of_exponent_eq_one
          (K := K) (2 : Fin 4) opposite B hop2
      have hS0 :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily J)
              (1 : Fin 4) 2) = 0 := by
        exact pderiv_hessian_mixed_eq_zero_of_second_pderiv_eq_zero
          (K := K) (2 : Fin 4) (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily J) hOppSecond
      have hAne :
          HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1 ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (1 : Fin 4) G.firstDeficitLayer first
            hfirst (by
              rw [hfirst1]
              simpa [q] using hqTwo))
      have hidentity :
          HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily Kord)
                (2 : Fin 4) 2 =
            HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily J)
                (1 : Fin 4) 2 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily J)
                (1 : Fin 4) 2 := by
        simpa [q, J, Kord] using heq
      have hthirdHessian :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily Kord)
              (2 : Fin 4) 2) = 0 := by
        exact pderiv_right_eq_zero_of_mul_eq_square
          (K := K) (2 : Fin 4)
          (HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily Kord)
            (2 : Fin 4) 2)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily J)
            (1 : Fin 4) 2)
          hidentity hA0 hS0 hAne
      have hthird :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily Kord))) = 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using hthirdHessian
      have hcap :
          ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → f 2 ≤ 2 := by
        intro f hf horder
        have hfLayer :
            f ∈ (familyParameterLayer P.centralDeficitFamily Kord).support := by
          rw [P.centralDeficitFamily_layer_mem_iff]
          exact ⟨hf, horder⟩
        by_contra hnot
        have hf3 : 3 ≤ f 2 := by omega
        exact
          (pderiv_pderiv_pderiv_ne_zero_of_support_exponent_ge_three
            (K := K) (2 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily Kord)
            f hfLayer hf3) hthird
      have hsecondDeriv :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily Kord)) ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (show
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily Kord)
              (2 : Fin 4) 2 ≠ 0 by
            simpa [q, J, Kord] using hsecond)
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily Kord) hsecondDeriv with
        ⟨secondExp, hsecondLayer, hsecondTwoGe⟩
      have hsecondSource :=
        (P.centralDeficitFamily_layer_mem_iff Kord secondExp).1 hsecondLayer
      have hsecondTwoLe :
          secondExp 2 ≤ 2 :=
        hcap secondExp hsecondSource.1 hsecondSource.2
      have hsecondTwo : secondExp 2 = 2 :=
        Nat.le_antisymm hsecondTwoLe hsecondTwoGe
      have hsecondUnique :
          ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → 2 ≤ f 2 →
            f = secondExp := by
        intro f hf horder hfTwoGe
        have hfTwoLe := hcap f hf horder
        have hfTwo : f 2 = 2 := Nat.le_antisymm hfTwoLe hfTwoGe
        have hfOne : f 1 = secondExp 1 := by
          omega
        have hfTwoEq : f 2 = secondExp 2 := by
          rw [hfTwo, hsecondTwo]
        exact F.support_eq_of_deficits_eq
          hthree houtThree hf hsecondSource.1 hfOne hfTwoEq
      rcases F.locked_yRoof_mem with
        ⟨hlocked, _hlocked0, hlocked1, hlocked2, _hlocked3⟩
      have hJle : J ≤ F.locked.ell := by
        have h := hminimal C.ray.outsideExponent hlocked
          (by rw [hlocked2]; exact F.locked.ell_pos)
        dsimp [J]
        rw [hlocked1, hlocked2] at h
        simpa using h
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
        hmin2 secondExp hsecondSource.1 hsecondSource.2
        hsecondTwo hsecondUnique hKle

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
      have hqTwo : 2 ≤ q := by
        dsimp [q]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hfirstKernel :
          MvPolynomial.pderiv (1 : Fin 4) G.firstDeficitLayer = 0 := by
        apply pderiv_eq_zero_of_all_supported_exponents_zero
        intro d hd
        rw [huniq d (MvPolynomial.mem_support_iff.mpr hd), hfirst1]
      have hA0 :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2) = 0 := by
        exact pderiv_hessian_diag_eq_zero_of_pderiv_eq_zero
          (K := K) (1 : Fin 4) (2 : Fin 4)
          G.firstDeficitLayer hfirstKernel
      have hLayerJ :
          familyParameterLayer P.centralDeficitFamily J =
            MvPolynomial.monomial opposite B := by
        simpa [J] using hlayer
      have hOppSecond :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily J)) = 0 := by
        rw [hLayerJ]
        exact pderiv_pderiv_monomial_eq_zero_of_exponent_eq_one
          (K := K) (1 : Fin 4) opposite B hop1
      have hS0 :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily J)
              (2 : Fin 4) 1) = 0 := by
        exact pderiv_hessian_mixed_eq_zero_of_second_pderiv_eq_zero
          (K := K) (1 : Fin 4) (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily J) hOppSecond
      have hAne :
          HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2 ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (2 : Fin 4) G.firstDeficitLayer first
            hfirst (by
              rw [hfirst2]
              simpa [q] using hqTwo))
      have hidentity :
          HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily Kord)
                (1 : Fin 4) 1 =
            HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily J)
                (2 : Fin 4) 1 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily J)
                (2 : Fin 4) 1 := by
        simpa [q, J, Kord] using heq
      have hthirdHessian :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily Kord)
              (1 : Fin 4) 1) = 0 := by
        exact pderiv_right_eq_zero_of_mul_eq_square
          (K := K) (1 : Fin 4)
          (HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily Kord)
            (1 : Fin 4) 1)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily J)
            (2 : Fin 4) 1)
          hidentity hA0 hS0 hAne
      have hthird :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (MvPolynomial.pderiv (1 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily Kord))) = 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using hthirdHessian
      have hcap :
          ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → f 1 ≤ 2 := by
        intro f hf horder
        have hfLayer :
            f ∈ (familyParameterLayer P.centralDeficitFamily Kord).support := by
          rw [P.centralDeficitFamily_layer_mem_iff]
          exact ⟨hf, horder⟩
        by_contra hnot
        have hf3 : 3 ≤ f 1 := by omega
        exact
          (pderiv_pderiv_pderiv_ne_zero_of_support_exponent_ge_three
            (K := K) (1 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily Kord)
            f hfLayer hf3) hthird
      have hsecondDeriv :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily Kord)) ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (show
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily Kord)
              (1 : Fin 4) 1 ≠ 0 by
            simpa [q, J, Kord] using hsecond)
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily Kord) hsecondDeriv with
        ⟨secondExp, hsecondLayer, hsecondOneGe⟩
      have hsecondSource :=
        (P.centralDeficitFamily_layer_mem_iff Kord secondExp).1 hsecondLayer
      have hsecondOneLe :
          secondExp 1 ≤ 2 :=
        hcap secondExp hsecondSource.1 hsecondSource.2
      have hsecondOne : secondExp 1 = 2 :=
        Nat.le_antisymm hsecondOneLe hsecondOneGe
      have hsecondUnique :
          ∀ f ∈ P.carrier.support, f 1 + f 2 = Kord → 2 ≤ f 1 →
            f = secondExp := by
        intro f hf horder hfOneGe
        have hfOneLe := hcap f hf horder
        have hfOne : f 1 = 2 := Nat.le_antisymm hfOneLe hfOneGe
        have hfTwo : f 2 = secondExp 2 := by
          omega
        have hfOneEq : f 1 = secondExp 1 := by
          rw [hfOne, hsecondOne]
        exact F.support_eq_of_deficits_eq
          hthree houtThree hf hsecondSource.1 hfOneEq hfTwo
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
        hmin2 secondExp hsecondSource.1 hsecondSource.2
        hsecondOne hsecondUnique hKle

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
