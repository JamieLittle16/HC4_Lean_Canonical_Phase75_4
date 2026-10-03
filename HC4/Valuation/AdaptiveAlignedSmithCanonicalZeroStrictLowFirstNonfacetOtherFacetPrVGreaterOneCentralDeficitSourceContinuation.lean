import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitZeroSchur
import HC4.Newton.RankOneSingularSchurConstantKernel
import HC4.Newton.GeneralFourBlockKernelLift
import HC4.Newton.SingularSchurDiagonalGap
import Mathlib.Tactic

/-!
# Source-safe continuation of the central zero-Schur tail

The normalized central Schur tail has a nonzero determinant-zero constant
block.  The generic binary dispatcher now gives exactly two outcomes.

* **Stationary:** pull the aligned stationary kernel back to the raw binary
  Schur coordinates.  Restoring the common first parameter factor gives a
  cleared Schur kernel of the original complete central four-block.  The
  generic denominator-cleared lift then gives an honest four-coordinate
  polynomial kernel equation for that original Hessian block.
* **Reflected:** retain the aligned first transverse order `j`, its nonzero
  off-diagonal coefficient, and the forced nonzero kernel coefficient at
  `2*j`.

The alignment is used only inside the generic binary algebra.  It is never
declared to be a source-coordinate transformation.
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

/-- The active `(0,3)` determinant of the complete central block is
nonzero as a polynomial series.  Its constant coefficient is exactly the
retained nonzero principal minor of the honest coordinate-max central face. -/
theorem centralDeficitSchurBlock_activeDet_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.activeDet ≠ 0 := by
  have hlayer0 :
      familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
    calc
      familyParameterLayer P.centralDeficitFamily 0 =
          MvPolynomial.monomial G.central
            (MvPolynomial.coeff G.central P.carrier) :=
        G.centralDeficitFamily_layer_zero_eq hthree houtThree
      _ = G.exposure.face := G.exposure_face_eq.symm
  have hcoeff :
      G.centralDeficitSchurBlock.activeDet.coeff 0 ≠ 0 := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    unfold GeneralFourBlock.activeDet
    rw [permutedFamilyHessianFourBlock_a,
      permutedFamilyHessianFourBlock_b,
      permutedFamilyHessianFourBlock_d]
    simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
    rw [centralDeficitActiveDet_coeff_zero_eq]
    rw [hlayer0]
    exact G.exposure_rankTwo_minor
  intro hzero
  rw [hzero] at hcoeff
  simp at hcoeff


/-- The retained active `(0,3)` minor is already nonzero in the special
fibre.  Exposing the coefficient, rather than only polynomial nonvanishing,
lets later Schur coefficient calculations stay purely multiplicative. -/
theorem centralDeficitSchurBlock_activeDet_coeff_zero_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.activeDet.coeff 0 ≠ 0 := by
  have hlayer0 :
      familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
    calc
      familyParameterLayer P.centralDeficitFamily 0 =
          MvPolynomial.monomial G.central
            (MvPolynomial.coeff G.central P.carrier) :=
        G.centralDeficitFamily_layer_zero_eq hthree houtThree
      _ = G.exposure.face := G.exposure_face_eq.symm
  unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
  unfold GeneralFourBlock.activeDet
  rw [permutedFamilyHessianFourBlock_a,
    permutedFamilyHessianFourBlock_b,
    permutedFamilyHessianFourBlock_d]
  simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
  rw [centralDeficitActiveDet_coeff_zero_eq]
  rw [hlayer0]
  exact G.exposure_rankTwo_minor

/-- **The first opposite source opening is exactly the first raw Schur
off-diagonal opening.**

If the missing source coordinate is `2`, then the central Schur fields
`p,r,y` vanish below the least opposite opening `J`; if the missing
coordinate is `1`, the mirror fields `q,s,y` do.  The special fibre has
all four cross entries zero.  The generic Schur coefficient helper therefore
reduces the coefficient at every order below `J` to zero and the coefficient
at `J` to the nonzero active minor times the honest mixed Hessian opening.

This is the source/algebra bridge needed before alignment: no Schur
congruence is interpreted as a source-coordinate transformation. -/
theorem centralDeficitSchurB_firstOppositeOpening_of_interaction
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (O : G.FirstDeficitSecondInteractionGeometry) :
    let H := G.centralDeficitSchurBlock
    ∃ J : ℕ,
      G.firstDeficitOrder < J ∧
      (∀ n : ℕ, n < J → H.schurB.coeff n = 0) ∧
      H.schurB.coeff J ≠ 0 := by
  let H := G.centralDeficitSchurBlock
  have hactive0 : H.activeDet.coeff 0 ≠ 0 := by
    simpa [H] using
      G.centralDeficitSchurBlock_activeDet_coeff_zero_ne_zero
        hthree houtThree
  cases O with
  | left first opposite B hfirst hfirst1 hfirst2 huniq hop hop2
        hstrict hminimal hB hlayer hmixed hsecond heq =>
      let J := opposite 1 + opposite 2
      have hp :
          ∀ n : ℕ, n < J → H.p.coeff n = 0 := by
        intro n hn
        rw [show H.p =
            parameterFirstHessian P.centralDeficitFamily (0 : Fin 4) 2 by
          simpa [H] using G.centralDeficitSchurBlock_p]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (0 : Fin 4) 2]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (2 : Fin 4) J hminimal hn 0
      have hr :
          ∀ n : ℕ, n < J → H.r.coeff n = 0 := by
        intro n hn
        rw [show H.r =
            parameterFirstHessian P.centralDeficitFamily (3 : Fin 4) 2 by
          simpa [H] using G.centralDeficitSchurBlock_r]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (3 : Fin 4) 2]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (2 : Fin 4) J hminimal hn 3
      have hy :
          ∀ n : ℕ, n < J → H.y.coeff n = 0 := by
        intro n hn
        rw [show H.y =
            parameterFirstHessian P.centralDeficitFamily (2 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_y]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (2 : Fin 4) J hminimal hn 1
      have hq0 : H.q.coeff 0 = 0 := by
        simpa [H] using G.centralDeficit_q_coeff_zero hthree houtThree
      have hs0 : H.s.coeff 0 = 0 := by
        simpa [H] using G.centralDeficit_s_coeff_zero hthree houtThree
      have hyJ : H.y.coeff J ≠ 0 := by
        rw [show H.y =
            parameterFirstHessian P.centralDeficitFamily (2 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_y]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (2 : Fin 4) 1]
        rw [parameterFirstHessian_coeff]
        simpa [J] using hmixed
      have hgap : ∀ n : ℕ, n < J → H.schurB.coeff n = 0 := by
        intro n hn
        have hform :=
          GeneralFourBlock.schurB_coeff_eq_activeDet_zero_mul_y_of_left_gap
            H
            (fun m hm => hp m (lt_trans hm hn))
            (fun m hm => hr m (lt_trans hm hn))
            (fun m hm => hy m (lt_trans hm hn))
            hq0 hs0
        rw [hform, hy n hn]
        simp
      have hopen : H.schurB.coeff J ≠ 0 := by
        rw [GeneralFourBlock.schurB_coeff_eq_activeDet_zero_mul_y_of_left_gap
          H hp hr hy hq0 hs0]
        exact mul_ne_zero hactive0 hyJ
      exact ⟨J, by simpa [J] using hstrict, hgap, hopen⟩
  | right first opposite B hfirst hfirst1 hfirst2 huniq hop hop1
        hstrict hminimal hB hlayer hmixed hsecond heq =>
      let J := opposite 1 + opposite 2
      have hq :
          ∀ n : ℕ, n < J → H.q.coeff n = 0 := by
        intro n hn
        rw [show H.q =
            parameterFirstHessian P.centralDeficitFamily (0 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_q]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (0 : Fin 4) 1]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (1 : Fin 4) J hminimal hn 0
      have hs :
          ∀ n : ℕ, n < J → H.s.coeff n = 0 := by
        intro n hn
        rw [show H.s =
            parameterFirstHessian P.centralDeficitFamily (3 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_s]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (3 : Fin 4) 1]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (1 : Fin 4) J hminimal hn 3
      have hy :
          ∀ n : ℕ, n < J → H.y.coeff n = 0 := by
        intro n hn
        rw [show H.y =
            parameterFirstHessian P.centralDeficitFamily (2 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_y]
        rw [parameterFirstHessian_symmetric
          P.centralDeficitFamily (2 : Fin 4) 1]
        exact missingHessianRow_coeff_eq_zero_of_lt (P := P)
          (1 : Fin 4) J hminimal hn 2
      have hp0 : H.p.coeff 0 = 0 := by
        simpa [H] using G.centralDeficit_p_coeff_zero hthree houtThree
      have hr0 : H.r.coeff 0 = 0 := by
        simpa [H] using G.centralDeficit_r_coeff_zero hthree houtThree
      have hyJ : H.y.coeff J ≠ 0 := by
        rw [show H.y =
            parameterFirstHessian P.centralDeficitFamily (2 : Fin 4) 1 by
          simpa [H] using G.centralDeficitSchurBlock_y]
        rw [parameterFirstHessian_coeff]
        simpa [J] using hmixed
      have hgap : ∀ n : ℕ, n < J → H.schurB.coeff n = 0 := by
        intro n hn
        have hform :=
          GeneralFourBlock.schurB_coeff_eq_activeDet_zero_mul_y_of_right_gap
            H
            (fun m hm => hq m (lt_trans hm hn))
            (fun m hm => hs m (lt_trans hm hn))
            (fun m hm => hy m (lt_trans hm hn))
            hp0 hr0
        rw [hform, hy n hn]
        simp
      have hopen : H.schurB.coeff J ≠ 0 := by
        rw [GeneralFourBlock.schurB_coeff_eq_activeDet_zero_mul_y_of_right_gap
          H hq hs hy hp0 hr0]
        exact mul_ne_zero hactive0 hyJ
      exact ⟨J, by simpa [J] using hstrict, hgap, hopen⟩


/-- Public wrapper selecting the canonical source interaction before exposing
the first raw Schur off-diagonal opening. -/
theorem centralDeficitSchurB_firstOppositeOpening
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := G.centralDeficitSchurBlock
    ∃ J : ℕ,
      G.firstDeficitOrder < J ∧
      (∀ n : ℕ, n < J → H.schurB.coeff n = 0) ∧
      H.schurB.coeff J ≠ 0 :=
  G.centralDeficitSchurB_firstOppositeOpening_of_interaction
    hthree houtThree
    (G.firstDeficit_secondInteractionGeometry hthree houtThree)

/-- **The aligned central tail first moves at the honest source gap `J-q`.**

The raw Schur off-diagonal first opens at the least actual opposite source
layer `J`.  Removing the common Schur factor of exact order
`q = firstDeficitOrder` moves this opening to `J-q`.  Both possible
constant rank-one alignments preserve that first opening: the right-axis
alignment leaves the off-diagonal entry unchanged, while in the left-pivot
alignment the raw tail has zero off-diagonal constant term, so the only
remaining factor is the nonzero active pivot scalar.

Thus the abstract first transverse Schur order is no longer anonymous and
the stationary aligned-tail branch is impossible. -/
theorem centralDeficit_alignedTail_firstPositiveTransverseOrder_eq_sourceGap
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    let Q := Z.tailSeries hz
    ∃ (J : ℕ) (A : RankOneSchurSeries (MvPolynomial (Fin 4) K))
        (htrans : A.HasPositiveTransverseLayer),
      G.firstDeficitOrder < J ∧
      A.leading ≠ 0 ∧
      A.determinant = 0 ∧
      ((∃ hleft : Q.LeftPivot, A = Q.alignLeft hleft) ∨
        (∃ hright : Q.RightAxisPivot, A = Q.alignRight hright)) ∧
      A.firstPositiveTransverseOrder htrans =
        J - G.firstDeficitOrder := by
  let H := G.centralDeficitSchurBlock
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let Q := Z.tailSeries hz

  have hraw :
      ∃ J : ℕ,
        G.firstDeficitOrder < J ∧
        (∀ n : ℕ, n < J → H.schurB.coeff n = 0) ∧
        H.schurB.coeff J ≠ 0 := by
    simpa [H] using
      G.centralDeficitSchurB_firstOppositeOpening hthree houtThree
  rcases hraw with ⟨J, hqJ, hrawGap, hrawOpen⟩

  have hfirst :
      Z.firstPositiveEntryOrder hz = G.firstDeficitOrder := by
    simpa [Z, hz] using
      G.centralDeficitZeroSchurSeries_firstPositiveEntryOrder_eq_firstDeficitOrder
        hthree houtThree

  have hrawGapZ :
      ∀ n : ℕ, n < J → Z.series.offDiag.coeff n = 0 := by
    intro n hn
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using hrawGap n hn
  have hrawOpenZ : Z.series.offDiag.coeff J ≠ 0 := by
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using hrawOpen

  rcases Z.tailSeries_offDiag_gap_and_open_at_sub
      hz hfirst hqJ hrawGapZ hrawOpenZ with
    ⟨hQgapRaw, hQopenRaw⟩
  have hQgap :
      ∀ n : ℕ, n < J - G.firstDeficitOrder →
        Q.offDiag.coeff n = 0 := by
    simpa [Q] using hQgapRaw
  have hQopen :
      Q.offDiag.coeff (J - G.firstDeficitOrder) ≠ 0 := by
    simpa [Q] using hQopenRaw
  have hd : 0 < J - G.firstDeficitOrder :=
    Nat.sub_pos_of_lt hqJ
  have hQdet : Q.determinant = 0 := by
    have h :=
      G.centralDeficitZeroSchurTail_determinant_eq_zero
        hthree houtThree
    simpa [Z, hz, Q] using h
  have hpivot : Q.LeftPivot ∨ Q.RightAxisPivot := by
    have h := G.centralDeficitZeroSchurTail_pivot hthree houtThree
    simpa [Z, hz, Q] using h

  rcases Q.exists_aligned_firstPositiveTransverseOrder_eq_of_offDiag_gap_open
      hQdet hpivot hd hQgap hQopen with
    ⟨A, htrans, hlead, hAdet, hprovenance, horder⟩
  exact ⟨J, A, htrans, hqJ, hlead, hAdet, hprovenance, horder⟩

/-- **Exact reflected Schur interaction at the honest source gap.**

The source/alignment bridge already identifies the first positive transverse
order with `J - firstDeficitOrder`.  Since the aligned series is identically
singular with nonzero leading coefficient, the generic rank-one singular
continuation formulas apply directly at that exact order.  In particular
there is no stationary alternative left in this theorem. -/
theorem centralDeficit_exactReflectedInteraction_at_sourceGap
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    let Q := Z.tailSeries hz
    ∃ (J : ℕ) (A : RankOneSchurSeries (MvPolynomial (Fin 4) K))
        (htrans : A.HasPositiveTransverseLayer),
      G.firstDeficitOrder < J ∧
      A.leading ≠ 0 ∧
      A.determinant = 0 ∧
      ((∃ hleft : Q.LeftPivot, A = Q.alignLeft hleft) ∨
        (∃ hright : Q.RightAxisPivot, A = Q.alignRight hright)) ∧
      let j := J - G.firstDeficitOrder
      0 < j ∧
      A.firstPositiveTransverseOrder htrans = j ∧
      A.offDiag.coeff j ≠ 0 ∧
      (∀ n : ℕ, n < 2 * j → A.kernel.coeff n = 0) ∧
      A.leading * A.kernel.coeff (2 * j) =
        A.offDiag.coeff j * A.offDiag.coeff j ∧
      A.kernel.coeff (2 * j) ≠ 0 := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let Q := Z.tailSeries hz
  rcases G.centralDeficit_alignedTail_firstPositiveTransverseOrder_eq_sourceGap
      hthree houtThree with
    ⟨J, A, htrans, hqJ, hlead, hdet, hprov, horder⟩
  let j := J - G.firstDeficitOrder
  have hj : 0 < j := by
    simpa [j] using Nat.sub_pos_of_lt hqJ
  have hoff :
      A.offDiag.coeff j ≠ 0 := by
    have h :=
      A.firstTransverse_offDiag_ne_zero_of_determinant_eq_zero
        hlead hdet htrans
    rw [horder] at h
    simpa [j] using h
  have hkernelLower :
      ∀ n : ℕ, n < 2 * j → A.kernel.coeff n = 0 := by
    intro n hn
    apply A.kernel_coeff_eq_zero_before_twice_firstTransverse
      hlead hdet htrans n
    rw [horder]
    simpa [j] using hn
  have hid :
      A.leading * A.kernel.coeff (2 * j) =
        A.offDiag.coeff j * A.offDiag.coeff j := by
    have h :=
      A.kernel_coeff_twice_firstTransverse_identity hlead hdet htrans
    rw [horder] at h
    simpa [j] using h
  have hkernel :
      A.kernel.coeff (2 * j) ≠ 0 := by
    have h :=
      A.kernel_coeff_twice_firstTransverse_ne_zero hlead hdet htrans
    rw [horder] at h
    simpa [j] using h
  refine ⟨J, A, htrans, hqJ, hlead, hdet, ?_, ?_⟩
  · simpa [Q, Z, hz] using hprov
  · dsimp [j]
    exact ⟨hj, by simpa [j] using horder, hoff, hkernelLower, hid, hkernel⟩


/-- **Raw-kernel or reflected continuation of the central total-deficit
family.**

The stationary branch is stated entirely in the raw source-honest central
four-block.  In particular the returned binary kernel coordinates are
polynomials in the source variables but are constant in the Rees parameter.
-/
theorem centralDeficit_rawKernel_or_reflectedInteraction
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := G.centralDeficitSchurBlock
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    let Q := Z.tailSeries hz
    (∃ u v : MvPolynomial (Fin 4) K,
        (u ≠ 0 ∨ v ≠ 0) ∧
        H.IsClearedSchurKernel (Polynomial.C u) (Polynomial.C v) ∧
        H.clearedKernelLift (Polynomial.C u) (Polynomial.C v) ≠ 0 ∧
        H.matrix.mulVec
          (H.clearedKernelLift (Polynomial.C u) (Polynomial.C v)) = 0) ∨
      ∃ A : RankOneSchurSeries (MvPolynomial (Fin 4) K),
        A.leading ≠ 0 ∧
        A.determinant = 0 ∧
        ((∃ hleft : Q.LeftPivot, A = Q.alignLeft hleft) ∨
          (∃ hright : Q.RightAxisPivot, A = Q.alignRight hright)) ∧
        ∃ j : ℕ,
          0 < j ∧
          A.offDiag.coeff j ≠ 0 ∧
          (∀ n : ℕ, n < 2 * j → A.kernel.coeff n = 0) ∧
          A.leading * A.kernel.coeff (2 * j) =
            A.offDiag.coeff j * A.offDiag.coeff j ∧
          A.kernel.coeff (2 * j) ≠ 0 := by
  let H := G.centralDeficitSchurBlock
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let Q := Z.tailSeries hz

  have hQdet : Q.determinant = 0 := by
    have h :=
      G.centralDeficitZeroSchurTail_determinant_eq_zero
        hthree houtThree
    simpa [Z, hz, Q] using h

  have hpivot : Q.LeftPivot ∨ Q.RightAxisPivot := by
    have h := G.centralDeficitZeroSchurTail_pivot hthree houtThree
    simpa [Z, hz, Q] using h

  rcases Q.constantKernel_or_reflectedInteraction hQdet hpivot with
    hconstant | hreflected
  · left
    rcases hconstant with ⟨u, v, huv, hrawA, hrawB⟩
    have hfactorA := Z.active_eq_firstFactor_mul_tail hz
    have hfactorB := Z.offDiag_eq_firstFactor_mul_tail hz
    have hfactorC := Z.kernel_eq_firstFactor_mul_tail hz
    have hA :
        H.schurA =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.active := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorA
    have hB :
        H.schurB =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorB
    have hC :
        H.schurC =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.kernel := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorC
    have hker :
        H.IsClearedSchurKernel (Polynomial.C u) (Polynomial.C v) := by
      unfold GeneralFourBlock.IsClearedSchurKernel
      constructor
      · rw [hA, hB]
        calc
          (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.active) *
                Polynomial.C u +
              (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag) *
                Polynomial.C v =
            Polynomial.X ^ Z.firstPositiveEntryOrder hz *
              (Q.active * Polynomial.C u +
                Q.offDiag * Polynomial.C v) := by ring
          _ = 0 := by rw [hrawA]; simp
      · rw [hB, hC]
        calc
          (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag) *
                Polynomial.C u +
              (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.kernel) *
                Polynomial.C v =
            Polynomial.X ^ Z.firstPositiveEntryOrder hz *
              (Q.offDiag * Polynomial.C u +
                Q.kernel * Polynomial.C v) := by ring
          _ = 0 := by rw [hrawB]; simp
    have hactive : H.activeDet ≠ 0 := by
      simpa [H] using
        G.centralDeficitSchurBlock_activeDet_ne_zero hthree houtThree
    have huvC :
        Polynomial.C u ≠ 0 ∨ Polynomial.C v ≠ 0 := by
      rcases huv with hu | hv
      · exact Or.inl (Polynomial.C_ne_zero.mpr hu)
      · exact Or.inr (Polynomial.C_ne_zero.mpr hv)
    have hlift :
        H.clearedKernelLift (Polynomial.C u) (Polynomial.C v) ≠ 0 :=
      H.clearedKernelLift_ne_zero_of_activeDet_ne_zero
        (Polynomial.C u) (Polynomial.C v) hactive huvC
    refine ⟨u, v, ?_⟩
    constructor
    · exact huv
    constructor
    · exact hker
    constructor
    · exact hlift
    · exact H.mulVec_clearedKernelLift_eq_zero
        (Polynomial.C u) (Polynomial.C v) hker
  · exact Or.inr hreflected

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
