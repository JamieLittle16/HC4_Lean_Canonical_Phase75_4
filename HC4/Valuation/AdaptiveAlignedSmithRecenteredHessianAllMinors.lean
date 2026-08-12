import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianRankOneRelations
import Mathlib.Tactic

/-!
# All 2×2 minors of the recentered blocker Hessian

The previous green module leaves a completely division-free permutation
family of principal and three-index rank-one relations on the constant
recentered Hessian.

This file closes the small linear-algebra seam between those relations and an
honest rank-at-most-one determinantal certificate.

The key point is that we never divide in the polynomial coefficient ring.
For a symmetric four-block, a short list of principal/cross relations gives a
factorisation through any nonzero diagonal pivot.  If that pivot vanishes,
the same principal relations kill its entire row/column and we pass to the
next diagonal entry.  Therefore every 2×2 minor vanishes.

The adaptive part then uses the fact that the rank-one relations hold for
*every* coordinate permutation to manufacture exactly the finite list needed
by the generic theorem.

No JC2 input occurs here.
-/

namespace HC4.Newton

noncomputable section

universe v

variable {R : Type v} [CommRing R]

namespace GeneralFourBlock

/-- Every `2 × 2` minor of the displayed symmetric matrix vanishes.  This is
our division-free rank-at-most-one certificate over a domain. -/
def AllTwoByTwoMinorsZero (H : GeneralFourBlock R) : Prop :=
  ∀ i j k l : Fin 4,
    H.matrix i j * H.matrix k l -
      H.matrix i l * H.matrix k j = 0

/-- If all entries factor through a nonzero diagonal pivot, every `2 × 2`
minor vanishes.  The proof deliberately cancels only after multiplying by the
square of the pivot, so it works over an arbitrary domain. -/
theorem allTwoByTwoMinorsZero_of_centerFactor
    [IsDomain R]
    (H : GeneralFourBlock R)
    (c : Fin 4)
    (hc : H.matrix c c ≠ 0)
    (hfactor : ∀ i j : Fin 4,
      H.matrix i j * H.matrix c c =
        H.matrix i c * H.matrix c j) :
    H.AllTwoByTwoMinorsZero := by
  intro i j k l
  let cc := H.matrix c c
  have hcc : cc ≠ 0 := by
    simpa [cc] using hc
  have hcc2 : cc * cc ≠ 0 := mul_ne_zero hcc hcc
  have hmul :
      (H.matrix i j * H.matrix k l -
          H.matrix i l * H.matrix k j) * (cc * cc) = 0 := by
    calc
      (H.matrix i j * H.matrix k l -
          H.matrix i l * H.matrix k j) * (cc * cc) =
          (H.matrix i j * cc) * (H.matrix k l * cc) -
            (H.matrix i l * cc) * (H.matrix k j * cc) := by
              ring
      _ =
          (H.matrix i c * H.matrix c j) *
              (H.matrix k c * H.matrix c l) -
            (H.matrix i c * H.matrix c l) *
              (H.matrix k c * H.matrix c j) := by
              rw [hfactor i j, hfactor k l, hfactor i l, hfactor k j]
      _ = 0 := by ring
  exact (mul_eq_zero.mp hmul).resolve_right hcc2

/-- A finite division-free relation package sufficient for all `2 × 2`
minors of a symmetric four-block to vanish.

The first six relations are the six principal `2 × 2` minors.  The next
three are the cross relations through the displayed diagonal pivot `d`; the
last relation is the cross relation needed after falling back to pivot `a`.
This is exactly the information produced from the permutation family in the
adaptive application below. -/
structure HasRankOneCoreRelations (H : GeneralFourBlock R) : Prop where
  principal01 : H.a * H.d - H.b * H.b = 0
  principal02 : H.a * H.x - H.p * H.p = 0
  principal03 : H.a * H.z - H.q * H.q = 0
  principal12 : H.x * H.d - H.r * H.r = 0
  principal13 : H.z * H.d - H.s * H.s = 0
  principal23 : H.x * H.z - H.y * H.y = 0
  cross012 : H.p * H.d - H.b * H.r = 0
  cross013 : H.q * H.d - H.b * H.s = 0
  cross213 : H.y * H.d - H.r * H.s = 0
  cross203 : H.y * H.a - H.p * H.q = 0

/-- The finite core relations imply vanishing of every `2 × 2` minor.

The proof is a pivot-free descent:

* if `d ≠ 0`, all entries factor through row/column `1`;
* if `d = 0`, the principal relations force `b=r=s=0`;
* if then `a ≠ 0`, all remaining entries factor through row/column `0`;
* if also `a = 0`, then `p=q=0`; use `x` as the final possible pivot;
* if `x = 0`, the last principal relation gives `y=0`, so only `z` can
  remain and the conclusion is immediate.
-/
theorem allTwoByTwoMinorsZero_of_rankOneCoreRelations
    [IsDomain R]
    (H : GeneralFourBlock R)
    (h : H.HasRankOneCoreRelations) :
    H.AllTwoByTwoMinorsZero := by
  have h01 : H.a * H.d = H.b * H.b := sub_eq_zero.mp h.principal01
  have h02 : H.a * H.x = H.p * H.p := sub_eq_zero.mp h.principal02
  have h03 : H.a * H.z = H.q * H.q := sub_eq_zero.mp h.principal03
  have h12 : H.x * H.d = H.r * H.r := sub_eq_zero.mp h.principal12
  have h13 : H.z * H.d = H.s * H.s := sub_eq_zero.mp h.principal13
  have h23 : H.x * H.z = H.y * H.y := sub_eq_zero.mp h.principal23
  have hc012 : H.p * H.d = H.b * H.r := sub_eq_zero.mp h.cross012
  have hc013 : H.q * H.d = H.b * H.s := sub_eq_zero.mp h.cross013
  have hc213 : H.y * H.d = H.r * H.s := sub_eq_zero.mp h.cross213
  have hc203 : H.y * H.a = H.p * H.q := sub_eq_zero.mp h.cross203

  by_cases hd : H.d = 0
  · have hb2 : H.b * H.b = 0 := by simpa [hd] using h01.symm
    have hr2 : H.r * H.r = 0 := by simpa [hd] using h12.symm
    have hs2 : H.s * H.s = 0 := by simpa [hd] using h13.symm
    have hb : H.b = 0 := by
      rcases mul_eq_zero.mp hb2 with hb | hb <;> exact hb
    have hr : H.r = 0 := by
      rcases mul_eq_zero.mp hr2 with hr | hr <;> exact hr
    have hs : H.s = 0 := by
      rcases mul_eq_zero.mp hs2 with hs | hs <;> exact hs

    by_cases ha : H.a = 0
    · have hp2 : H.p * H.p = 0 := by simpa [ha] using h02.symm
      have hq2 : H.q * H.q = 0 := by simpa [ha] using h03.symm
      have hp : H.p = 0 := by
        rcases mul_eq_zero.mp hp2 with hp | hp <;> exact hp
      have hq : H.q = 0 := by
        rcases mul_eq_zero.mp hq2 with hq | hq <;> exact hq

      by_cases hx : H.x = 0
      · have hy2 : H.y * H.y = 0 := by simpa [hx] using h23.symm
        have hy : H.y = 0 := by
          rcases mul_eq_zero.mp hy2 with hy | hy <;> exact hy
        intro i j k l
        fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
          simp [GeneralFourBlock.matrix, hd, ha, hx, hb, hr, hs, hp, hq, hy]
      · have hfactor : ∀ i j : Fin 4,
            H.matrix i j * H.matrix (2 : Fin 4) 2 =
              H.matrix i 2 * H.matrix 2 j := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [GeneralFourBlock.matrix, hd, ha, hb, hr, hs, hp, hq,
              h23, mul_comm, mul_left_comm, mul_assoc]
        exact H.allTwoByTwoMinorsZero_of_centerFactor 2
          (by simpa [GeneralFourBlock.matrix] using hx) hfactor

    · have hfactor : ∀ i j : Fin 4,
          H.matrix i j * H.matrix (0 : Fin 4) 0 =
            H.matrix i 0 * H.matrix 0 j := by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [GeneralFourBlock.matrix, hd, hb, hr, hs,
            h02, h03, hc203, mul_comm, mul_left_comm, mul_assoc]
      exact H.allTwoByTwoMinorsZero_of_centerFactor 0
        (by simpa [GeneralFourBlock.matrix] using ha) hfactor

  · have hfactor : ∀ i j : Fin 4,
        H.matrix i j * H.matrix (1 : Fin 4) 1 =
          H.matrix i 1 * H.matrix 1 j := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralFourBlock.matrix, h01, h12, h13, hc012, hc013, hc213,
          mul_comm, mul_left_comm, mul_assoc]
    exact H.allTwoByTwoMinorsZero_of_centerFactor 1
      (by simpa [GeneralFourBlock.matrix] using hd) hfactor

end GeneralFourBlock

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-! ## Passing the green series relations to the finite special Hessian -/

/-- The existing parameter-series rank-one relations specialize exactly to
the finite right-recentered special-fibre Hessian block. -/
theorem adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (hrank : HasAdaptiveAlignedRightRecenteredHessianRankOneRelations E)
    (rho : Equiv.Perm (Fin 4)) :
    let H := adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
      rho E
    H.activeDet = 0 ∧
      H.x * H.d - H.r * H.r = 0 ∧
      H.p * H.d - H.b * H.r = 0 := by
  let HP := adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E
  let H0 := adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E
  have hseries := hrank rho
  dsimp only at hseries
  have hspec : parameterConstantCoeffFourBlock HP = H0 := by
    simpa [HP, H0] using
      (parameterConstantCoeff_rightRecenteredHessianFourBlock rho E)

  have hactive : H0.activeDet = 0 := by
    have hz := hseries.1
    rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero] at hz
    simpa [H0] using hz

  have hsecond : H0.x * H0.d - H0.r * H0.r = 0 := by
    have hz :
        (parameterConstantCoeffFourBlock HP).x *
            (parameterConstantCoeffFourBlock HP).d -
          (parameterConstantCoeffFourBlock HP).r *
            (parameterConstantCoeffFourBlock HP).r = 0 := by
      simpa [parameterConstantCoeffFourBlock, HP] using hseries.2.1
    rw [hspec] at hz
    exact hz

  have hcross : H0.p * H0.d - H0.b * H0.r = 0 := by
    have hz :
        (parameterConstantCoeffFourBlock HP).p *
            (parameterConstantCoeffFourBlock HP).d -
          (parameterConstantCoeffFourBlock HP).b *
            (parameterConstantCoeffFourBlock HP).r = 0 := by
      simpa [parameterConstantCoeffFourBlock, HP] using hseries.2.2
    rw [hspec] at hz
    exact hz

  exact ⟨hactive, hsecond, hcross⟩

/-! ## Local coordinate permutations used to expose the finite core -/

private noncomputable def rankOneSwap23 : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

private noncomputable def rankOneSwap12 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2

private noncomputable def rankOneSwap13 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 3

/-- Local order `(2,1,3,0)`. -/
private noncomputable def rankOneOrder2130 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 3)

/-- Local order `(2,3,0,1)`. -/
private noncomputable def rankOneOrder2301 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

/-- Local order `(2,0,3,1)`. -/
private noncomputable def rankOneOrder2031 : Equiv.Perm (Fin 4) :=
  ((Equiv.swap 0 1).trans (Equiv.swap 1 2)).trans (Equiv.swap 1 3)

@[simp] private theorem rankOneSwap23_zero : rankOneSwap23 0 = 0 := by decide
@[simp] private theorem rankOneSwap23_one : rankOneSwap23 1 = 1 := by decide
@[simp] private theorem rankOneSwap23_two : rankOneSwap23 2 = 3 := by decide
@[simp] private theorem rankOneSwap23_three : rankOneSwap23 3 = 2 := by decide

@[simp] private theorem rankOneSwap12_zero : rankOneSwap12 0 = 0 := by decide
@[simp] private theorem rankOneSwap12_one : rankOneSwap12 1 = 2 := by decide
@[simp] private theorem rankOneSwap12_two : rankOneSwap12 2 = 1 := by decide
@[simp] private theorem rankOneSwap12_three : rankOneSwap12 3 = 3 := by decide

@[simp] private theorem rankOneSwap13_zero : rankOneSwap13 0 = 0 := by decide
@[simp] private theorem rankOneSwap13_one : rankOneSwap13 1 = 3 := by decide
@[simp] private theorem rankOneSwap13_two : rankOneSwap13 2 = 2 := by decide
@[simp] private theorem rankOneSwap13_three : rankOneSwap13 3 = 1 := by decide

@[simp] private theorem rankOneOrder2130_zero : rankOneOrder2130 0 = 2 := by decide
@[simp] private theorem rankOneOrder2130_one : rankOneOrder2130 1 = 1 := by decide
@[simp] private theorem rankOneOrder2130_two : rankOneOrder2130 2 = 3 := by decide
@[simp] private theorem rankOneOrder2130_three : rankOneOrder2130 3 = 0 := by decide

@[simp] private theorem rankOneOrder2301_zero : rankOneOrder2301 0 = 2 := by decide
@[simp] private theorem rankOneOrder2301_one : rankOneOrder2301 1 = 3 := by decide
@[simp] private theorem rankOneOrder2301_two : rankOneOrder2301 2 = 0 := by decide
@[simp] private theorem rankOneOrder2301_three : rankOneOrder2301 3 = 1 := by decide

@[simp] private theorem rankOneOrder2031_zero : rankOneOrder2031 0 = 2 := by decide
@[simp] private theorem rankOneOrder2031_one : rankOneOrder2031 1 = 0 := by decide
@[simp] private theorem rankOneOrder2031_two : rankOneOrder2031 2 = 3 := by decide
@[simp] private theorem rankOneOrder2031_three : rankOneOrder2031 3 = 1 := by decide

/-- The permutation family from the green rank-one residual contains the
finite core relations needed to force *all* `2 × 2` minors of any displayed
special-Hessian chart to vanish. -/
theorem adaptiveAlignedRightRecenteredSpecialHessian_hasRankOneCoreRelations
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (hrank : HasAdaptiveAlignedRightRecenteredHessianRankOneRelations E)
    (rho : Equiv.Perm (Fin 4)) :
    (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E).HasRankOneCoreRelations := by
  let H := adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E

  have h0 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank rho
  have h23 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneSwap23.trans rho)
  have h12 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneSwap12.trans rho)
  have h13 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneSwap13.trans rho)
  have h213 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneOrder2130.trans rho)
  have h2301 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneOrder2301.trans rho)
  have h2031 := adaptiveAlignedRightRecenteredSpecialHessian_rankOneRelations
    E hrank (rankOneOrder2031.trans rho)

  dsimp only at h0 h23 h12 h13 h213 h2301 h2031

  have hp01 : H.a * H.d - H.b * H.b = 0 := by
    simpa [H, GeneralFourBlock.activeDet] using h0.1
  have hp12 : H.x * H.d - H.r * H.r = 0 := by
    simpa [H] using h0.2.1
  have hc012 : H.p * H.d - H.b * H.r = 0 := by
    simpa [H] using h0.2.2

  have hp13 : H.z * H.d - H.s * H.s = 0 := by
    simpa [H, adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      rankOneSwap23] using h23.2.1
  have hc013 : H.q * H.d - H.b * H.s = 0 := by
    simpa [H, adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      rankOneSwap23] using h23.2.2

  have hc213 : H.y * H.d - H.r * H.s = 0 := by
    simpa [H, adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      HC4.Polynomial.hessian,
      pderiv_comm_commRing, mul_comm] using h213.2.2

  have hp02 : H.a * H.x - H.p * H.p = 0 := by
    simpa [H, GeneralFourBlock.activeDet,
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      rankOneSwap12] using h12.1

  have hp03 : H.a * H.z - H.q * H.q = 0 := by
    simpa [H, GeneralFourBlock.activeDet,
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      rankOneSwap13] using h13.1

  have hp23 : H.x * H.z - H.y * H.y = 0 := by
    simpa [H, GeneralFourBlock.activeDet,
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      rankOneOrder2301] using h2301.1

  have hc203 : H.y * H.a - H.p * H.q = 0 := by
    have hs := h2031.2.2
    -- The local `b` entry is the reversed `(2,0)` Hessian entry.  Commute
    -- the two partial derivatives once to identify it with `H.p`.
    simpa [H, adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Equiv.trans_apply,
      HC4.Polynomial.hessian,
      pderiv_comm_commRing, mul_comm] using hs

  exact {
    principal01 := hp01
    principal02 := hp02
    principal03 := hp03
    principal12 := hp12
    principal13 := hp13
    principal23 := hp23
    cross012 := hc012
    cross013 := hc013
    cross213 := hc213
    cross203 := hc203
  }

/-- **Honest all-minors form of the exceptional blocker branch.**

The previous green permutation/shear residual is not merely suggestive of
rank one: every `2 × 2` minor of the finite right-recentered special-fibre
Hessian vanishes, in every coordinate chart. -/
theorem adaptiveAlignedRightRecenteredSpecialHessian_allTwoByTwoMinorsZero
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap)
    (hrank : HasAdaptiveAlignedRightRecenteredHessianRankOneRelations E) :
    ∀ rho : Equiv.Perm (Fin 4),
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E).AllTwoByTwoMinorsZero := by
  intro rho
  exact GeneralFourBlock.allTwoByTwoMinorsZero_of_rankOneCoreRelations
    (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E)
    (adaptiveAlignedRightRecenteredSpecialHessian_hasRankOneCoreRelations
      E hrank rho)

/-- Blocker-facing frontier with a genuine determinantal rank-at-most-one
certificate.  The first two alternatives are the already-green Schur
architectures; the residual alternative retains the exact first longitudinal
departure and now certifies vanishing of every finite Hessian `2 × 2` minor.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFrontier_with_allMinors
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty (ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) ∨
      (HasFirstExactSmithExponentLongitudinalDeparture
          (polynomialFamilySpecialFiber B.aligned.endpoint.rightRecenteredFamily)
          B.exponent ∧
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero) := by
  rcases B.rightRecenteredHessianFrontier_with_firstDeparture hdefect with
    hschur | hzero | hres
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · exact Or.inr (Or.inr
      ⟨hres.1,
        adaptiveAlignedRightRecenteredSpecialHessian_allTwoByTwoMinorsZero
          B.aligned.endpoint hres.2⟩)

end

end HC4.Valuation
