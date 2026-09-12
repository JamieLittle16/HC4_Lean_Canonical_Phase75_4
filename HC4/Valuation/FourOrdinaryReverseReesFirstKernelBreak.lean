import HC4.Valuation.FourOrdinaryReverseReesCollision
import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# Ordinary reverse-Rees first kernel break gives source rank-two geometry

`FirstKernelBreakRankTwo` proves the finite polynomial-series statement:
a first preclosing break of a rank-three constant kernel has a nonzero
principal `2 x 2` coefficient-layer minor.  `FourOrdinaryReverseRees` proves
that the coefficient layers of the honest ordinary reverse-Rees family are
exactly the ordinary homogeneous layers of the original source.

This file is the representation bridge between those two results.

No A19 terminal record appears here.  The input is deliberately source-level:

* `F` has Hessian determinant one;
* `D` is an actual ordinary-degree bound;
* through reverse-Rees orders below `q`, coordinate `3` remains a Hessian
  kernel direction on the corresponding homogeneous source layers;
* at order `q` that kernel genuinely breaks;
* the constant complementary `3 x 3` determinant of the reverse-Rees Hessian
  block is nonzero.

The conclusion is an explicit nonzero principal `2 x 2` Hessian minor on the
actual homogeneous source layer `H_{D-q}`.  No repair/progress conclusion is
attached here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Source-facing rank-two witness on one ordinary homogeneous layer. -/
structure FourOrdinaryLayerPrincipalRankTwoWitness
    (F : MvPolynomial (Fin 4) K)
    (D q : ℕ) where
  index : Fin 3
  minor_ne_zero :
    let H := fourOrdinaryDegreeComponent F (D - q)
    HC4.Polynomial.hessian H (Fin.castSucc index) (Fin.castSucc index) *
          HC4.Polynomial.hessian H (3 : Fin 4) (3 : Fin 4) -
        HC4.Polynomial.hessian H (Fin.castSucc index) (3 : Fin 4) *
          HC4.Polynomial.hessian H (3 : Fin 4) (Fin.castSucc index) ≠ 0

/-- Coefficients of the actual reverse-Rees Hessian series are exactly the
Hessians of ordinary homogeneous source layers. -/
theorem fourOrdinaryReverseRees_parameterFirstHessian_coeff
    (F : MvPolynomial (Fin 4) K)
    (D n : ℕ)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hn : n ≤ D)
    (i j : Fin 4) :
    (parameterFirstHessian
        (fourOrdinaryReverseReesFamily F D) i j).coeff n =
      HC4.Polynomial.hessian
        (fourOrdinaryDegreeComponent F (D - n)) i j := by
  rw [parameterFirstHessian_coeff]
  rw [familyParameterLayer_fourOrdinaryReverseReesFamily F D n hmax hn]

/-- **Generic ordinary reverse-Rees first-kernel-break theorem.**

If coordinate `3` is a Hessian kernel of every ordinary homogeneous layer
strictly before reverse-Rees order `q`, but not of the order-`q` layer, then
strictly before the reverse-Rees determinant-closing order an actual
homogeneous source layer carries a nonzero principal `2 x 2` Hessian minor.

The nonzero complementary `3 x 3` hypothesis is stated on the constant
coefficient of the canonical family four-block.  This is the exact hypothesis
needed by `FirstKernelBreakFourBlockData`; A19 adapters may prove it from their
straightened rank-three top cone without any further series algebra. -/
theorem fourOrdinaryReverseRees_firstKernelBreak_rankTwo
    (F : MvPolynomial (Fin 4) K)
    (D q : ℕ)
    (hD : 3 ≤ D)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hqpos : 0 < q)
    (hqle : q ≤ D - 2)
    (hbefore :
      ∀ n : ℕ,
        n < q →
        ∀ i : Fin 4,
          HC4.Polynomial.hessian
              (fourOrdinaryDegreeComponent F (D - n)) i (3 : Fin 4) = 0)
    (hbreak :
      ∃ i : Fin 4,
        HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) i (3 : Fin 4) ≠ 0)
    (hactive :
      (firstKernelBreakActiveThreeDet
          (familyHessianFourBlock
            (fourOrdinaryReverseReesFamily F D))).coeff 0 ≠ 0) :
    Nonempty (FourOrdinaryLayerPrincipalRankTwoWitness F D q) := by
  let R := fourOrdinaryReverseReesFamily F D
  let B := familyHessianFourBlock R
  let Delta := 4 * (D - 2)

  have hD2 : 2 ≤ D := by omega
  have hdef : HasPolynomialFamilyHessianDefect (K := K) R Delta := by
    dsimp [R, Delta]
    exact fourOrdinaryReverseReesFamily_hasHessianDefect F D hD2 hmax hdet
  have hqltD : q ≤ D := by omega
  have hqltDelta : q < Delta := by
    dsimp [Delta]
    omega

  have hcoeff
      (n : ℕ) (hn : n ≤ D) (i j : Fin 4) :
      (parameterFirstHessian R i j).coeff n =
        HC4.Polynomial.hessian
          (fourOrdinaryDegreeComponent F (D - n)) i j := by
    dsimp [R]
    exact fourOrdinaryReverseRees_parameterFirstHessian_coeff
      F D n hmax hn i j

  have hqzero : ∀ n : ℕ, n < q → B.q.coeff n = 0 := by
    intro n hn
    have hnD : n ≤ D := by omega
    change (parameterFirstHessian R (0 : Fin 4) (3 : Fin 4)).coeff n = 0
    rw [hcoeff n hnD (0 : Fin 4) (3 : Fin 4)]
    exact hbefore n hn (0 : Fin 4)
  have hszero : ∀ n : ℕ, n < q → B.s.coeff n = 0 := by
    intro n hn
    have hnD : n ≤ D := by omega
    change (parameterFirstHessian R (1 : Fin 4) (3 : Fin 4)).coeff n = 0
    rw [hcoeff n hnD (1 : Fin 4) (3 : Fin 4)]
    exact hbefore n hn (1 : Fin 4)
  have hyzero : ∀ n : ℕ, n < q → B.y.coeff n = 0 := by
    intro n hn
    have hnD : n ≤ D := by omega
    change (parameterFirstHessian R (2 : Fin 4) (3 : Fin 4)).coeff n = 0
    rw [hcoeff n hnD (2 : Fin 4) (3 : Fin 4)]
    exact hbefore n hn (2 : Fin 4)
  have hzzero : ∀ n : ℕ, n < q → B.z.coeff n = 0 := by
    intro n hn
    have hnD : n ≤ D := by omega
    change (parameterFirstHessian R (3 : Fin 4) (3 : Fin 4)).coeff n = 0
    rw [hcoeff n hnD (3 : Fin 4) (3 : Fin 4)]
    exact hbefore n hn (3 : Fin 4)

  have hdetB : B.determinantCore =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
    dsimp [B]
    exact familyHessianFourBlock_determinantCore_eq_X_pow R hdef

  have hbreakB :
      B.q.coeff q ≠ 0 ∨
        B.s.coeff q ≠ 0 ∨
        B.y.coeff q ≠ 0 ∨
        B.z.coeff q ≠ 0 := by
    rcases hbreak with ⟨i, hi⟩
    have hqi :
        (parameterFirstHessian R i (3 : Fin 4)).coeff q ≠ 0 := by
      rw [hcoeff q hqltD i (3 : Fin 4)]
      exact hi
    fin_cases i
    · exact Or.inl hqi
    · exact Or.inr (Or.inl hqi)
    · exact Or.inr (Or.inr (Or.inl hqi))
    · exact Or.inr (Or.inr (Or.inr hqi))

  let E : FirstKernelBreakFourBlockData (MvPolynomial (Fin 4) K) := {
    block := B
    order := q
    defect := Delta
    order_pos := hqpos
    order_lt_defect := hqltDelta
    q_lower_zero := hqzero
    s_lower_zero := hszero
    y_lower_zero := hyzero
    z_lower_zero := hzzero
    activeThree_coeff_zero_ne_zero := by simpa [B, R] using hactive
    determinantCore_eq := hdetB
    kernel_break := hbreakB
  }

  have hminor := E.exists_nonzero_principalMinor_at_order
  rcases hminor with h0 | h1 | h2
  · refine ⟨{
      index := (0 : Fin 3)
      minor_ne_zero := ?_
    }⟩
    dsimp
    change
      HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (0 : Fin 4) (0 : Fin 4) *
          HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (3 : Fin 4) (3 : Fin 4) -
        HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (0 : Fin 4) (3 : Fin 4) *
          HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (3 : Fin 4) (0 : Fin 4) ≠ 0
    have hsymm :
        HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (3 : Fin 4) (0 : Fin 4) =
          HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (0 : Fin 4) (3 : Fin 4) := by
      exact pderiv_comm_commRing _ _ _
    rw [hsymm]
    change
      B.a.coeff q * B.z.coeff q - B.q.coeff q * B.q.coeff q ≠ 0 at h0
    simpa only [hcoeff q hqltD] using h0
  · refine ⟨{
      index := (1 : Fin 3)
      minor_ne_zero := ?_
    }⟩
    dsimp
    have hsymm :
        HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (3 : Fin 4) (1 : Fin 4) =
          HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (1 : Fin 4) (3 : Fin 4) := by
      exact pderiv_comm_commRing _ _ _
    rw [hsymm]
    change
      B.d.coeff q * B.z.coeff q - B.s.coeff q * B.s.coeff q ≠ 0 at h1
    simpa only [hcoeff q hqltD] using h1
  · refine ⟨{
      index := (2 : Fin 3)
      minor_ne_zero := ?_
    }⟩
    dsimp
    have hsymm :
        HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (3 : Fin 4) (2 : Fin 4) =
          HC4.Polynomial.hessian
            (fourOrdinaryDegreeComponent F (D - q)) (2 : Fin 4) (3 : Fin 4) := by
      exact pderiv_comm_commRing _ _ _
    rw [hsymm]
    change
      B.x.coeff q * B.z.coeff q - B.y.coeff q * B.y.coeff q ≠ 0 at h2
    simpa only [hcoeff q hqltD] using h2

end

end HC4.Valuation
