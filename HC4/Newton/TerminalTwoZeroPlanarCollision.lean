import HC4.Newton.TerminalTwoZeroGradientConjugacy
import HC4.Newton.TerminalTwoZeroKellerReduction
import HC4.Newton.TerminalCollision
import Mathlib.Tactic

/-!
# A19.37: a two-zero terminal collision is already a planar Keller collision

The existing two-zero endpoint uses planar JC2 only to prove injectivity of the
planar base map.  Before invoking JC2, the terminal structure is already much
more explicit: the four-dimensional gradient is the Hessian-doubling map of a
planar Keller map.

This file records the converse direction needed for the unrestricted attack.
A *distinct* four-dimensional gradient collision in standard two-zero form
forces a distinct collision of the planar Keller base map itself.  If the two
base points were equal, invertibility of the evaluated planar Jacobian would
force equality of the two fibre points as well, contradicting distinctness of
the original four-points.

Thus the deep terminal endpoint is not merely "JC2-like": it canonically
produces an actual planar Keller counterexample witness.  No JC2 assumption is
used here.
-/

namespace HC4

noncomputable section

variable {K : Type*} [Field K]

/-- Concrete failure witness for planar Keller injectivity. -/
def HasPlanarKellerCollision (K : Type*) [Field K] : Prop :=
  ∃ G : PlanarPolynomialMap K,
    HasNonzeroConstantPlanarJacobian G ∧
      ∃ u v : Point2 K,
        u ≠ v ∧
          planarPolynomialMapEval G u = planarPolynomialMapEval G v

/-- A concrete Keller collision contradicts the planar JC2 injectivity
statement. -/
theorem HasPlanarKellerCollision.not_planarJC2
    (h : HasPlanarKellerCollision K) :
    ¬ PlanarJC2Injectivity K := by
  intro hJC2
  rcases h with ⟨G, hKeller, u, v, huv, hG⟩
  exact huv (hJC2 G hKeller hG)

/-- Conversely, classically, failure of the planar JC2 injectivity interface
is witnessed by an actual Keller collision. -/
theorem not_planarJC2_iff_hasPlanarKellerCollision :
    (¬ PlanarJC2Injectivity K) ↔ HasPlanarKellerCollision K := by
  classical
  constructor
  · intro hnot
    unfold PlanarJC2Injectivity at hnot
    push_neg at hnot
    rcases hnot with ⟨G, hKeller, hnoninj⟩
    rw [Function.not_injective_iff] at hnoninj
    rcases hnoninj with ⟨u, v, hG, huv⟩
    exact ⟨G, hKeller, u, v, huv, hG⟩
  · exact HasPlanarKellerCollision.not_planarJC2

end

end HC4

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- **Unconditional two-zero counterexample extraction.**

A distinct gradient collision of a standard two-zero Monge--Ampere terminal
potential produces a distinct collision of its planar Keller base map. -/
theorem standardTwoZero_terminal_hasPlanarKellerCollision
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (p q : Fin 4 → K)
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    HC4.HasPlanarKellerCollision K := by
  rcases standardTwoZero_mongeAmpere_hasPlanarKellerModel
      hd hhom hMA with
    ⟨A, C, hA, hC, hKeller⟩
  let G : HC4.PlanarPolynomialMap K := standardPlanarPairMap A C

  have hgrad : mvGradientMap F p = mvGradientMap F q := by
    funext i
    exact hcoll i

  have hbaseImage :
      HC4.planarPolynomialMapEval G (standardBasePoint p) =
        HC4.planarPolynomialMapEval G (standardBasePoint q) := by
    have hpos := congrArg standardFibrePoint hgrad
    rw [standardTwoZero_gradient_positive_eq_planar hA hC p] at hpos
    rw [standardTwoZero_gradient_positive_eq_planar hA hC q] at hpos
    simpa [G] using hpos

  have hbaseNe : standardBasePoint p ≠ standardBasePoint q := by
    intro hbase
    have hzero := congrArg standardBasePoint hgrad
    rw [standardTwoZero_gradient_zero_eq_vecMul hd hhom hA hC p] at hzero
    rw [standardTwoZero_gradient_zero_eq_vecMul hd hhom hA hC q] at hzero
    rw [hbase] at hzero
    have hdet :
        Matrix.det
            (HC4.planarJacobianMatrixAt G (standardBasePoint q)) ≠ 0 := by
      exact HC4.planarJacobianMatrixAt_det_ne_zero G hKeller _
    have hfibre : standardFibrePoint p = standardFibrePoint q := by
      apply HC4.vecMul_injective_of_det_ne_zero
        (HC4.planarJacobianMatrixAt G (standardBasePoint q)) hdet
      simpa [G] using hzero
    have hsplit : standardSplitPoint p = standardSplitPoint q := by
      apply Prod.ext
      · exact hbase
      · exact hfibre
    exact hpq (standardSplitPoint_injective hsplit)

  exact ⟨G, hKeller,
    standardBasePoint p, standardBasePoint q,
    hbaseNe, hbaseImage⟩

/-- A standard two-zero terminal collision therefore proves the negation of
the exact planar JC2 injectivity interface. -/
theorem standardTwoZero_terminal_not_planarJC2
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (p q : Fin 4 → K)
    (hpq : p ≠ q)
    (hcoll : HasExactGradientCollision F p q) :
    ¬ HC4.PlanarJC2Injectivity K :=
  (standardTwoZero_terminal_hasPlanarKellerCollision
    hd hhom hMA p q hpq hcoll).not_planarJC2

end

end HC4.Newton
