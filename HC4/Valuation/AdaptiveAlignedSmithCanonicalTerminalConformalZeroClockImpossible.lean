import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalConformalZeroClockEndpoint
import Mathlib.Tactic

/-!
# A19.23: unconditional closure of the conformal zero-clock terminal

A19.15 constructs, whenever the three genuinely strict low Smith patterns are
absent, the complete conformal degree-two face of a zero-clock presented
terminal.  After swapping coordinates `1` and `3` this face is homogeneous for
the standard one-zero weight `(0,2,1,1)`, has Hessian determinant one, and
retains the marked collision `0 ~ e₀`.

The generic associated-graded endpoint interface routes a one-zero endpoint
through planar JC2 because it allows arbitrary collision points.  The marked
collision here is much stronger.  The already-green affine one-zero recovery
theorem says equality of gradients determines the unique zero-weight source
coordinate.  Applied to the renamed collision it would force `0 = 1`.

Thus this zero-clock branch is contradictory without JC2.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

variable {RR : RepairRanking}
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {complexity : ℕ}

/-- The conformal zero-clock endpoint of A19.15 is impossible outright.

The fixed permutation `swap 1 3` puts the positive conformal weight
`(0,1,1,2)` into standard one-zero form `(0,2,1,1)`.  The permutation fixes the
longitudinal coordinate, so the transported marked collision still has
zero-coordinate values `0` and `1`.  One-zero affine recovery therefore gives
the contradiction directly. -/
theorem conformalDegreeTwoFace_impossible_of_source_rawDefect_eq_zero
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hzero : state.rawDefect = 0)
    (hno : T.HasNoStrictLowSmithPatterns) :
    False := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3

  have hweight :
      (fun i : Fin 4 => terminalQuadraticPositiveWeight (rho.symm i)) =
        standardOneZeroTerminalWeight 2 1 := by
    funext i
    fin_cases i
    · have hswap :
          (Equiv.swap (1 : Fin 4) 3) (0 : Fin 4) = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      simp [rho, hswap, terminalQuadraticPositiveWeight,
        standardOneZeroTerminalWeight]
    · simp [rho, terminalQuadraticPositiveWeight,
        standardOneZeroTerminalWeight]
    · have hswap :
          (Equiv.swap (1 : Fin 4) 3) (2 : Fin 4) = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      simp [rho, hswap, terminalQuadraticPositiveWeight,
        standardOneZeroTerminalWeight]
    · simp [rho, terminalQuadraticPositiveWeight,
        standardOneZeroTerminalWeight]

  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight 2 1) 2
        (MvPolynomial.rename rho T.conformalDegreeTwoFace) := by
    have h := integralWeightedHomogeneous_rename_perm
      T.conformalDegreeTwoFace_positiveHomogeneous rho
    rw [hweight] at h
    exact h

  have hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        T.conformalDegreeTwoFace := by
    unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    exact T.conformalDegreeTwoFace_hessianDeterminant_eq_one hzero hno

  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho T.conformalDegreeTwoFace) :=
    isPolynomialMongeAmpere_rename_perm rho hMA

  let p : Fin 4 → K := fun _ => 0
  let q : Fin 4 → K := coordinateAxisPoint (K := K) (0 : Fin 4)

  have hgrad : mvGradientMap T.conformalDegreeTwoFace p =
      mvGradientMap T.conformalDegreeTwoFace q :=
    mvGradientMap_eq_of_exactCollision
      T.conformalDegreeTwoFace p q T.conformalDegreeTwoFace_exactAxisCollision

  have hgradRenamed :
      mvGradientMap
          (MvPolynomial.rename rho T.conformalDegreeTwoFace)
          (terminalPermutePoint rho p) =
        mvGradientMap
          (MvPolynomial.rename rho T.conformalDegreeTwoFace)
          (terminalPermutePoint rho q) := by
    funext j
    rw [mvGradientMap_rename_perm, mvGradientMap_rename_perm]
    exact congrFun hgrad (rho.symm j)

  have hrecover :=
    standardOneZero_gradient_eq_recovers_zero
      (d := (2 : ℤ)) (a := (1 : ℤ))
      (F := MvPolynomial.rename rho T.conformalDegreeTwoFace)
      (by norm_num) (by norm_num)
      hhomRenamed hMARenamed hgradRenamed

  have hrho0 : rho.symm (0 : Fin 4) = 0 := by
    decide
  have hbad : (0 : K) = 1 := by
    change p (rho.symm 0) = q (rho.symm 0) at hrecover
    rw [hrho0] at hrecover
    simpa [p, q, coordinateAxisPoint] using hrecover
  exact zero_ne_one hbad

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation
