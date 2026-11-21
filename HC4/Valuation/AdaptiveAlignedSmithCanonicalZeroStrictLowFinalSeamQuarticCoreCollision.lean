import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticHomogeneousCore
import HC4.Newton.TerminalOneZeroAffineRecovery
import Mathlib.Tactic

/-!
# G22: the quartic homogeneous core carries the antipodal collision

G21 decomposes the midpoint-normalized quartic seam as an affine part plus
the homogeneous nonlinear core q2+h3+h4, and proves that the affine part has
zero Hessian.

Therefore every component of the affine gradient is a constant polynomial.
Subtracting that same constant gradient from the two sides of the midpoint
collision shows that the homogeneous nonlinear core itself has the exact
antipodal gradient collision.

This is a purely formal affine-cleanup step.  No low-dimensional
Hessian/Jacobian theorem or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Each gradient component of the affine midpoint part is constant. -/
theorem finalSeamMidpointAffinePart_gradientComponent_constant
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    MvPolynomial.pderiv i T.finalSeamMidpointAffinePart =
      MvPolynomial.C
        (MvPolynomial.coeff 0
          (MvPolynomial.pderiv i T.finalSeamMidpointAffinePart)) := by
  have hH := T.finalSeamMidpointAffinePart_hessian_eq_zero
  have hrow :
      ∀ j : Fin 4,
        MvPolynomial.pderiv j
          (MvPolynomial.pderiv i T.finalSeamMidpointAffinePart) = 0 := by
    intro j
    have hij := congrArg (fun M => M i j) hH
    simpa [HC4.Polynomial.hessian_apply] using hij
  exact finFour_eq_C_of_all_pderiv_eq_zero
    (MvPolynomial.pderiv i T.finalSeamMidpointAffinePart)
    (hrow 0) (hrow 1) (hrow 2) (hrow 3)

/-- The affine gradient evaluates equally at arbitrary source points. -/
theorem finalSeamMidpointAffinePart_gradient_eval_eq
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4)
    (p q : Fin 4 → K) :
    MvPolynomial.eval p
        (MvPolynomial.pderiv i T.finalSeamMidpointAffinePart) =
      MvPolynomial.eval q
        (MvPolynomial.pderiv i T.finalSeamMidpointAffinePart) := by
  rw [T.finalSeamMidpointAffinePart_gradientComponent_constant i]
  simp

/-- The nonlinear quartic core itself carries the exact antipodal gradient
collision. -/
theorem finalSeamMidpointQuarticCore_exactCollision
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    HasExactGradientCollision
      T.finalSeamMidpointQuarticCore
      (finalSeamMidpointLeft (K := K))
      (finalSeamMidpointRight (K := K)) := by
  intro i
  have hcoll := T.finalSeamMidpointFibre_exactCollision i
  have hdecomp :=
    T.finalSeamMidpointFibre_eq_affine_add_quarticCore hdeg
  unfold mvGradientComponentAt at hcoll ⊢
  rw [hdecomp] at hcoll
  simp only [map_add] at hcoll
  have ha :=
    T.finalSeamMidpointAffinePart_gradient_eval_eq i
      (finalSeamMidpointLeft (K := K))
      (finalSeamMidpointRight (K := K))
  linear_combination hcoll - ha

/-- G22 packet: a determinant-one q2+h3+h4 homogeneous core with a nontrivial
antipodal exact gradient collision. -/
structure FinalSeamQuarticCoreCollisionData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  homogeneousCore : T.FinalSeamQuarticHomogeneousCoreData
  exactCollision :
    HasExactGradientCollision
      T.finalSeamMidpointQuarticCore
      (finalSeamMidpointLeft (K := K))
      (finalSeamMidpointRight (K := K))
  distinct :
    finalSeamMidpointLeft (K := K) ≠
      finalSeamMidpointRight (K := K)

/-- Assemble the completely affine-free quartic collision packet. -/
theorem finalSeamQuarticCoreCollisionData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    Nonempty T.FinalSeamQuarticCoreCollisionData := by
  rcases T.finalSeamQuarticHomogeneousCoreData hdeg with ⟨C⟩
  exact ⟨{
    homogeneousCore := C
    exactCollision := T.finalSeamMidpointQuarticCore_exactCollision hdeg
    distinct := finalSeamMidpoint_points_distinct (K := K)
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
