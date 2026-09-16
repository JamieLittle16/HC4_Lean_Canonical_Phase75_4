import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticInitialForm
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import HC4.Newton.MixedDegreeWallRefinement
import HC4.Polynomial.MaximalHessianInitial
import HC4.Valuation.AdaptiveAlignedSmithFirstContactUniqueZeroElimination
import HC4.Newton.TerminalAssociatedGradedEndpoint
import Mathlib.Tactic

/-!
# A19.13: zero-clock quadratic terminals are honest one-zero endpoints

A19.10--12 retained the complete symmetric Smith equality face and identified
it with the exact maximal initial form for the negative source weight

    (0,-1,-1,-2)

at potential weight `-2`.  The determinant weight is exactly zero.  Therefore,
when the terminal source clock is zero, the represented special fibre still
has Hessian determinant one and the maximal-initial Hessian theorem gives
Hessian determinant one on the complete quadratic face itself.

The same face has only the transverse quadratic Smith patterns, so every first
derivative vanishes on the distinguished longitudinal axis.  It therefore
retains the marked exact collision `0 ~ e₀`.

Finally the positive weight `(0,1,1,2)` becomes the standard one-zero weight
`(0,2,1,1)` after swapping coordinates `1` and `3`.  Coordinate permutation
preserves both weighted homogeneity and the Monge--Ampere equation, so the
complete quadratic face is an actual certified one-zero associated-graded
collision endpoint.

No singular ordinary-degree packet is promoted to a Keller potential here:
the determinant-one object is the *complete* Smith equality face.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry

variable {RR : RepairRanking}
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {complexity : ℕ}
variable {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
  RR state complexity}

/-- A pure ramified presentation of a zero-clock source still has zero raw
clock. -/
theorem presentedState_rawDefect_eq_zero_of_source
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T)
    (hzero : state.rawDefect = 0) :
    T.presentedState.rawDefect = 0 := by
  have hmove := T.sourcePresentation
  change Nonempty
    (CertifiedRamifiedEpisodeInternalMove T.presentedState state) at hmove
  rcases hmove with ⟨hmove⟩
  rw [hmove.raw_eq, hzero]
  simp

/-- At source clock zero the represented terminal special fibre still has
Hessian determinant one. -/
theorem specialFiber_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T)
    (hzero : state.rawDefect = 0) :
    HC4.Polynomial.hessianDeterminant T.specialFiber = 1 := by
  have hpresented : T.presentedState.rawDefect = 0 :=
    G.presentedState_rawDefect_eq_zero_of_source hzero
  change
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber T.presentedState.family) = 1
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := T.presentedState.hessianDefect
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef, hpresented]
  simp

/-- The complete quadratic Smith equality face has Hessian determinant one at
clock zero.  This is the determinant-preserving object; the separate minimal
ordinary-degree packet remains Hessian-singular. -/
theorem quadraticFace_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T)
    (hzero : state.rawDefect = 0) :
    HC4.Polynomial.hessianDeterminant G.quadraticFace = 1 := by
  have htop :=
    HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      terminalQuadraticNegativeWeight (-2) T.specialFiber G.negativeWeightLE
  have htop' :
      HC4.Polynomial.initialForm terminalQuadraticNegativeWeight 0
          (HC4.Polynomial.hessianDeterminant T.specialFiber) =
        HC4.Polynomial.hessianDeterminant
          (HC4.Polynomial.initialForm terminalQuadraticNegativeWeight (-2)
            T.specialFiber) := by
    simpa [terminalQuadraticNegativeWeight_sum] using htop
  have hdet : HC4.Polynomial.hessianDeterminant T.specialFiber = 1 :=
    G.specialFiber_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero hzero
  rw [hdet] at htop'
  have hone :
      HC4.Polynomial.initialForm terminalQuadraticNegativeWeight 0
          (1 : MvPolynomial (Fin 4) K) = 1 := by
    exact HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_one K terminalQuadraticNegativeWeight)
  rw [hone] at htop'
  rw [G.quadraticFace_eq_negativeInitialForm]
  exact htop'.symm

/-- Every derivative of the complete quadratic Smith face vanishes on the
whole distinguished longitudinal axis. -/
theorem quadraticFace_gradient_axis_zero
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    ∀ x : K, ∀ i : Fin 4,
      mvGradientComponentAt
        (Fin.cons x (fun _ : Fin 3 => (0 : K)))
        G.quadraticFace i = 0 := by
  let S : Finset SmithSupportExponent :=
    smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ))
  have hnot (e : SmithSupportExponent)
      (hbad :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e ∨
        IsWLinearSmithPattern e) :
      e ∉ smithProjectedSupport (1 : Fin 4) 2 3 G.quadraticFace := by
    intro he
    unfold smithProjectedSupport at he
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    have hdcoeff : MvPolynomial.coeff d G.quadraticFace ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hdS :
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ S := by
      unfold quadraticFace at hdcoeff
      exact smithSubfacePolynomial_supported
        (1 : Fin 4) 2 3 S T.specialFiber d hdcoeff
    have hpattern := G.quadratic _ (by simpa [S] using hdS)
    rcases hpattern with hyy | hyz | hzz <;>
      rcases hbad with hpure | hfirst | hsecond | hw <;>
      simp [IsPureLongitudinalSmithPattern,
        IsLowNegativeFirstSmithPattern,
        IsLowNegativeSecondSmithPattern,
        IsWLinearSmithPattern, smithSupportExponentOf] at * <;> omega
  have hpure : longitudinalCoefficientPolynomial 0 0 0 G.quadraticFace = 0 := by
    by_contra hne
    exact hnot ⟨0, 0, 0⟩ (Or.inl ⟨rfl, rfl, rfl⟩)
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G.quadraticFace ⟨0, 0, 0⟩).mp hne)
  have hpureAt : longitudinalCoefficientPolynomialAt 0 G.quadraticFace = 0 := by
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hpure
  have hfirst : longitudinalCoefficientPolynomial 0 1 0 G.quadraticFace = 0 := by
    by_contra hne
    exact hnot ⟨0, 1, 0⟩ (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G.quadraticFace ⟨0, 1, 0⟩).mp hne)
  have hsecond : longitudinalCoefficientPolynomial 1 0 0 G.quadraticFace = 0 := by
    by_contra hne
    exact hnot ⟨1, 0, 0⟩
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G.quadraticFace ⟨1, 0, 0⟩).mp hne)
  have hw : longitudinalCoefficientPolynomial 0 0 1 G.quadraticFace = 0 := by
    by_contra hne
    exact hnot ⟨0, 0, 1⟩
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G.quadraticFace ⟨0, 0, 1⟩).mp hne)
  intro x i
  change mvGradientComponentAt
    (Fin.cons x (fun _ : Fin 3 => (0 : K))) G.quadraticFace i = 0
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold mvGradientComponentAt
    rw [eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
    rw [longitudinalAxisRestriction_eq_coefficient_zero, hpureAt]
    simp
  · unfold mvGradientComponentAt
    rw [eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    fin_cases j
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hsecond
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hfirst
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hw

/-- The complete determinant-one quadratic face retains the canonical marked
axis collision. -/
theorem quadraticFace_exactAxisCollision
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    HasExactGradientCollision
      G.quadraticFace
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  intro i
  have hzeroPoint : (fun _ : Fin 4 => (0 : K)) =
      Fin.cons 0 (fun _ : Fin 3 => (0 : K)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  have haxisPoint : coordinateAxisPoint (K := K) (0 : Fin 4) =
      Fin.cons 1 (fun _ : Fin 3 => (0 : K)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp [coordinateAxisPoint]
  rw [hzeroPoint, haxisPoint]
  rw [G.quadraticFace_gradient_axis_zero 0 i,
    G.quadraticFace_gradient_axis_zero 1 i]

/-- At clock zero, the complete quadratic Smith face is an honest certified
one-zero associated-graded collision endpoint (up to swapping coordinates
`1` and `3`). -/
theorem quadraticFace_associatedGradedCollisionData_of_source_rawDefect_eq_zero
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T)
    (hzero : state.rawDefect = 0) :
    Nonempty (TerminalAssociatedGradedCollisionData K) := by
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
        (MvPolynomial.rename rho G.quadraticFace) := by
    have h := integralWeightedHomogeneous_rename_perm
      G.quadraticFace_positiveHomogeneous rho
    rw [hweight] at h
    exact h
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere G.quadraticFace := by
    unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    exact G.quadraticFace_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero hzero
  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho G.quadraticFace) :=
    isPolynomialMongeAmpere_rename_perm rho hMA
  have hendpoint : CertifiedTerminalDirectJumpEndpoint G.quadraticFace :=
    .permuted rho
      (.oneZero 2 1 (by norm_num) (by norm_num) hhomRenamed hMARenamed)
  exact ⟨{
    fibre := G.quadraticFace
    leftPoint := fun _ : Fin 4 => (0 : K)
    rightPoint := coordinateAxisPoint (K := K) (0 : Fin 4)
    distinct := T.specialFiber_markedPoints_distinct
    exactCollision := G.quadraticFace_exactAxisCollision
    endpoint := hendpoint
  }⟩

end AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry

end

end HC4.Valuation
