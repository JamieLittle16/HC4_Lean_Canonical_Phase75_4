import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticZeroClockEndpoint
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSupportFrontier
import Mathlib.Tactic

/-!
# A19.15: zero-clock terminals with no strict low blocker are one-zero endpoints

A19.13 treated the surviving quadratic face after excluding all four historical
blocker patterns, including the `w`-linear pattern `(0,0,1)`.  For the actual
JC2 endpoint that last exclusion is unnecessary.

With the conformal positive weight

    (0,1,1,2)

both the three quadratic Smith patterns and the `w`-linear pattern have degree
exactly two.  Only the genuinely earlier patterns

    (0,0,0), (0,1,0), (1,0,0)

have degree below two.  Hence if those three strict low patterns are absent,
the maximal negative-weight initial form at level `-2` is still an honest
one-zero homogeneous face.

The only extra point relative to A19.13 is the marked collision.  A `w`-linear
term may contribute to the fourth gradient component on the longitudinal axis,
but the level `-2` initial form retains its entire longitudinal coefficient
polynomial exactly.  Thus the original terminal equality at `0` and `e₀`
passes to the conformal face.
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

/-- The three genuinely sub-conformal Smith patterns are absent from the
represented terminal special fibre. -/
def HasNoStrictLowSmithPatterns
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) : Prop :=
  ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
    ¬ IsPureLongitudinalSmithPattern e ∧
    ¬ IsLowNegativeFirstSmithPattern e ∧
    ¬ IsLowNegativeSecondSmithPattern e

/-- The conformal degree-two face of the actual terminal special fibre. -/
noncomputable def conformalDegreeTwoFace
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm terminalQuadraticNegativeWeight (-2) T.specialFiber

/-- A pure ramified presentation preserves a zero source raw clock. -/
theorem presentedState_rawDefect_eq_zero_of_source
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hzero : state.rawDefect = 0) :
    T.presentedState.rawDefect = 0 := by
  have hmove := T.sourcePresentation
  change Nonempty
    (CertifiedRamifiedEpisodeInternalMove T.presentedState state) at hmove
  rcases hmove with ⟨hmove⟩
  rw [hmove.raw_eq, hzero]
  simp

/-- At source clock zero the represented special fibre itself has Hessian
 determinant one. -/
theorem specialFiber_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hzero : state.rawDefect = 0) :
    HC4.Polynomial.hessianDeterminant T.specialFiber = 1 := by
  have hpresented : T.presentedState.rawDefect = 0 :=
    T.presentedState_rawDefect_eq_zero_of_source hzero
  change
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber T.presentedState.family) = 1
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := T.presentedState.hessianDefect
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef, hpresented]
  simp

/-- Absence of the three strict low patterns puts the full special fibre on or
above conformal degree two. -/
theorem conformalNegativeWeightLE_of_noStrictLow
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hno : T.HasNoStrictLowSmithPatterns) :
    HC4.Polynomial.IsWeightLE terminalQuadraticNegativeWeight (-2)
      T.specialFiber := by
  intro d hd
  let e := smithSupportExponentOf (1 : Fin 4) 2 3 d
  have he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hnone := hno e he
  have hshape : HasGeneralSurvivingSmithGradeShape e :=
    generalSurvivingSmithGradeShape_of_noNegativeLowPatterns e hnone
  have htwo : 2 ≤ e.b + e.c + 2 * e.d :=
    two_le_terminalQuadraticDegree_of_generalSurvivingShape e hshape
  have hcoords :
      e.b = d (1 : Fin 4) ∧
      e.c = d (2 : Fin 4) ∧
      e.d = d (3 : Fin 4) := by
    simp [e, smithSupportExponentOf]
  rw [terminalQuadraticNegativeWeight_finsupp]
  rcases hcoords with ⟨hb, hc, hw⟩
  rw [hb, hc, hw] at htwo
  omega

/-- Every monomial of the conformal initial form has positive conformal degree
exactly two. -/
theorem conformalDegreeTwoFace_positiveHomogeneous
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) :
    IsIntegralWeightedHomogeneous
      terminalQuadraticPositiveWeight 2 T.conformalDegreeTwoFace := by
  intro d hd
  unfold conformalDegreeTwoFace at hd
  rw [HC4.Polynomial.coeff_initialForm] at hd
  split at hd
  · rename_i hweight
    have hneg := hweight
    rw [terminalQuadraticNegativeWeight_finsupp] at hneg
    rw [AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry.
      terminalQuadraticPositiveWeight_integralWeightedDegree]
    omega
  · exact (hd rfl).elim

/-- The conformal degree-two face keeps Hessian determinant one at zero raw
clock. -/
theorem conformalDegreeTwoFace_hessianDeterminant_eq_one
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hzero : state.rawDefect = 0)
    (hno : T.HasNoStrictLowSmithPatterns) :
    HC4.Polynomial.hessianDeterminant T.conformalDegreeTwoFace = 1 := by
  have hbound := T.conformalNegativeWeightLE_of_noStrictLow hno
  have htop :=
    HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      terminalQuadraticNegativeWeight (-2) T.specialFiber hbound
  have htop' :
      HC4.Polynomial.initialForm terminalQuadraticNegativeWeight 0
          (HC4.Polynomial.hessianDeterminant T.specialFiber) =
        HC4.Polynomial.hessianDeterminant T.conformalDegreeTwoFace := by
    simpa [terminalQuadraticNegativeWeight_sum,
      AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.conformalDegreeTwoFace]
      using htop
  have hdet : HC4.Polynomial.hessianDeterminant T.specialFiber = 1 :=
    T.specialFiber_hessianDeterminant_eq_one_of_source_rawDefect_eq_zero hzero
  rw [hdet] at htop'
  have hone :
      HC4.Polynomial.initialForm terminalQuadraticNegativeWeight 0
          (1 : MvPolynomial (Fin 4) K) = 1 := by
    exact HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_one K terminalQuadraticNegativeWeight)
  rw [hone] at htop'
  exact htop'.symm

/-- Every supported projected exponent of the conformal degree-two face has
positive conformal degree exactly two. -/
theorem conformalDegreeTwoFace_projected_degree_two
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.conformalDegreeTwoFace) :
    e.b + e.c + 2 * e.d = 2 := by
  rcases smithProjectedSupport_realised (1 : Fin 4) 2 3
      T.conformalDegreeTwoFace e he with ⟨d, hd, hde⟩
  have hcoeff : MvPolynomial.coeff d T.conformalDegreeTwoFace ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hhom := T.conformalDegreeTwoFace_positiveHomogeneous d hcoeff
  rw [AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry.
    terminalQuadraticPositiveWeight_integralWeightedDegree] at hhom
  have hcoords :
      e.b = d (1 : Fin 4) ∧
      e.c = d (2 : Fin 4) ∧
      e.d = d (3 : Fin 4) := by
    simpa [smithSupportExponentOf] using congrArg id hde.symm
  rcases hcoords with ⟨hb, hc, hw⟩
  rw [hb, hc, hw]
  exact_mod_cast hhom

/-- Hence the conformal face contains no pure longitudinal or transverse-linear
low Smith term. -/
theorem conformalDegreeTwoFace_no_strictLow
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) :
    (∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.conformalDegreeTwoFace,
      ¬ IsPureLongitudinalSmithPattern e ∧
      ¬ IsLowNegativeFirstSmithPattern e ∧
      ¬ IsLowNegativeSecondSmithPattern e) := by
  intro e he
  have hdeg := T.conformalDegreeTwoFace_projected_degree_two e he
  constructor
  · intro hpure
    rcases hpure with ⟨hb, hc, hd⟩
    omega
  constructor
  · intro hfirst
    rcases hfirst with ⟨hb, hc, hd⟩
    omega
  · intro hsecond
    rcases hsecond with ⟨hb, hc, hd⟩
    omega

/-- The conformal initial form retains the full `w`-linear longitudinal
coefficient polynomial, since that pattern has conformal degree exactly two. -/
theorem conformalDegreeTwoFace_wLinearCoefficient
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) :
    longitudinalCoefficientPolynomial 0 0 1 T.conformalDegreeTwoFace =
      longitudinalCoefficientPolynomial 0 0 1 T.specialFiber := by
  ext a
  rw [coeff_longitudinalCoefficientPolynomial,
    coeff_longitudinalCoefficientPolynomial]
  unfold conformalDegreeTwoFace
  rw [HC4.Polynomial.coeff_initialForm]
  have hw :
      Finsupp.weight terminalQuadraticNegativeWeight
          ((smithTransverseExponent 0 0 1).cons a) = -2 := by
    rw [terminalQuadraticNegativeWeight_finsupp]
    simp [smithTransverseExponent]
  simp [hw]

/-- The conformal face retains the marked exact collision `0 ~ e₀`.  The first
three gradient components vanish on the longitudinal axis; the fourth is the
original `w`-linear coefficient polynomial and hence has equal values at the
two marked points. -/
theorem conformalDegreeTwoFace_exactAxisCollision
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity) :
    HasExactGradientCollision
      T.conformalDegreeTwoFace
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have hnoFace := T.conformalDegreeTwoFace_no_strictLow
  have hpure :
      longitudinalCoefficientPolynomial 0 0 0 T.conformalDegreeTwoFace = 0 := by
    by_contra hne
    have he :=
      (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        T.conformalDegreeTwoFace ⟨0, 0, 0⟩).mp hne
    exact (hnoFace ⟨0, 0, 0⟩ he).1 ⟨rfl, rfl, rfl⟩
  have hpureAt :
      longitudinalCoefficientPolynomialAt 0 T.conformalDegreeTwoFace = 0 := by
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hpure
  have hfirst :
      longitudinalCoefficientPolynomial 0 1 0 T.conformalDegreeTwoFace = 0 := by
    by_contra hne
    have he :=
      (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        T.conformalDegreeTwoFace ⟨0, 1, 0⟩).mp hne
    exact (hnoFace ⟨0, 1, 0⟩ he).2.1 ⟨rfl, rfl, rfl⟩
  have hsecond :
      longitudinalCoefficientPolynomial 1 0 0 T.conformalDegreeTwoFace = 0 := by
    by_contra hne
    have he :=
      (longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        T.conformalDegreeTwoFace ⟨1, 0, 0⟩).mp hne
    exact (hnoFace ⟨1, 0, 0⟩ he).2.2 ⟨rfl, rfl, rfl⟩
  have hw := T.conformalDegreeTwoFace_wLinearCoefficient
  have hcoll := T.specialFiber_exactCollision
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
  fin_cases i
  · unfold mvGradientComponentAt
    rw [eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative,
      eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
    rw [longitudinalAxisRestriction_eq_coefficient_zero, hpureAt]
    simp
  · unfold mvGradientComponentAt
    rw [eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single,
      eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using congrArg (Polynomial.eval 0) hsecond
  · unfold mvGradientComponentAt
    rw [eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single,
      eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using congrArg (Polynomial.eval 0) hfirst
  · have hcoll3 := hcoll (3 : Fin 4)
    rw [hzeroPoint, haxisPoint] at hcoll3
    unfold mvGradientComponentAt at hcoll3 ⊢
    rw [eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single,
      eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    rw [hw]
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hcoll3

/-- At zero clock, absence of only the three strict low Smith patterns is enough
to construct an honest one-zero associated-graded collision.  A `w`-linear
term is harmless and is retained in the degree-two face. -/
theorem conformalDegreeTwoFace_associatedGradedCollisionData_of_source_rawDefect_eq_zero
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity)
    (hzero : state.rawDefect = 0)
    (hno : T.HasNoStrictLowSmithPatterns) :
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
        (MvPolynomial.rename rho T.conformalDegreeTwoFace) := by
    have h := integralWeightedHomogeneous_rename_perm
      T.conformalDegreeTwoFace_positiveHomogeneous rho
    rw [hweight] at h
    exact h
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere
      T.conformalDegreeTwoFace := by
    unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    exact T.conformalDegreeTwoFace_hessianDeterminant_eq_one hzero hno
  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho T.conformalDegreeTwoFace) :=
    isPolynomialMongeAmpere_rename_perm rho hMA
  have hendpoint : CertifiedTerminalDirectJumpEndpoint
      T.conformalDegreeTwoFace :=
    .permuted rho
      (.oneZero 2 1 (by norm_num) (by norm_num) hhomRenamed hMARenamed)
  exact ⟨{
    fibre := T.conformalDegreeTwoFace
    leftPoint := fun _ : Fin 4 => (0 : K)
    rightPoint := coordinateAxisPoint (K := K) (0 : Fin 4)
    distinct := T.specialFiber_markedPoints_distinct
    exactCollision := T.conformalDegreeTwoFace_exactAxisCollision
    endpoint := hendpoint
  }⟩

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

end

end HC4.Valuation