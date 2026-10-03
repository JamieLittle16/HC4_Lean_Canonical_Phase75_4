import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamSourceSpread
import Mathlib.Tactic

/-!
# G12: the final seam has genuine longitudinal--transverse nonlinear coupling

G8 rules out the extreme case in which all nonlinear represented-source
support lies on the distinguished longitudinal axis.  In fact the same
axis-Hessian argument proves a stronger statement.

Suppose no nonlinear represented-source monomial contains both coordinate
`0` and a transverse coordinate.  Then every transverse-linear longitudinal
coefficient fibre has degree at most one: a coefficient of longitudinal
degree at least two would itself reconstruct such a nonlinear coupled
monomial.  Exact collision forces the two factors `X(X-1)`, so all those
coefficient fibres vanish.  Hence the entire mixed first row of the
axis-restricted Hessian vanishes.

Determinant one then makes the longitudinal Hessian entry a unit in `K[X]`,
hence a nonzero constant.  The normalized longitudinal gradient collision
forces that constant to vanish, a contradiction.

Therefore every final seam contains an actual nonlinear source monomial with
positive longitudinal exponent and positive transverse exponent.  This is
strictly sharper than the G10 spread alternative and is exactly the source
shape needed by the first-contact / reverse-Rees closing mechanisms.

No progress theorem, terminal weight, repair transition, cocharacter, or JC2
input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- An actual nonlinear represented-source monomial coupling the marked
longitudinal coordinate to at least one transverse coordinate. -/
def HasLongitudinalTransverseNonlinearCoupling
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∃ d ∈ T.representedSpecialFiber.support,
    3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (0 : Fin 4) ∧
      ∃ j : Fin 3, 0 < d j.succ

/-- Absence of a longitudinal--transverse nonlinear coupling bounds every
transverse-linear longitudinal coefficient polynomial by degree one. -/
theorem represented_transverseLinear_natDegree_le_one_of_noLongitudinalCoupling
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hnocouple : ¬ T.HasLongitudinalTransverseNonlinearCoupling)
    (j : Fin 3) :
    (longitudinalCoefficientPolynomialAt
      (Finsupp.single j 1) T.representedSpecialFiber).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
  by_contra hne
  let d : Fin 4 →₀ ℕ := (Finsupp.single j 1).cons n
  have hd : d ∈ T.representedSpecialFiber.support := by
    exact MvPolynomial.mem_support_iff.mpr (by simpa [d] using hne)
  have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
    dsimp [d]
    fin_cases j <;>
      simp [HC4.Polynomial.ordinaryDegree4] <;>
      omega
  have hd0 : 0 < d (0 : Fin 4) := by
    dsimp [d]
    simp
    omega
  have hdj : 0 < d j.succ := by
    dsimp [d]
    rw [Finsupp.cons_succ]
    simp
  exact hnocouple ⟨d, hd, hdeg, hd0, j, hdj⟩

/-- Exact collision then kills every transverse-linear longitudinal
coefficient fibre. -/
theorem represented_transverseLinearCoefficient_eq_zero_of_noLongitudinalCoupling
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hnocouple : ¬ T.HasLongitudinalTransverseNonlinearCoupling)
    (j : Fin 3) :
    longitudinalCoefficientPolynomialAt
      (Finsupp.single j 1) T.representedSpecialFiber = 0 := by
  let A :=
    longitudinalCoefficientPolynomialAt
      (Finsupp.single j 1) T.representedSpecialFiber
  have hdeg : A.natDegree ≤ 1 := by
    simpa [A] using
      T.represented_transverseLinear_natDegree_le_one_of_noLongitudinalCoupling
        hnocouple j
  have hdvd :
      Polynomial.X * (Polynomial.X - Polynomial.C (1 : K)) ∣ A := by
    have h :=
      X_mul_X_sub_one_dvd_longitudinalCoefficient_single_of_collision
        j T.representedSpecialFiber
        T.finalSeamData.exactCollision
        (T.represented_gradientAtZero_eq_zero j.succ)
    simpa [A] using h
  by_contra hA
  rcases exists_twoEndpointResidual_natDegree_lt A hA hdvd with
    ⟨B, _hB, _hfactor, hdegree⟩
  omega

/-- Hence every mixed longitudinal/transverse Hessian entry vanishes after
restriction to the marked axis. -/
theorem represented_axis_mixedHessian_zero_of_noLongitudinalCoupling
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hnocouple : ¬ T.HasLongitudinalTransverseNonlinearCoupling)
    (j : Fin 3) :
    longitudinalAxisRestriction
      (HC4.Polynomial.hessian T.representedSpecialFiber
        (0 : Fin 4) j.succ) = 0 := by
  rw [longitudinalAxisRestriction_hessian_zero_succ]
  rw [T.represented_transverseLinearCoefficient_eq_zero_of_noLongitudinalCoupling
    hnocouple j]
  simp

/-- Generic final-seam contradiction once the mixed first axis-Hessian row is
zero.  This is the matrix/algebraic core of G8 isolated from its stronger
support hypothesis. -/
theorem impossible_of_representedAxisMixedHessianZero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hmixed :
      ∀ j : Fin 3,
        longitudinalAxisRestriction
          (HC4.Polynomial.hessian T.representedSpecialFiber
            (0 : Fin 4) j.succ) = 0) :
    False := by
  let H := T.representedAxisHessian
  have h1 : H 0 (1 : Fin 4) = 0 := by
    simpa [H, representedAxisHessian,
      longitudinalAxisRestrictionRingHom_apply] using hmixed (0 : Fin 3)
  have h2 : H 0 (2 : Fin 4) = 0 := by
    simpa [H, representedAxisHessian,
      longitudinalAxisRestrictionRingHom_apply] using hmixed (1 : Fin 3)
  have h3 : H 0 (3 : Fin 4) = 0 := by
    simpa [H, representedAxisHessian,
      longitudinalAxisRestrictionRingHom_apply] using hmixed (2 : Fin 3)

  have hadj :=
    congrArg
      (fun M : Matrix (Fin 4) (Fin 4) (Polynomial K) => M 0 0)
      (Matrix.mul_adjugate H)
  have hdet : H.det = 1 := by
    simpa [H] using T.representedAxisHessian_det_one
  have hmul : H 0 0 * H.adjugate 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3, hdet] using hadj
  have hunit : IsUnit (H 0 0) := by
    rw [isUnit_iff_exists_inv]
    exact ⟨H.adjugate 0 0, hmul⟩
  rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hc, hC⟩
  have hcne : c ≠ 0 := hc.ne_zero
  have h00 : H 0 0 = Polynomial.C c := hC.symm

  have hsecond :
      (longitudinalAxisRestriction
        T.representedSpecialFiber).derivative.derivative =
        Polynomial.C c := by
    have haxis :
        longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.representedSpecialFiber
              (0 : Fin 4) (0 : Fin 4)) =
          Polynomial.C c := by
      simpa [H, representedAxisHessian,
        longitudinalAxisRestrictionRingHom_apply] using h00
    change
      longitudinalAxisRestriction
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv (0 : Fin 4)
              T.representedSpecialFiber)) =
        Polynomial.C c at haxis
    rw [longitudinalAxisRestriction_pderiv_zero,
      longitudinalAxisRestriction_pderiv_zero] at haxis
    exact haxis

  let G := (longitudinalAxisRestriction T.representedSpecialFiber).derivative
  have hGderiv : G.derivative = Polynomial.C c := by
    simpa [G] using hsecond
  have hconstDeriv :
      (G - Polynomial.C c * Polynomial.X).derivative = 0 := by
    rw [Polynomial.derivative_sub, hGderiv,
      Polynomial.derivative_C_mul_X]
    simp
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hconstDeriv
  have hevalConst :
      Polynomial.eval (0 : K) (G - Polynomial.C c * Polynomial.X) =
        Polynomial.eval (1 : K) (G - Polynomial.C c * Polynomial.X) := by
    rw [hconst]
    simp
  have hevalConst' :
      Polynomial.eval 0 G = Polynomial.eval 1 G - c := by
    simpa using hevalConst

  have hcoll := T.finalSeamData.exactCollision (0 : Fin 4)
  rw [eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative,
    eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative] at hcoll
  have hgrad : Polynomial.eval 0 G = Polynomial.eval 1 G := by
    simpa [G] using hcoll
  have hc0 : c = 0 := by
    have hsub :
        Polynomial.eval 1 G - c = Polynomial.eval 1 G := by
      exact hevalConst'.symm.trans hgrad
    exact sub_eq_self.mp hsub
  exact hcne hc0

/-- **G12 longitudinal-coupling theorem.**

Every zero-clock strict-low final seam contains an actual nonlinear represented
source monomial coupling coordinate `0` to a transverse coordinate. -/
theorem hasLongitudinalTransverseNonlinearCoupling
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.HasLongitudinalTransverseNonlinearCoupling := by
  by_contra hnocouple
  apply T.impossible_of_representedAxisMixedHessianZero
  intro j
  exact T.represented_axis_mixedHessian_zero_of_noLongitudinalCoupling
    hnocouple j

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
