import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamOrderTransfer
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalStructure
import Mathlib.Tactic

/-!
# G8: longitudinal nonlinear confinement is impossible at the final seam

This file isolates a genuinely contradictory terminal class at the zero-clock
strict-low seam.

Assume every represented source monomial of ordinary degree at least three is
supported on the distinguished longitudinal coordinate `0`.  For each
transverse coordinate, the corresponding longitudinal coefficient polynomial
can then have degree at most one: a coefficient in longitudinal degree at
least two would reconstruct a nonlinear source monomial using both coordinate
`0` and that transverse coordinate.

The normalized exact collision already proves that

    X (X - 1)

divides every transverse-linear longitudinal coefficient polynomial.  A
nonzero polynomial of degree at most one cannot have that degree-two factor.
Hence every mixed `(0,j)` Hessian entry vanishes after restriction to the
longitudinal axis.

The represented Hessian determinant is exactly one.  The standard adjugate
identity therefore makes the longitudinal axis-Hessian entry `H₀₀` a unit in
`K[X]`, hence a nonzero constant.  But then the longitudinal gradient changes
by that nonzero constant between the collision endpoints `0` and `1`,
contradicting the exact collision.

Only generic polynomial/matrix algebra is reused from the mature
positive-clock proof.  No positive-clock carrier, progress theorem, repair
transition, source-complexity interpretation, cocharacter, or JC2 input is
used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Every nonlinear represented-source monomial is supported on coordinate
`0`.  Quadratic support is deliberately unrestricted. -/
def RepresentedNonlinearSupportLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∀ d ∈ T.representedSpecialFiber.support,
    3 ≤ HC4.Polynomial.ordinaryDegree4 d →
      d (1 : Fin 4) = 0 ∧
      d (2 : Fin 4) = 0 ∧
      d (3 : Fin 4) = 0

/-- Under longitudinal nonlinear confinement, every transverse-linear
longitudinal coefficient fibre has degree at most one. -/
theorem represented_transverseLinear_natDegree_le_one_of_nonlinearLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal)
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
  have haxis := hconf d hd hdeg
  have hjone : d j.succ = 1 := by
    dsimp [d]
    rw [Finsupp.cons_succ]
    simp
  fin_cases j
  · have hjzero : d (1 : Fin 4) = 0 := haxis.1
    exact (by omega)
  · have hjzero : d (2 : Fin 4) = 0 := haxis.2.1
    exact (by omega)
  · have hjzero : d (3 : Fin 4) = 0 := haxis.2.2
    exact (by omega)

/-- The represented blocker retains the normalized zero-left gradient on the
same literal special fibre used by the final seam. -/
theorem represented_gradientAtZero_eq_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    MvPolynomial.eval
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (MvPolynomial.pderiv i T.representedSpecialFiber) = 0 := by
  have hraw :=
    T.terminal.blocker.blocker.aligned.rawSpecialFiber_axisData
  rcases hraw with ⟨_hcoll, hzero, _hvalue⟩
  have hF :
      T.representedSpecialFiber =
        T.terminal.blocker.blocker.aligned.endpoint.rawSpecialFiber := by
    simp [representedSpecialFiber,
      AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
      T.terminal.blocker.family_eq]
  simpa [hF] using hzero i

/-- Exact collision plus the degree bound forces every transverse-linear
coefficient fibre to vanish identically. -/
theorem represented_transverseLinearCoefficient_eq_zero_of_nonlinearLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal)
    (j : Fin 3) :
    longitudinalCoefficientPolynomialAt
      (Finsupp.single j 1) T.representedSpecialFiber = 0 := by
  let A :=
    longitudinalCoefficientPolynomialAt
      (Finsupp.single j 1) T.representedSpecialFiber
  have hdeg : A.natDegree ≤ 1 := by
    simpa [A] using
      T.represented_transverseLinear_natDegree_le_one_of_nonlinearLongitudinal
        hconf j
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

/-- Every represented mixed longitudinal/transverse Hessian entry vanishes on
the distinguished axis. -/
theorem represented_axis_mixedHessian_zero_of_nonlinearLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal)
    (j : Fin 3) :
    longitudinalAxisRestriction
      (HC4.Polynomial.hessian T.representedSpecialFiber
        (0 : Fin 4) j.succ) = 0 := by
  rw [longitudinalAxisRestriction_hessian_zero_succ]
  rw [T.represented_transverseLinearCoefficient_eq_zero_of_nonlinearLongitudinal
    hconf j]
  simp

/-- Axis-restricted Hessian of the represented determinant-one source. -/
noncomputable def representedAxisHessian
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian T.representedSpecialFiber)

/-- The represented axis Hessian still has determinant exactly one. -/
theorem representedAxisHessian_det_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.representedAxisHessian.det = 1 := by
  let phi := longitudinalAxisRestrictionRingHom (K := K)
  let H := HC4.Polynomial.hessian T.representedSpecialFiber
  have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
  calc
    T.representedAxisHessian.det = (phi.mapMatrix H).det := by rfl
    _ = phi H.det := hmap.symm
    _ = phi (HC4.Polynomial.hessianDeterminant
        T.representedSpecialFiber) := by rfl
    _ = phi 1 := by rw [T.finalSeamData.representedHessianDetOne]
    _ = 1 := map_one phi

/-- Under longitudinal nonlinear confinement the first represented axis
Hessian row is zero away from its longitudinal entry. -/
theorem representedAxisHessian_row_zero_of_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal)
    (i : Fin 4) (hi : i ≠ 0) :
    T.representedAxisHessian 0 i = 0 := by
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    exact False.elim (hi rfl)
  · intro _hi
    simpa [representedAxisHessian,
      longitudinalAxisRestrictionRingHom_apply] using
      T.represented_axis_mixedHessian_zero_of_nonlinearLongitudinal hconf j

/-- Determinant one plus the zero mixed row makes the longitudinal represented
axis-Hessian entry a unit in `K[X]`. -/
theorem representedAxisHessian_zero_zero_isUnit_of_nonlinearLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal) :
    IsUnit (T.representedAxisHessian 0 0) := by
  let H := T.representedAxisHessian
  have hadj :=
    congrArg
      (fun M : Matrix (Fin 4) (Fin 4) (Polynomial K) => M 0 0)
      (Matrix.mul_adjugate H)
  have h1 : H 0 (1 : Fin 4) = 0 := by
    exact T.representedAxisHessian_row_zero_of_ne_zero hconf 1 (by decide)
  have h2 : H 0 (2 : Fin 4) = 0 := by
    exact T.representedAxisHessian_row_zero_of_ne_zero hconf 2 (by decide)
  have h3 : H 0 (3 : Fin 4) = 0 := by
    exact T.representedAxisHessian_row_zero_of_ne_zero hconf 3 (by decide)
  have hdet : H.det = 1 := by
    simpa [H] using T.representedAxisHessian_det_one
  have hmul : H 0 0 * H.adjugate 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3, hdet] using hadj
  rw [isUnit_iff_exists_inv]
  exact ⟨H.adjugate 0 0, hmul⟩

/-- Hence the represented longitudinal axis Hessian is a nonzero constant. -/
theorem representedAxisHessian_zero_zero_eq_C_nonzero_of_nonlinearLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal) :
    ∃ c : K, c ≠ 0 ∧
      T.representedAxisHessian 0 0 = Polynomial.C c := by
  have hunit :=
    T.representedAxisHessian_zero_zero_isUnit_of_nonlinearLongitudinal hconf
  rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hc, hC⟩
  exact ⟨c, hc.ne_zero, hC.symm⟩

/-- **G8 direct contradiction.**

A zero-clock strict-low singular terminal cannot have all represented
nonlinear support confined to the distinguished longitudinal axis. -/
theorem impossible_of_representedNonlinearSupportLongitudinal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hconf : T.RepresentedNonlinearSupportLongitudinal) :
    False := by
  rcases
      T.representedAxisHessian_zero_zero_eq_C_nonzero_of_nonlinearLongitudinal
        hconf with
    ⟨c, hc, h00⟩
  have hsecond :
      (longitudinalAxisRestriction
        T.representedSpecialFiber).derivative.derivative =
        Polynomial.C c := by
    have haxis :
        longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.representedSpecialFiber
              (0 : Fin 4) (0 : Fin 4)) =
          Polynomial.C c := by
      simpa [representedAxisHessian,
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
  exact hc hc0

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
