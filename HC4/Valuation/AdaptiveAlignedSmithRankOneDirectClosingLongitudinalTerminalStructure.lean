import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalFrontier
import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import HC4.RationalRigidity.ReducedFractionAssembly
import Mathlib.Tactic

/-!
# Longitudinal canonical terminal structure

The canonical longitudinal terminal ray has source weights

    (0, 2*Delta, 2*Delta, 2*Delta).

At direct closing `j = Delta`, exact first-contact arithmetic therefore forces
any monomial surviving in the terminal fibre to have total transverse degree
exactly `0` or `2`.  In particular there are no transverse-linear terms.

That support statement is precisely what the existing longitudinal-axis
restriction machinery needs: every mixed `(0,i)` Hessian entry vanishes on
the distinguished axis.  Restricting the Monge--Ampere determinant to that
axis and expanding the adjugate identity then shows that the longitudinal
`(0,0)` Hessian entry is a unit in `K[X]`, hence a nonzero constant.

This is the structural input for the final direct collision contradiction.
No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Total degree in the three transverse coordinates. -/
def directClosingLongitudinalTransverseDegree (d : Fin 4 →₀ ℕ) : ℕ :=
  d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4)

/-- The canonical longitudinal square weight is exactly twice the defect
multiplied by total transverse degree. -/
theorem directClosingCanonicalSquareWeight_longitudinal
    (Delta : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (directClosingCanonicalSquareWeight Delta (0 : Fin 4)) d =
      2 * Delta * directClosingLongitudinalTransverseDegree d := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [directClosingCanonicalSquareWeight,
      directClosingLongitudinalTransverseDegree]
    ring
  · intro i
    simp

/-- For the original closing family, the exact parameter order of any
supported coefficient is either zero or at least the first positive actual
source-layer order. -/
theorem sourceCoefficientOrder_eq_zero_or_firstActual_le
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ C.family.support) :
    smithFamilyCoefficientParameterOrder C.family d hd = 0 ∨
      C.firstActualLayerOrder ≤
        smithFamilyCoefficientParameterOrder C.family d hd := by
  let q := smithFamilyCoefficientParameterOrder C.family d hd
  by_cases hq0 : q = 0
  · exact Or.inl (by simpa [q] using hq0)
  · right
    by_contra hnot
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqlt : q < C.firstActualLayerOrder := Nat.lt_of_not_ge hnot
    have hzero := familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
      C.family C.hasPositiveActualParameterLayer hqpos
        (by simpa [firstActualLayerOrder, q] using hqlt)
    have hc : MvPolynomial.coeff d C.family ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hcoeff : (MvPolynomial.coeff d C.family).coeff q ≠ 0 := by
      have h := polynomialParameterOrder_coeff_ne_zero
        (MvPolynomial.coeff d C.family) hc
      simpa [q, smithFamilyCoefficientParameterOrder] using h
    have hz := congrArg (MvPolynomial.coeff d) hzero
    rw [familyParameterLayer_coeff] at hz
    simp only [MvPolynomial.coeff_zero] at hz
    exact hcoeff hz

namespace DirectClosingLongitudinalCanonicalTerminalData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}

/-- Every nonzero terminal monomial has transverse degree exactly `0` or `2`.
The two cases correspond respectively to a coefficient arriving at parameter
order `Delta`, or a special-fibre coefficient at parameter order zero. -/
theorem terminal_transverseDegree_eq_zero_or_two
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    {d : Fin 4 →₀ ℕ}
    (hdT : d ∈ T.fibre.support) :
    directClosingLongitudinalTransverseDegree d = 0 ∨
      directClosingLongitudinalTransverseDegree d = 2 := by
  let D := C.directClosingLongitudinalSquareSource S.fresh
  let L := S.integrality.toFirstContactLattice heq
  have hcoeff : MvPolynomial.coeff d T.fibre ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdT
  rcases T.sourceContactLevel_of_coeff_ne_zero hcoeff with ⟨hdD, hlevel⟩
  have hdC : d ∈ C.family.support := by
    simpa [D, directClosingLongitudinalSquareSource] using hdD
  let q := smithFamilyCoefficientParameterOrder C.family d hdC
  have hqcases := C.sourceCoefficientOrder_eq_zero_or_firstActual_le hdC
  have hDelta : 0 < B.aligned.endpoint.defect := by
    rw [← heq]
    exact C.firstActualLayerOrder_pos
  have hlevel' :
      4 * q +
          2 * B.aligned.endpoint.defect *
            directClosingLongitudinalTransverseDegree d =
        4 * B.aligned.endpoint.defect := by
    simpa [D, L,
      DirectClosingCanonicalSquareIntegralityData.toFirstContactLattice,
      directClosingCanonicalSquareRamification,
      directClosingCanonicalSquareCommonLevel,
      directClosingLongitudinalSquareSource,
      directClosingCanonicalSquareWeight_longitudinal,
      q] using hlevel
  rcases hqcases with hq0 | hqge
  · right
    have hq0' : q = 0 := by simpa [q] using hq0
    nlinarith
  · left
    have hqge' : B.aligned.endpoint.defect ≤ q := by
      rw [← heq]
      simpa [q] using hqge
    nlinarith

/-- The longitudinal coefficient fibre of every transverse-linear monomial
is zero on the terminal fibre. -/
theorem terminal_transverseLinearCoefficientPolynomial_eq_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j : Fin 3) :
    longitudinalCoefficientPolynomialAt (Finsupp.single j 1) T.fibre = 0 := by
  apply Polynomial.ext
  intro a
  rw [Polynomial.coeff_zero]
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
  by_contra hne
  let d : Fin 4 →₀ ℕ := (Finsupp.single j 1).cons a
  have hd : d ∈ T.fibre.support := by
    apply MvPolynomial.mem_support_iff.mpr
    simpa [d] using hne
  have hdeg := S.terminal_transverseDegree_eq_zero_or_two T hd
  have hdeg1 : directClosingLongitudinalTransverseDegree d = 1 := by
    unfold directClosingLongitudinalTransverseDegree
    dsimp [d]
    rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
      show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
      show (3 : Fin 4) = (2 : Fin 3).succ by rfl]
    rw [Finsupp.cons_succ, Finsupp.cons_succ, Finsupp.cons_succ]
    fin_cases j <;> simp
  omega

/-- Every mixed longitudinal/transverse Hessian entry vanishes after
restriction to the distinguished axis. -/
theorem terminal_axis_mixedHessian_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j : Fin 3) :
    longitudinalAxisRestriction
        (HC4.Polynomial.hessian T.fibre (0 : Fin 4) j.succ) = 0 := by
  rw [longitudinalAxisRestriction_hessian_zero_succ]
  rw [S.terminal_transverseLinearCoefficientPolynomial_eq_zero T j]
  simp

/-- Axis-restricted Hessian matrix of the terminal fibre. -/
noncomputable def terminalAxisHessian
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq)) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian T.fibre)

/-- The axis-restricted Hessian still has determinant one. -/
theorem terminalAxisHessian_det_one
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq)) :
    (S.terminalAxisHessian T).det = 1 := by
  let phi := longitudinalAxisRestrictionRingHom (K := K)
  let H := HC4.Polynomial.hessian T.fibre
  have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
  have hMA := T.mongeAmpere
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere at hMA
  calc
    (S.terminalAxisHessian T).det = (phi.mapMatrix H).det := by rfl
    _ = phi H.det := hmap.symm
    _ = phi (HC4.Polynomial.hessianDeterminant T.fibre) := by rfl
    _ = phi 1 := by rw [hMA]
    _ = 1 := map_one phi

/-- The first row of the axis Hessian is zero away from its longitudinal
entry. -/
theorem terminalAxisHessian_row_zero_of_ne_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (i : Fin 4) (hi : i ≠ 0) :
    S.terminalAxisHessian T 0 i = 0 := by
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    exact False.elim (hi rfl)
  · intro _hi
    simpa [terminalAxisHessian,
      longitudinalAxisRestrictionRingHom_apply] using
      S.terminal_axis_mixedHessian_zero T j

/-- The longitudinal `(0,0)` axis-Hessian entry is a unit in `K[X]`. -/
theorem terminalAxisHessian_zero_zero_isUnit
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq)) :
    IsUnit (S.terminalAxisHessian T 0 0) := by
  let H := S.terminalAxisHessian T
  have hadj := congrArg (fun M : Matrix (Fin 4) (Fin 4) (Polynomial K) => M 0 0)
    (Matrix.mul_adjugate H)
  have h1 : H 0 (1 : Fin 4) = 0 := by
    exact S.terminalAxisHessian_row_zero_of_ne_zero T 1 (by decide)
  have h2 : H 0 (2 : Fin 4) = 0 := by
    exact S.terminalAxisHessian_row_zero_of_ne_zero T 2 (by decide)
  have h3 : H 0 (3 : Fin 4) = 0 := by
    exact S.terminalAxisHessian_row_zero_of_ne_zero T 3 (by decide)
  have hdet : H.det = 1 := by
    simpa [H] using S.terminalAxisHessian_det_one T
  have hmul : H 0 0 * H.adjugate 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3, hdet] using hadj
  rw [isUnit_iff_exists_inv]
  exact ⟨H.adjugate 0 0, hmul⟩

/-- Consequently the longitudinal axis Hessian is a nonzero constant
polynomial. -/
theorem terminalAxisHessian_zero_zero_eq_C_nonzero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq)) :
    ∃ c : K, c ≠ 0 ∧
      S.terminalAxisHessian T 0 0 = Polynomial.C c := by
  have hunit := S.terminalAxisHessian_zero_zero_isUnit T
  rcases Polynomial.isUnit_iff.mp hunit with ⟨c, hc, hC⟩
  exact ⟨c, hc.ne_zero, hC.symm⟩

end DirectClosingLongitudinalCanonicalTerminalData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
