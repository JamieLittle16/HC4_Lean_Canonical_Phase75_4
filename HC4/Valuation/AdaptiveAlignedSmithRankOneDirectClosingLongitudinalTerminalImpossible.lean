import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalStructure
import HC4.Newton.PositiveWeightTriangularEvaluation
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Longitudinal canonical terminal contact is impossible

The previous module proves that every monomial in the longitudinal canonical
terminal fibre has transverse degree `0` or `2`, and that the `(0,0)` entry of
its axis-restricted Hessian is a nonzero constant.

This file closes that terminal branch directly.

For a transverse coordinate `j`, the polynomial `pderiv j F` is homogeneous
of degree one for the transverse weight `(0,1,1,1)`.  Weighted Euler therefore
identifies its value at the right collision point with the transverse Hessian
row applied to the transverse displacement.  Every second transverse
derivative has transverse degree zero, so its value depends only on the
longitudinal coordinate and hence agrees with the corresponding entry of the
axis Hessian at `x₀ = -1`.

Thus the vector obtained from the right point by replacing its longitudinal
coordinate by zero lies in the kernel of the axis Hessian evaluated at `-1`.
That Hessian has determinant one, so the vector vanishes.  The right point is
therefore exactly `-e₀`.

Finally the longitudinal axis Hessian is the nonzero constant `c`.  Hence the
longitudinal gradient changes by `c` between `x₀=-1` and `x₀=0`, contradicting
the exact gradient collision.

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

/-- The elementary transverse weight: zero on the marked longitudinal
coordinate and one on all three transverse coordinates. -/
def directClosingLongitudinalTransverseWeight : Fin 4 → ℕ :=
  Fin.cases 0 (fun _ : Fin 3 => 1)

/-- Its weighted exponent degree is exactly the explicit transverse degree
used by the longitudinal terminal structure module. -/
theorem directClosingLongitudinalTransverseWeight_degree
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight directClosingLongitudinalTransverseWeight d =
      directClosingLongitudinalTransverseDegree d := by
  have hw0 : directClosingLongitudinalTransverseWeight (0 : Fin 4) = 0 := by
    rfl
  have hw1 : directClosingLongitudinalTransverseWeight (1 : Fin 4) = 1 := by
    rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl]
    rfl
  have hw2 : directClosingLongitudinalTransverseWeight (2 : Fin 4) = 1 := by
    rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl]
    rfl
  have hw3 : directClosingLongitudinalTransverseWeight (3 : Fin 4) = 1 := by
    rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl]
    rfl
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four, hw0, hw1, hw2, hw3]
    simp [directClosingLongitudinalTransverseDegree]
  · intro i
    simp

/-- Adding one transverse variable raises transverse degree by exactly one. -/
theorem directClosingLongitudinalTransverseDegree_add_single_succ
    (d : Fin 4 →₀ ℕ) (j : Fin 3) :
    directClosingLongitudinalTransverseDegree
        (d + Finsupp.single j.succ 1) =
      directClosingLongitudinalTransverseDegree d + 1 := by
  unfold directClosingLongitudinalTransverseDegree
  fin_cases j <;> simp [Finsupp.add_apply] <;> omega

namespace DirectClosingLongitudinalCanonicalTerminalData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}

/-- Every transverse gradient component of the terminal fibre is homogeneous
of transverse degree one for the weight `(0,1,1,1)`. -/
theorem terminal_transverseGradient_isWeightedHomogeneous
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j : Fin 3) :
    (MvPolynomial.pderiv j.succ T.fibre).IsWeightedHomogeneous
      directClosingLongitudinalTransverseWeight 1 := by
  intro d hd
  have hsourceCoeff :
      MvPolynomial.coeff (d + Finsupp.single j.succ 1) T.fibre ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) j.succ T.fibre d] at hd
    intro hz
    apply hd
    simp [hz]
  have hsourceSupport :
      d + Finsupp.single j.succ 1 ∈ T.fibre.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hdeg := S.terminal_transverseDegree_eq_zero_or_two T hsourceSupport
  have hadd :=
    directClosingLongitudinalTransverseDegree_add_single_succ d j
  have hddeg : directClosingLongitudinalTransverseDegree d = 1 := by
    rcases hdeg with hzero | htwo
    · rw [hadd] at hzero
      omega
    · rw [hadd] at htwo
      omega
  rw [directClosingLongitudinalTransverseWeight_degree]
  exact hddeg

/-- Two transverse derivatives of the terminal fibre have transverse degree
zero on every supported monomial. -/
theorem terminal_transverseSecondDerivative_support_degree_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j k : Fin 3)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈
      (MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ T.fibre)).support) :
    directClosingLongitudinalTransverseDegree d = 0 := by
  have hcoeff2 :
      MvPolynomial.coeff d
        (MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv j.succ T.fibre)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcoeff1 :
      MvPolynomial.coeff (d + Finsupp.single k.succ 1)
        (MvPolynomial.pderiv j.succ T.fibre) ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) k.succ
      (MvPolynomial.pderiv j.succ T.fibre) d] at hcoeff2
    intro hz
    apply hcoeff2
    simp [hz]
  have hsourceCoeff :
      MvPolynomial.coeff
        ((d + Finsupp.single k.succ 1) + Finsupp.single j.succ 1)
        T.fibre ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) j.succ T.fibre
      (d + Finsupp.single k.succ 1)] at hcoeff1
    intro hz
    apply hcoeff1
    simp [hz]
  have hsourceSupport :
      (d + Finsupp.single k.succ 1) + Finsupp.single j.succ 1 ∈
        T.fibre.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hdeg := S.terminal_transverseDegree_eq_zero_or_two T hsourceSupport
  have hk :=
    directClosingLongitudinalTransverseDegree_add_single_succ d k
  have hj :=
    directClosingLongitudinalTransverseDegree_add_single_succ
      (d + Finsupp.single k.succ 1) j
  rcases hdeg with hzero | htwo
  · rw [hj, hk] at hzero
    omega
  · rw [hj, hk] at htwo
    omega

/-- A polynomial supported only in transverse degree zero has the same value
at any two points with the same longitudinal coordinate. -/
theorem eval_eq_of_support_transverseDegree_zero
    (P : MvPolynomial (Fin 4) K)
    (hsupp :
      ∀ d ∈ P.support,
        directClosingLongitudinalTransverseDegree d = 0)
    (p q : Fin 4 → K)
    (hzero : p (0 : Fin 4) = q (0 : Fin 4)) :
    MvPolynomial.eval p P = MvPolynomial.eval q P := by
  rw [MvPolynomial.as_sum P]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply eval_monomial_eq_of_eq_on_exponent_support
  intro i hi
  fin_cases i
  · exact hzero
  · have hdeg := hsupp d hd
    unfold directClosingLongitudinalTransverseDegree at hdeg
    exfalso
    apply hi
    change d (1 : Fin 4) = 0
    omega
  · have hdeg := hsupp d hd
    unfold directClosingLongitudinalTransverseDegree at hdeg
    exfalso
    apply hi
    change d (2 : Fin 4) = 0
    omega
  · have hdeg := hsupp d hd
    unfold directClosingLongitudinalTransverseDegree at hdeg
    exfalso
    apply hi
    change d (3 : Fin 4) = 0
    omega

/-- A transverse second derivative evaluated at the terminal right point is
exactly the corresponding axis-Hessian entry evaluated at `x₀=-1`. -/
theorem terminal_transverseSecondDerivative_eval_right_eq_axis
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j k : Fin 3) :
    MvPolynomial.eval T.rightPoint
        (MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv j.succ T.fibre)) =
      Polynomial.eval (-1 : K) (S.terminalAxisHessian T j.succ k.succ) := by
  let q : Fin 4 → K := Fin.cons (-1 : K) (fun _ : Fin 3 => 0)
  have heval :
      MvPolynomial.eval T.rightPoint
          (MvPolynomial.pderiv k.succ
            (MvPolynomial.pderiv j.succ T.fibre)) =
        MvPolynomial.eval q
          (MvPolynomial.pderiv k.succ
            (MvPolynomial.pderiv j.succ T.fibre)) := by
    apply eval_eq_of_support_transverseDegree_zero
    · intro d hd
      exact S.terminal_transverseSecondDerivative_support_degree_zero T j k hd
    · simpa [q] using T.rightPoint_zero
  calc
    MvPolynomial.eval T.rightPoint
        (MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv j.succ T.fibre)) =
        MvPolynomial.eval q
          (MvPolynomial.pderiv k.succ
            (MvPolynomial.pderiv j.succ T.fibre)) := heval
    _ = Polynomial.eval (-1 : K)
        (longitudinalAxisRestriction
          (MvPolynomial.pderiv k.succ
            (MvPolynomial.pderiv j.succ T.fibre))) := by
      simpa [q] using
        (eval_finCons_zero_eq_longitudinalAxisRestriction
          (MvPolynomial.pderiv k.succ
            (MvPolynomial.pderiv j.succ T.fibre)) (-1 : K))
    _ = Polynomial.eval (-1 : K)
        (S.terminalAxisHessian T j.succ k.succ) := by
      simp [terminalAxisHessian,
        longitudinalAxisRestrictionRingHom_apply,
        HC4.Polynomial.hessian_apply]

/-- The right transverse gradient vanishes, and weighted Euler identifies it
with the axis-Hessian transverse row applied to the right transverse
coordinates. -/
theorem terminal_axisHessian_transverseRow_mul_right_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq))
    (j : Fin 3) :
    Polynomial.eval (-1 : K) (S.terminalAxisHessian T j.succ (1 : Fin 4)) *
          T.rightPoint (1 : Fin 4) +
        Polynomial.eval (-1 : K) (S.terminalAxisHessian T j.succ (2 : Fin 4)) *
          T.rightPoint (2 : Fin 4) +
        Polynomial.eval (-1 : K) (S.terminalAxisHessian T j.succ (3 : Fin 4)) *
          T.rightPoint (3 : Fin 4) = 0 := by
  let P := MvPolynomial.pderiv j.succ T.fibre
  have hhom := S.terminal_transverseGradient_isWeightedHomogeneous T j
  have hleft :
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K)) P = 0 := by
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
    apply hhom.coeff_eq_zero
    simp [directClosingLongitudinalTransverseWeight]
  have hcoll := T.exactCollision j.succ
  change
    MvPolynomial.eval T.leftPoint P =
      MvPolynomial.eval T.rightPoint P at hcoll
  rw [T.leftPoint_eq_zero] at hcoll
  have hright : MvPolynomial.eval T.rightPoint P = 0 := by
    rw [← hcoll]
    exact hleft
  have heuler := hhom.sum_weight_X_mul_pderiv
  have heval := congrArg (MvPolynomial.eval T.rightPoint) heuler
  have hw0 : directClosingLongitudinalTransverseWeight (0 : Fin 4) = 0 := by
    rfl
  have hw1 : directClosingLongitudinalTransverseWeight (1 : Fin 4) = 1 := by
    rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl]
    rfl
  have hw2 : directClosingLongitudinalTransverseWeight (2 : Fin 4) = 1 := by
    rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl]
    rfl
  have hw3 : directClosingLongitudinalTransverseWeight (3 : Fin 4) = 1 := by
    rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl]
    rfl
  simp [-standardTwoZero_pderiv_two_eq_A,
    -standardTwoZero_pderiv_three_eq_C, P, Fin.sum_univ_four,
    hw0, hw1, hw2, hw3, standardTwoZeroA, standardTwoZeroC] at heval
  have h1 := S.terminal_transverseSecondDerivative_eval_right_eq_axis
    T j (0 : Fin 3)
  have h2 := S.terminal_transverseSecondDerivative_eval_right_eq_axis
    T j (1 : Fin 3)
  have h3 := S.terminal_transverseSecondDerivative_eval_right_eq_axis
    T j (2 : Fin 3)
  rw [show ((0 : Fin 3).succ : Fin 4) = 1 by rfl] at h1
  rw [show ((1 : Fin 3).succ : Fin 4) = 2 by rfl] at h2
  rw [show ((2 : Fin 3).succ : Fin 4) = 3 by rfl] at h3
  rw [h1, h2, h3, hright] at heval
  simpa [mul_comm, add_assoc] using heval

/-- The terminal right point is forced back onto the marked negative
longitudinal axis. -/
theorem terminal_rightPoint_eq_negativeLongitudinalAxis
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (T : DirectClosingSquareFirstContactTerminalData
      (S.integrality.toFirstContactLattice heq)) :
    T.rightPoint = negativeLongitudinalAxisPoint (K := K) := by
  let H := S.terminalAxisHessian T
  let phi : Polynomial K →+* K := Polynomial.evalRingHom (-1 : K)
  let A : Matrix (Fin 4) (Fin 4) K := phi.mapMatrix H
  let v : Fin 4 → K := fun i => if i = 0 then 0 else T.rightPoint i
  have hdet : A.det = 1 := by
    have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
    calc
      A.det = (phi.mapMatrix H).det := by rfl
      _ = phi H.det := hmap.symm
      _ = phi 1 := by rw [S.terminalAxisHessian_det_one T]
      _ = 1 := map_one phi
  have hkernel : Matrix.mulVec A v = 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h01 := S.terminalAxisHessian_row_zero_of_ne_zero T (1 : Fin 4) (by decide)
      have h02 := S.terminalAxisHessian_row_zero_of_ne_zero T (2 : Fin 4) (by decide)
      have h03 := S.terminalAxisHessian_row_zero_of_ne_zero T (3 : Fin 4) (by decide)
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        A, H, phi, v, h01, h02, h03]
    · have hrow := S.terminal_axisHessian_transverseRow_mul_right_zero T j
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        A, H, phi, v, mul_comm, add_assoc] using hrow
  have hvzero : v = 0 := by
    by_contra hvne
    have hdet0 : A.det = 0 :=
      (Matrix.exists_mulVec_eq_zero_iff (M := A)).mp
        ⟨v, hvne, hkernel⟩
    rw [hdet] at hdet0
    exact one_ne_zero hdet0
  funext i
  by_cases hi : i = 0
  · subst i
    simpa [negativeLongitudinalAxisPoint, coordinateAxisPoint] using T.rightPoint_zero
  · have hvi := congrFun hvzero i
    have hri : T.rightPoint i = 0 := by
      simpa [v, hi] using hvi
    simp [negativeLongitudinalAxisPoint, coordinateAxisPoint, hi, hri]

/-- **Longitudinal canonical terminal contradiction.**

The rigid support structure, determinant-one axis Hessian, and exact collision
are already mutually inconsistent. -/
theorem impossible
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq) : False := by
  rcases S.terminal with ⟨T⟩
  have hright := S.terminal_rightPoint_eq_negativeLongitudinalAxis T
  rcases S.terminalAxisHessian_zero_zero_eq_C_nonzero T with
    ⟨c, hc, h00⟩
  have hsecond :
      (longitudinalAxisRestriction T.fibre).derivative.derivative =
        Polynomial.C c := by
    have haxis :
        longitudinalAxisRestriction
            (HC4.Polynomial.hessian T.fibre (0 : Fin 4) (0 : Fin 4)) =
          Polynomial.C c := by
      simpa [DirectClosingLongitudinalCanonicalTerminalData.terminalAxisHessian,
        longitudinalAxisRestrictionRingHom_apply] using h00
    change
      longitudinalAxisRestriction
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv (0 : Fin 4) T.fibre)) =
        Polynomial.C c at haxis
    rw [longitudinalAxisRestriction_pderiv_zero,
      longitudinalAxisRestriction_pderiv_zero] at haxis
    exact haxis
  let G := (longitudinalAxisRestriction T.fibre).derivative
  have hGderiv : G.derivative = Polynomial.C c := by
    simpa [G] using hsecond
  have hconstDeriv :
      (G - Polynomial.C c * Polynomial.X).derivative = 0 := by
    rw [Polynomial.derivative_sub, hGderiv, Polynomial.derivative_C_mul_X]
    simp
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hconstDeriv
  have hevalConst :
      Polynomial.eval (0 : K) (G - Polynomial.C c * Polynomial.X) =
        Polynomial.eval (-1 : K) (G - Polynomial.C c * Polynomial.X) := by
    rw [hconst]
    simp
  have hevalConst' :
      Polynomial.eval 0 G = Polynomial.eval (-1 : K) G + c := by
    simpa using hevalConst
  have hcoll := T.exactCollision (0 : Fin 4)
  change
    MvPolynomial.eval T.leftPoint
        (MvPolynomial.pderiv (0 : Fin 4) T.fibre) =
      MvPolynomial.eval T.rightPoint
        (MvPolynomial.pderiv (0 : Fin 4) T.fibre) at hcoll
  rw [T.leftPoint_eq_zero, hright] at hcoll
  have hzeroPoint :
      (fun _ : Fin 4 => (0 : K)) =
        Fin.cons (0 : K) (fun _ : Fin 3 => (0 : K)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hnegPoint :
      negativeLongitudinalAxisPoint (K := K) =
        Fin.cons (-1 : K) (fun _ : Fin 3 => (0 : K)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [negativeLongitudinalAxisPoint, coordinateAxisPoint]
    · simp [negativeLongitudinalAxisPoint, coordinateAxisPoint]
  rw [hzeroPoint, hnegPoint] at hcoll
  rw [eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative,
    eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative] at hcoll
  have hgrad : Polynomial.eval 0 G = Polynomial.eval (-1 : K) G := by
    simpa [G] using hcoll
  have hc0 : c = 0 := by
    have hcancel :
        Polynomial.eval (-1 : K) G + c =
          Polynomial.eval (-1 : K) G + 0 := by
      calc
        Polynomial.eval (-1 : K) G + c = Polynomial.eval 0 G :=
          hevalConst'.symm
        _ = Polynomial.eval (-1 : K) G := hgrad
        _ = Polynomial.eval (-1 : K) G + 0 := (add_zero _).symm
    exact add_left_cancel hcancel
  exact hc hc0

end DirectClosingLongitudinalCanonicalTerminalData

/-- Once the longitudinal terminal branch is eliminated, equality of the
actual-layer clock and the Hessian defect can only produce an explicit
strictly-earlier canonical square wall. -/
theorem directClosing_equality_forces_earlierWall
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    ∃ D : DirectClosingAlignedSquareSourceData C,
      DirectClosingCanonicalSquareEarlierWall D := by
  rcases C.directClosing_equality_earlierWall_or_longitudinalTerminal heq with
    hwall | hterminal
  · exact hwall
  · rcases hterminal with ⟨S⟩
    exact False.elim S.impossible

/-- **JC2-free local rank-one closing frontier.**

The first actual layer is either already strictly before the Hessian defect,
or equality has been converted into a concrete strictly-earlier canonical
coefficient/section wall.  There is no terminal square survivor left.

This is the exact interface wanted by the global restart assembly: the local
direct-closing geometry no longer contributes an unresolved terminal branch. -/
theorem firstActualLayer_strict_or_canonicalEarlierWall
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.firstActualLayerOrder < B.aligned.endpoint.defect ∨
      ∃ D : DirectClosingAlignedSquareSourceData C,
        DirectClosingCanonicalSquareEarlierWall D := by
  rcases Nat.lt_or_eq_of_le C.firstActualLayerOrder_le_defect with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr (C.directClosing_equality_forces_earlierWall heq)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
