import HC4.Newton.LinearPowerPacketNormalForm
import Mathlib.Tactic

/-!
# Orientation-independent rank-two homogeneous packet classification

Phase 91.11 proves the full coefficientwise linear-power normal form in the
generic left-pivot orientation `b ≠ 0`.

The remaining orientations are simpler:

* left pivot with `b = 0`:
  the canonical kernel direction `(-b,a)` becomes `(0,a)`.  Since `a ≠ 0`,
  vanishing of that directional derivative forces `pderiv j F = 0`.
  Phase 91.5 then gives pure left-axis transverse support.

* right-axis pivot:
  the kernel direction is `(1,0)`, so the same Phase 91.4/91.5 chain gives
  pure right-axis transverse support.

This file packages all three possibilities into one theorem, removing the
pivot-orientation case split from later corank-entry arguments.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Orientation-independent normal-form conclusion for a rank-two
homogeneous binary packet. -/
def HasRankTwoHomogeneousPacketClassification
    (q : BinarySchurBlock K)
    (i j : σ)
    (n : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  (q.LeftPivot ∧ q.b ≠ 0 ∧
      HasLinearPowerTransverseNormalForm
        (-q.b) q.a i j n F) ∨
  (q.LeftPivot ∧ q.b = 0 ∧
      HasPureLeftAxisTransverseDegree i j n F) ∨
  (q.RightAxisPivot ∧
      HasPureRightAxisTransverseDegree i j n F)

/-- In the left-pivot axis case `b = 0`, vanishing of the canonical
directional derivative forces the second partial derivative to vanish. -/
theorem pderiv_second_eq_zero_of_leftPivot_b_eq_zero
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (hb : q.b = 0)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hdir :
      binaryDirectionalDeriv (-q.b) q.a i j F = 0) :
    MvPolynomial.pderiv j F = 0 := by
  have hscaled :
      MvPolynomial.C q.a * MvPolynomial.pderiv j F = 0 := by
    simpa [binaryDirectionalDeriv, hb] using hdir
  have hCa :
      (MvPolynomial.C q.a : MvPolynomial σ K) ≠ 0 := by
    simpa using hleft.1
  exact (mul_eq_zero.mp hscaled).resolve_left hCa

/-- Left-pivot axis branch: `b = 0` forces pure left-axis transverse
support. -/
theorem pureLeftAxis_of_leftPivot_b_eq_zero
    [CharZero K]
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (hb : q.b = 0)
    {i j : σ}
    (n m : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmpos : 0 < m)
    (hexactD :
      HasExactTransverseDegree i j m
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hkernel : HasLeftPivotHessianKernel q i j F) :
    HasPureLeftAxisTransverseDegree i j n F := by
  have hdir :
      binaryDirectionalDeriv (-q.b) q.a i j F = 0 :=
    binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree
      (-q.b) q.a i j F m hmpos hkernel hexactD
  have hpj :
      MvPolynomial.pderiv j F = 0 :=
    pderiv_second_eq_zero_of_leftPivot_b_eq_zero
      q hleft hb i j F hdir
  exact
    pureLeftAxis_of_pderiv_second_eq_zero_of_exactDegree
      i j n F hexactF hpj

/-- Right-axis branch: the canonical kernel `(1,0)` forces pure
right-axis transverse support. -/
theorem pureRightAxis_of_rightAxisPivotKernel
    [CharZero K]
    (q : BinarySchurBlock K)
    (hright : q.RightAxisPivot)
    {i j : σ}
    (n m : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmpos : 0 < m)
    (hexactD :
      HasExactTransverseDegree i j m
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hkernel : HasRightAxisHessianKernel i j F) :
    HasPureRightAxisTransverseDegree i j n F := by
  have hdir :
      binaryDirectionalDeriv (1 : K) 0 i j F = 0 :=
    binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree
      (1 : K) 0 i j F m hmpos hkernel hexactD
  exact
    pureRightAxis_of_axisDirectionalDeriv_eq_zero
      i j n F hexactF hdir

/-- **Orientation-independent rank-two homogeneous classification.**
A nonzero determinant-zero binary Schur packet has one of the three rigid
homogeneous normal forms:

1. generic one-linear-form power (`b ≠ 0`);
2. pure left-axis power (`b = 0` inside the left-pivot branch);
3. pure right-axis power.

The Hessian-kernel and positive-degree hypotheses are supplied separately
for the left and right pivot orientations, and only the branch selected by
the determinant-zero pivot theorem is used. -/
theorem rankTwoHomogeneousPacketClassification
    [CharZero K]
    (q : BinarySchurBlock K)
    (hdet : q.detCore = 0)
    (hnz : q.Nonzero)
    {i j : σ}
    (hij : i ≠ j)
    (n mLeft mRight : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmLeftPos : 0 < mLeft)
    (hmRightPos : 0 < mRight)
    (hexactLeft :
      HasExactTransverseDegree i j mLeft
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hexactRight :
      HasExactTransverseDegree i j mRight
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hleftKernel :
      q.LeftPivot -> HasLeftPivotHessianKernel q i j F)
    (hrightKernel :
      q.RightAxisPivot -> HasRightAxisHessianKernel i j F) :
    HasRankTwoHomogeneousPacketClassification q i j n F := by
  rcases q.pivot_of_detCore_eq_zero hdet hnz with hleft | hright
  · by_cases hb : q.b = 0
    · right
      left
      refine ⟨hleft, hb, ?_⟩
      exact
        pureLeftAxis_of_leftPivot_b_eq_zero
          q hleft hb n mLeft F hexactF hmLeftPos
          hexactLeft (hleftKernel hleft)
    · left
      refine ⟨hleft, hb, ?_⟩
      exact
        hasLinearPowerTransverseNormalForm_of_leftPivotKernel
          q hleft hb hij n mLeft F hexactF hmLeftPos
          hexactLeft (hleftKernel hleft)
  · right
    right
    refine ⟨hright, ?_⟩
    exact
      pureRightAxis_of_rightAxisPivotKernel
        q hright n mRight F hexactF hmRightPos
        hexactRight (hrightKernel hright)

end

end HC4.Newton
