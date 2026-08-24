import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTransverseJetNormalForm
import Mathlib.Tactic

/-!
# Exact all-depth recurrence for the stationary binary transverse staircase

The preceding stationary-core files identify a maximal homogeneous top layer

    H = a * L^D

and, in the genuinely curved branch, the first two descendants on the forced
arithmetic ray.  The first curved layer has degree `E`, the next forced
compensator has degree `2E-D`, and their exact transverse orders are `1` and
`2` respectively.

This file isolates the determinant recurrence which is valid at *every*
integer degree, not only at the first compensator degree.

If

    Q = H + R,
    det Hess Q = 0,
    det Hess H = 0,

and `H` is homogeneous of degree `D`, then for every integer `m`

    B(H, in_m R)
      = - in_{(D-2)+(m-2)} (det Hess R).

No upper bound on `R` is needed.  This is the exact triangular equation for
all later staircase layers.

We then package the arithmetic ray

    d_n = D - n*delta

and prove its finite terminal equation: when `delta > 0`, the candidate
layer at `n = D+1` has negative ordinary degree and therefore vanishes, so
the corresponding exact determinant source of the remainder must vanish as
well.

Thus the remaining curved-branch problem is reduced to a single sharp task:
show that the nonzero first transverse jet forces the terminal determinant
source on this ray to be nonzero.  That contradiction closes the curved
stationary binary branch.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Arbitrary exact-degree determinant recurrence -/

/-- **All-depth binary determinant recurrence.**

For a decomposition `Q = H + R` whose top piece `H` is homogeneous of
ordinary degree `D`, if both `Q` and `H` have zero binary Hessian determinant,
then the exact degree-`m` layer of `R` is tested by the exact determinant
component of the remainder at degree `(D-2)+(m-2)`.

This is the unrestricted-degree version of the equation used by the forced
compensator theorem.  In particular, no `IsWeightLE` hypothesis on `R` is
present. -/
theorem binarySingularHessian_crossComponent_recurrence_integer
    (Q H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (m : ℤ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    binaryHessianDetCross H
        (initialForm binaryOrdinaryIntegerWeight m R) =
      - initialForm binaryOrdinaryIntegerWeight
          (((D : ℤ) - 2) + (m - 2))
          (binaryDirectionalHessianDet (0 : Fin 2) 1 R) := by
  let level : ℤ := ((D : ℤ) - 2) + (m - 2)
  have hsum :
      binaryHessianDetCross H R +
          binaryDirectionalHessianDet (0 : Fin 2) 1 R = 0 := by
    have hexpand := binaryDirectionalHessianDet_add_cross H R
    have hrewrite :
        binaryHessianDetCross H R +
            binaryDirectionalHessianDet (0 : Fin 2) 1 R =
          binaryDirectionalHessianDet (0 : Fin 2) 1 (H + R) -
            binaryDirectionalHessianDet (0 : Fin 2) 1 H := by
      rw [hexpand]
      ring
    rw [hrewrite, ← hdecomp, hQdet, hHdet]
    ring
  have hcomponent := congrArg
    (fun P : MvPolynomial (Fin 2) K =>
      initialForm binaryOrdinaryIntegerWeight level P) hsum
  have hcross :=
    initialForm_binaryHessianDetCross_eq_integerComponent H R D m hH
  dsimp [level] at hcomponent hcross
  rw [initialForm_add, hcross, initialForm_zero] at hcomponent
  linear_combination hcomponent

/-- Natural-degree presentation of the all-depth recurrence. -/
theorem binarySingularHessian_crossComponent_recurrence_nat
    (Q H R : MvPolynomial (Fin 2) K)
    (D m : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    binaryHessianDetCross H (binaryOrdinaryDegreeComponent R m) =
      - initialForm binaryOrdinaryIntegerWeight
          (((D : ℤ) - 2) + ((m : ℤ) - 2))
          (binaryDirectionalHessianDet (0 : Fin 2) 1 R) := by
  simpa [binaryOrdinaryDegreeComponent] using
    (binarySingularHessian_crossComponent_recurrence_integer
      Q H R D (m : ℤ) hdecomp hH hQdet hHdet)

/-- A nonzero exact determinant source forces the corresponding exact
remainder layer to exist. -/
theorem binarySingularHessian_integerComponent_ne_zero_of_detSource_ne_zero
    (Q H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (m : ℤ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0)
    (hsource :
      initialForm binaryOrdinaryIntegerWeight
          (((D : ℤ) - 2) + (m - 2))
          (binaryDirectionalHessianDet (0 : Fin 2) 1 R) ≠ 0) :
    initialForm binaryOrdinaryIntegerWeight m R ≠ 0 := by
  intro hlayer
  have hrec := binarySingularHessian_crossComponent_recurrence_integer
    Q H R D m hdecomp hH hQdet hHdet
  have hcrossZero :
      binaryHessianDetCross H
          (initialForm binaryOrdinaryIntegerWeight m R) = 0 := by
    rw [hlayer]
    simp [binaryHessianDetCross, directionalSecondDerivative,
      directionalMixedDerivative]
  rw [hcrossZero] at hrec
  apply hsource
  exact neg_eq_zero.mp hrec.symm

/-- If the candidate remainder degree is negative, the exact determinant
source at the matching recurrence level must vanish.  This is the terminal
equation used when a finite staircase runs out of polynomial degrees. -/
theorem binarySingularHessian_detSource_eq_zero_of_candidateDegree_neg
    (Q H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (m : ℤ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0)
    (hm : m < 0) :
    initialForm binaryOrdinaryIntegerWeight
        (((D : ℤ) - 2) + (m - 2))
        (binaryDirectionalHessianDet (0 : Fin 2) 1 R) = 0 := by
  have hlayer : initialForm binaryOrdinaryIntegerWeight m R = 0 :=
    binaryOrdinaryInitialForm_eq_zero_of_neg R m hm
  have hrec := binarySingularHessian_crossComponent_recurrence_integer
    Q H R D m hdecomp hH hQdet hHdet
  have hcrossZero :
      binaryHessianDetCross H
          (initialForm binaryOrdinaryIntegerWeight m R) = 0 := by
    rw [hlayer]
    simp [binaryHessianDetCross, directionalSecondDerivative,
      directionalMixedDerivative]
  rw [hcrossZero] at hrec
  exact neg_eq_zero.mp hrec.symm

/-! ## The arithmetic staircase ray -/

/-- Integer ordinary degree of the `n`-th point on a staircase with top
ordinary degree `D` and positive degree gap `delta`.  Integer degrees avoid
truncating the terminal negative layer. -/
def binaryStationaryStaircaseDegree
    (D : ℕ) (delta : ℤ) (n : ℕ) : ℤ :=
  (D : ℤ) - (n : ℤ) * delta

/-- Matching determinant degree for the `n`-th staircase equation. -/
def binaryStationaryStaircaseDetLevel
    (D : ℕ) (delta : ℤ) (n : ℕ) : ℤ :=
  ((D : ℤ) - 2) + (binaryStationaryStaircaseDegree D delta n - 2)

/-- Exact remainder layer on the arithmetic stationary staircase. -/
noncomputable def binaryStationaryStaircaseLayer
    (R : MvPolynomial (Fin 2) K)
    (D : ℕ) (delta : ℤ) (n : ℕ) : MvPolynomial (Fin 2) K :=
  initialForm binaryOrdinaryIntegerWeight
    (binaryStationaryStaircaseDegree D delta n) R

@[simp]
theorem binaryStationaryStaircaseDegree_zero
    (D : ℕ) (delta : ℤ) :
    binaryStationaryStaircaseDegree D delta 0 = D := by
  simp [binaryStationaryStaircaseDegree]

/-- Consecutive staircase degrees differ by the fixed gap. -/
theorem binaryStationaryStaircaseDegree_succ
    (D : ℕ) (delta : ℤ) (n : ℕ) :
    binaryStationaryStaircaseDegree D delta (n + 1) =
      binaryStationaryStaircaseDegree D delta n - delta := by
  simp [binaryStationaryStaircaseDegree]
  ring

/-- The staircase recurrence is literally the arbitrary exact-component
recurrence specialised to the arithmetic ray. -/
theorem binarySingularHessian_staircase_recurrence
    (Q H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (delta : ℤ)
    (n : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    binaryHessianDetCross H
        (binaryStationaryStaircaseLayer R D delta n) =
      - initialForm binaryOrdinaryIntegerWeight
          (binaryStationaryStaircaseDetLevel D delta n)
          (binaryDirectionalHessianDet (0 : Fin 2) 1 R) := by
  simpa [binaryStationaryStaircaseLayer,
    binaryStationaryStaircaseDetLevel] using
    (binarySingularHessian_crossComponent_recurrence_integer
      Q H R D (binaryStationaryStaircaseDegree D delta n)
      hdecomp hH hQdet hHdet)

/-- A nonzero determinant source on the arithmetic ray forces the matching
staircase layer to be nonzero. -/
theorem binarySingularHessian_staircaseLayer_ne_zero_of_detSource_ne_zero
    (Q H R : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (delta : ℤ)
    (n : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0)
    (hsource :
      initialForm binaryOrdinaryIntegerWeight
          (binaryStationaryStaircaseDetLevel D delta n)
          (binaryDirectionalHessianDet (0 : Fin 2) 1 R) ≠ 0) :
    binaryStationaryStaircaseLayer R D delta n ≠ 0 := by
  exact binarySingularHessian_integerComponent_ne_zero_of_detSource_ne_zero
    Q H R D (binaryStationaryStaircaseDegree D delta n)
    hdecomp hH hQdet hHdet hsource

/-- If the fixed gap is positive, staircase degrees strictly decrease. -/
theorem binaryStationaryStaircaseDegree_succ_lt
    (D : ℕ) (delta : ℤ) (n : ℕ)
    (hdelta : 0 < delta) :
    binaryStationaryStaircaseDegree D delta (n + 1) <
      binaryStationaryStaircaseDegree D delta n := by
  rw [binaryStationaryStaircaseDegree_succ]
  omega

/-- For a positive natural gap, the `(D+1)`-st staircase candidate already
has negative ordinary degree.  This deliberately uses the crude bound
`D+1`; no division or floor arithmetic is needed. -/
theorem binaryStationaryStaircaseDegree_terminal_neg
    (D delta : ℕ)
    (hdelta : 0 < delta) :
    binaryStationaryStaircaseDegree D (delta : ℤ) (D + 1) < 0 := by
  have hdeltaOne : 1 ≤ delta := hdelta
  have hmul : D < (D + 1) * delta := by
    calc
      D < D + 1 := Nat.lt_succ_self D
      _ = (D + 1) * 1 := by omega
      _ ≤ (D + 1) * delta := Nat.mul_le_mul_left (D + 1) hdeltaOne
  have hmulZ :
      (D : ℤ) < ((D + 1 : ℕ) : ℤ) * (delta : ℤ) := by
    exact_mod_cast hmul
  unfold binaryStationaryStaircaseDegree
  omega

/-- Therefore the polynomial layer itself is zero at the crude finite
terminal index `D+1`. -/
theorem binaryStationaryStaircaseLayer_terminal_zero
    (R : MvPolynomial (Fin 2) K)
    (D delta : ℕ)
    (hdelta : 0 < delta) :
    binaryStationaryStaircaseLayer R D (delta : ℤ) (D + 1) = 0 := by
  unfold binaryStationaryStaircaseLayer
  apply binaryOrdinaryInitialForm_eq_zero_of_neg
  exact binaryStationaryStaircaseDegree_terminal_neg D delta hdelta

/-- **Finite terminal determinant equation.**

Every singular-Hessian decomposition with a positive staircase gap reaches,
by the crude index `D+1`, an exact determinant level whose source must vanish.
The next closing theorem only has to prove that a genuinely curved seed makes
this source nonzero. -/
theorem binarySingularHessian_staircase_terminal_detSource_zero
    (Q H R : MvPolynomial (Fin 2) K)
    (D delta : ℕ)
    (hdelta : 0 < delta)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    initialForm binaryOrdinaryIntegerWeight
        (binaryStationaryStaircaseDetLevel D (delta : ℤ) (D + 1))
        (binaryDirectionalHessianDet (0 : Fin 2) 1 R) = 0 := by
  apply binarySingularHessian_detSource_eq_zero_of_candidateDegree_neg
    Q H R D
      (binaryStationaryStaircaseDegree D (delta : ℤ) (D + 1))
      hdecomp hH hQdet hHdet
  exact binaryStationaryStaircaseDegree_terminal_neg D delta hdelta

/-! ## Alignment with the first two already-constructed descendants -/

/-- If `delta = D-E`, the first arithmetic staircase degree is exactly `E`. -/
theorem binaryStationaryStaircaseDegree_one_eq_next
    (D E : ℕ)
    (hED : E ≤ D) :
    binaryStationaryStaircaseDegree D ((D - E : ℕ) : ℤ) 1 = E := by
  simp [binaryStationaryStaircaseDegree, Nat.cast_sub hED]

/-- The second arithmetic staircase degree is the integer `2E-D`, exactly the
forced-compensator degree before nonnegativity is established. -/
theorem binaryStationaryStaircaseDegree_two_eq_compensator
    (D E : ℕ)
    (hED : E ≤ D) :
    binaryStationaryStaircaseDegree D ((D - E : ℕ) : ℤ) 2 =
      2 * (E : ℤ) - D := by
  simp [binaryStationaryStaircaseDegree, Nat.cast_sub hED]
  ring

end

end HC4.Valuation
