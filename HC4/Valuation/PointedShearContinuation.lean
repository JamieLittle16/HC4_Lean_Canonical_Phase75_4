import HC4.Valuation.GeometricAssemblyEntry
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Pointed shear continuation

Phase 93.72 exposed the first genuinely geometric assembly interface:
after a separated right Smith section wall the exact collision survives,
the source-homogeneous family survives, and the determinant defect drops on
the once-ramified scale, but the right special point has moved from `e0` to

    (1,Y,Z,W).

This file removes the *point-normalisation* part of that interface.

The correct coordinate change is not translation, which would destroy
ordinary source homogeneity.  It is a determinant-one unipotent shear.

For a transverse coordinate `k != 0` and coefficient `c`, put

    X_k |-> X_k + c X_0,

fixing the other source variables.  The inverse change on a moving section is

    a_k |-> a_k - c a_0.

The file proves, coefficientwise over `K[tau]`:

* exact evaluation covariance;
* ordinary homogeneity preservation;
* the first-order chain rule;
* exact Hessian congruence by the two elementary transvections;
* exact Hessian-determinant preservation;
* exact family-gradient collision preservation.

Applying the shears in coordinates `1,2,3`, with constants equal to the
three transverse special coordinates of the moving right section, sends
every special point with zero-coordinate equal to `1` exactly to `e0`.

The final theorem applies this to a separated right Smith wall after the
green `X^10` common-factor extraction from Phase 93.72.  Consequently the
previously named proposition

    HasCanonicalContinuationFromSeparatedRightWall

is now proved from the actual geometric hypotheses.

Important audit boundary:
this removes the pointed-coordinate obstruction but does not by itself turn
the physical defect `20*(Delta-2)` into an unramified defect `Delta-2`.
That scale descent is a distinct global-recursion issue and is not hidden
inside this theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open Matrix

variable {K : Type*} [Field K]

/-! ## One elementary determinant-one shear -/

/-- Source-variable image for the elementary shear

    X_k |-> X_k + c X_0.

The intended use always has `k != 0`. -/
def elementaryShearVariable
    (k : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  if i = k then
    MvPolynomial.X k +
      MvPolynomial.C c * MvPolynomial.X (0 : Fin 4)
  else
    MvPolynomial.X i

/-- Ring homomorphism implementing the elementary shear. -/
noncomputable def elementaryShearHom
    (k : Fin 4)
    (c : Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom
    MvPolynomial.C
    (elementaryShearVariable (K := K) k c)

/-- Inverse shear on a polynomial moving section. -/
def elementaryUnshearSection
    (k : Fin 4)
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  fun i =>
    if i = k then
      a i - c * a 0
    else
      a i

@[simp] theorem elementaryUnshearSection_zero
    (k : Fin 4)
    (c : Polynomial K) :
    elementaryUnshearSection
        k c
        (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  by_cases hi : i = k
  · simp [elementaryUnshearSection,
      zeroPolynomialSection, hi]
  · simp [elementaryUnshearSection,
      zeroPolynomialSection, hi]

/-- Evaluation of one sheared variable at the inverse-sheared section
recovers the original source coordinate. -/
theorem eval_elementaryShearVariable_unshear
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K)
    (i : Fin 4) :
    MvPolynomial.eval
        (elementaryUnshearSection k c a)
        (elementaryShearVariable (K := K) k c i) =
      a i := by
  by_cases hik : i = k
  · subst i
    have hk0' : (0 : Fin 4) ≠ k := Ne.symm hk0
    simp [elementaryShearVariable,
      elementaryUnshearSection, hk0']
  · simp [elementaryShearVariable,
      elementaryUnshearSection, hik]

/-- Exact evaluation covariance of the elementary shear. -/
theorem eval_elementaryShearHom_unshear
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval
        (elementaryUnshearSection k c a)
        (elementaryShearHom (K := K) k c P) =
      MvPolynomial.eval a P := by
  change
    MvPolynomial.eval
        (elementaryUnshearSection k c a)
        (MvPolynomial.eval₂
          MvPolynomial.C
          (elementaryShearVariable (K := K) k c)
          P) =
      MvPolynomial.eval a P
  rw [← MvPolynomial.eval_assoc
    (elementaryShearVariable (K := K) k c)
    (elementaryUnshearSection k c a)
    P]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext i
  exact
    eval_elementaryShearVariable_unshear
      k hk0 c a i

/-! ## Homogeneity -/

/-- Every elementary shear variable is linear in the source variables. -/
theorem elementaryShearVariable_isHomogeneous_one
    (k : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    (elementaryShearVariable (K := K) k c i).IsHomogeneous 1 := by
  by_cases hik : i = k
  · subst i
    unfold elementaryShearVariable
    simp only [if_pos rfl]
    exact
      (MvPolynomial.isHomogeneous_X
          (Polynomial K) k).add
        (MvPolynomial.isHomogeneous_C_mul_X
          c (0 : Fin 4))
  · unfold elementaryShearVariable
    rw [if_neg hik]
    exact MvPolynomial.isHomogeneous_X
      (Polynomial K) i

/-- A linear shear preserves ordinary source homogeneity exactly. -/
theorem elementaryShearHom_isHomogeneous
    {D : ℕ}
    (k : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D) :
    (elementaryShearHom (K := K) k c P).IsHomogeneous D := by
  have hout :=
    hP.eval₂
      MvPolynomial.C
      (elementaryShearVariable (K := K) k c)
      (fun r =>
        MvPolynomial.isHomogeneous_C (Fin 4) r)
      (fun i =>
        elementaryShearVariable_isHomogeneous_one
          (K := K) k c i)
  simpa [elementaryShearHom] using hout

/-! ## First-order chain rule -/

/-!
The first draft unfolded `elementaryShearHom` inside the induction.  That
turns `eval₂Hom` into its internal `bind₁` representation, so the induction
hypothesis no longer matches syntactically.

The stable approach is to keep the ring homomorphism opaque.  We expose only
its values on constants and variables and then use the standard
`MvPolynomial.induction_on` constructor `p * X n`.
-/

@[simp] theorem elementaryShearHom_C
    (k : Fin 4)
    (c r : Polynomial K) :
    elementaryShearHom (K := K) k c (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [elementaryShearHom]

@[simp] theorem elementaryShearHom_X
    (k : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    elementaryShearHom (K := K) k c (MvPolynomial.X i) =
      elementaryShearVariable (K := K) k c i := by
  simp [elementaryShearHom]

/-- Away from the longitudinal coordinate, the elementary shear has the
identity chain rule. -/
theorem pderiv_elementaryShearHom_of_ne_zero
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (j : Fin 4)
    (hj0 : j ≠ (0 : Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv j
        (elementaryShearHom (K := K) k c P) =
      elementaryShearHom (K := K) k c
        (MvPolynomial.pderiv j P) := by
  apply MvPolynomial.induction_on P
  · intro r
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp only [map_mul, elementaryShearHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnk : n = k
    · subst n
      by_cases hkj : k = j
      · subst j
        simp [elementaryShearVariable, hk0] <;> ring
      · have hjk : j ≠ k := Ne.symm hkj
        simp [elementaryShearVariable, hk0, hkj, hjk, hj0] <;> ring
    · by_cases hnj : n = j
      · subst n
        have hjk : j ≠ k := by
          intro h
          exact hnk h
        simp [elementaryShearVariable, hnk, hjk, hj0] <;> ring
      · have hjn : j ≠ n := Ne.symm hnj
        simp [elementaryShearVariable, hnk, hnj, hjn, hj0] <;> ring

/-- In the longitudinal direction, the shear chain rule has one additional
transverse component. -/
theorem pderiv_zero_elementaryShearHom
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv (0 : Fin 4)
        (elementaryShearHom (K := K) k c P) =
      elementaryShearHom (K := K) k c
          (MvPolynomial.pderiv (0 : Fin 4) P) +
        MvPolynomial.C c *
          elementaryShearHom (K := K) k c
            (MvPolynomial.pderiv k P) := by
  apply MvPolynomial.induction_on P
  · intro r
    simp
  · intro p q hp hq
    simp [hp, hq, mul_add, add_mul] <;> ring
  · intro p n hp
    simp only [map_mul, elementaryShearHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hn0 : n = (0 : Fin 4)
    · subst n
      have hk0' : (0 : Fin 4) ≠ k := Ne.symm hk0
      simp [elementaryShearVariable, hk0, hk0']
      ring
    · by_cases hnk : n = k
      · subst n
        have hk0' : (0 : Fin 4) ≠ k := Ne.symm hk0
        simp [elementaryShearVariable, hk0, hk0']
        ring
      · have h0n : (0 : Fin 4) ≠ n := Ne.symm hn0
        simp [elementaryShearVariable, hn0, h0n, hnk, hk0]
        ring

/-! ## Hessian congruence -/

/-- Right source matrix of the elementary shear. -/
def elementaryShearMatrix
    (k : Fin 4)
    (c : Polynomial K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
  Matrix.transvection
    k (0 : Fin 4) (MvPolynomial.C c)

/-- Left transpose matrix of the same elementary shear. -/
def elementaryShearTransposeMatrix
    (k : Fin 4)
    (c : Polynomial K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
  Matrix.transvection
    (0 : Fin 4) k (MvPolynomial.C c)

/-- Entrywise Hessian covariance under the elementary shear. -/
theorem hessian_elementaryShearHom
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian
        (elementaryShearHom (K := K) k c P) =
      elementaryShearTransposeMatrix (K := K) k c *
        (elementaryShearHom (K := K) k c).mapMatrix
          (HC4.Polynomial.hessian P) *
        elementaryShearMatrix (K := K) k c := by
  apply Matrix.ext
  intro i j
  let A :
      Matrix (Fin 4) (Fin 4)
        (MvPolynomial (Fin 4) (Polynomial K)) :=
    (elementaryShearHom (K := K) k c).mapMatrix
      (HC4.Polynomial.hessian P)
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    by_cases hj0 : j = (0 : Fin 4)
    · subst j
      rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_zero_elementaryShearHom
        k hk0 c P]
      rw [map_add, MvPolynomial.pderiv_C_mul]
      rw [pderiv_zero_elementaryShearHom
        k hk0 c (MvPolynomial.pderiv (0 : Fin 4) P)]
      rw [pderiv_zero_elementaryShearHom
        k hk0 c (MvPolynomial.pderiv k P)]
      have hleft0 :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              (0 : Fin 4) (0 : Fin 4) =
            A 0 0 + MvPolynomial.C c * A k 0 := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_same
            (0 : Fin 4) k (0 : Fin 4)
            (MvPolynomial.C c) A
      have hleftk :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              (0 : Fin 4) k =
            A 0 k + MvPolynomial.C c * A k k := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_same
            (0 : Fin 4) k k
            (MvPolynomial.C c) A
      have hright :
          ((elementaryShearTransposeMatrix (K := K) k c * A) *
              elementaryShearMatrix (K := K) k c)
              (0 : Fin 4) (0 : Fin 4) =
            (elementaryShearTransposeMatrix (K := K) k c * A)
                0 0 +
              MvPolynomial.C c *
                (elementaryShearTransposeMatrix (K := K) k c * A)
                  0 k := by
        unfold elementaryShearMatrix
        exact
          Matrix.mul_transvection_apply_same
            k (0 : Fin 4) (0 : Fin 4)
            (MvPolynomial.C c)
            (elementaryShearTransposeMatrix (K := K) k c * A)
      rw [hright, hleft0, hleftk]
      simp [A, HC4.Polynomial.hessian_apply] <;> ring
    · rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_zero_elementaryShearHom
        k hk0 c P]
      rw [map_add, MvPolynomial.pderiv_C_mul]
      rw [pderiv_elementaryShearHom_of_ne_zero
        k hk0 c j hj0
        (MvPolynomial.pderiv (0 : Fin 4) P)]
      rw [pderiv_elementaryShearHom_of_ne_zero
        k hk0 c j hj0
        (MvPolynomial.pderiv k P)]
      have hleft :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              (0 : Fin 4) j =
            A 0 j + MvPolynomial.C c * A k j := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_same
            (0 : Fin 4) k j
            (MvPolynomial.C c) A
      have hright :
          ((elementaryShearTransposeMatrix (K := K) k c * A) *
              elementaryShearMatrix (K := K) k c)
              (0 : Fin 4) j =
            (elementaryShearTransposeMatrix (K := K) k c * A)
              0 j := by
        unfold elementaryShearMatrix
        exact
          Matrix.mul_transvection_apply_of_ne
            k (0 : Fin 4) (0 : Fin 4) j hj0
            (MvPolynomial.C c)
            (elementaryShearTransposeMatrix (K := K) k c * A)
      rw [hright, hleft]
      simp [A, HC4.Polynomial.hessian_apply]
  · by_cases hj0 : j = (0 : Fin 4)
    · subst j
      rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_elementaryShearHom_of_ne_zero
        k hk0 c i hi0 P]
      rw [pderiv_zero_elementaryShearHom
        k hk0 c (MvPolynomial.pderiv i P)]
      have hleft0 :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              i (0 : Fin 4) =
            A i 0 := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_of_ne
            (0 : Fin 4) k i 0 hi0
            (MvPolynomial.C c) A
      have hleftk :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              i k =
            A i k := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_of_ne
            (0 : Fin 4) k i k hi0
            (MvPolynomial.C c) A
      have hright :
          ((elementaryShearTransposeMatrix (K := K) k c * A) *
              elementaryShearMatrix (K := K) k c)
              i (0 : Fin 4) =
            (elementaryShearTransposeMatrix (K := K) k c * A)
                i 0 +
              MvPolynomial.C c *
                (elementaryShearTransposeMatrix (K := K) k c * A)
                  i k := by
        unfold elementaryShearMatrix
        exact
          Matrix.mul_transvection_apply_same
            k (0 : Fin 4) i
            (MvPolynomial.C c)
            (elementaryShearTransposeMatrix (K := K) k c * A)
      rw [hright, hleft0, hleftk]
      simp [A, HC4.Polynomial.hessian_apply]
    · rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_elementaryShearHom_of_ne_zero
        k hk0 c i hi0 P]
      rw [pderiv_elementaryShearHom_of_ne_zero
        k hk0 c j hj0
        (MvPolynomial.pderiv i P)]
      have hleft :
          (elementaryShearTransposeMatrix (K := K) k c * A)
              i j =
            A i j := by
        unfold elementaryShearTransposeMatrix
        exact
          Matrix.transvection_mul_apply_of_ne
            (0 : Fin 4) k i j hi0
            (MvPolynomial.C c) A
      have hright :
          ((elementaryShearTransposeMatrix (K := K) k c * A) *
              elementaryShearMatrix (K := K) k c)
              i j =
            (elementaryShearTransposeMatrix (K := K) k c * A)
              i j := by
        unfold elementaryShearMatrix
        exact
          Matrix.mul_transvection_apply_of_ne
            k (0 : Fin 4) i j hj0
            (MvPolynomial.C c)
            (elementaryShearTransposeMatrix (K := K) k c * A)
      rw [hright, hleft]
      simp [A, HC4.Polynomial.hessian_apply]

/-- Both elementary shear matrices have determinant one. -/
theorem det_elementaryShearMatrices
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K) :
    (elementaryShearMatrix (K := K) k c).det = 1 ∧
      (elementaryShearTransposeMatrix (K := K) k c).det = 1 := by
  constructor
  · unfold elementaryShearMatrix
    exact
      Matrix.det_transvection_of_ne
        k (0 : Fin 4) hk0 (MvPolynomial.C c)
  · unfold elementaryShearTransposeMatrix
    exact
      Matrix.det_transvection_of_ne
        (0 : Fin 4) k (Ne.symm hk0)
        (MvPolynomial.C c)

/-- Exact Hessian determinant covariance under the determinant-one shear. -/
theorem hessianDeterminant_elementaryShearHom
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (elementaryShearHom (K := K) k c P) =
      elementaryShearHom (K := K) k c
        (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_elementaryShearHom
    k hk0 c P]
  rw [Matrix.det_mul, Matrix.det_mul]
  rcases
      det_elementaryShearMatrices
        (K := K) k hk0 c with
    ⟨hright, hleft⟩
  rw [hleft, hright]
  simp
  exact
    (RingHom.map_det
      (elementaryShearHom (K := K) k c)
      (HC4.Polynomial.hessian P)).symm

/-- Pure polynomial-family Hessian defect is unchanged by an elementary
determinant-one shear. -/
theorem elementaryShearHom_preservesHessianDefect
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (elementaryShearHom (K := K) k c P)
      Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_elementaryShearHom
    k hk0 c P]
  rw [hdef]
  simp [elementaryShearHom]

/-! ## Exact collision covariance -/

/-- An exact family-gradient collision survives the elementary shear when
both marked sections are transformed by the inverse shear. -/
theorem polynomialFamilyExactGradientCollision_elementaryShear
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (elementaryShearHom (K := K) k c P)
      (elementaryUnshearSection k c a)
      (elementaryUnshearSection k c b) := by
  intro i
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    rw [pderiv_zero_elementaryShearHom
      k hk0 c P]
    have h0 := hcoll (0 : Fin 4)
    have hk := hcoll k
    have hsum :=
      congrArg₂
        (fun x y : Polynomial K => x + c * y)
        h0 hk
    simpa [eval_elementaryShearHom_unshear
      (K := K) k hk0 c] using hsum
  · rw [pderiv_elementaryShearHom_of_ne_zero
      k hk0 c i hi0 P]
    rw [eval_elementaryShearHom_unshear
      (K := K) k hk0 c]
    rw [eval_elementaryShearHom_unshear
      (K := K) k hk0 c]
    exact hcoll i

/-! ## Special-point effect -/

/-- The longitudinal special coordinate is unchanged by every transverse
inverse shear. -/
theorem polynomialSectionSpecialPoint_elementaryUnshear_zero
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K) :
    polynomialSectionSpecialPoint
        (elementaryUnshearSection k c a)
        (0 : Fin 4) =
      polynomialSectionSpecialPoint a (0 : Fin 4) := by
  have hk0' : (0 : Fin 4) ≠ k := Ne.symm hk0
  simp [polynomialSectionSpecialPoint,
    elementaryUnshearSection, hk0']

/-- Choosing a constant shear coefficient equal to the transverse special
coordinate kills that coordinate whenever the longitudinal special
coordinate is one. -/
theorem polynomialSectionSpecialPoint_elementaryUnshear_k_eq_zero
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (a : Fin 4 → Polynomial K)
    (ha0 :
      polynomialSectionSpecialPoint a (0 : Fin 4) = 1) :
    polynomialSectionSpecialPoint
        (elementaryUnshearSection
          k
          (Polynomial.C
            (polynomialSectionSpecialPoint a k))
          a)
        k = 0 := by
  have ha0' :
      Polynomial.constantCoeff (a 0) = 1 := by
    simpa [polynomialSectionSpecialPoint] using ha0
  have ha0coeff :
      (a 0).coeff 0 = 1 := by
    simpa using ha0'
  simp [polynomialSectionSpecialPoint,
    elementaryUnshearSection]
  rw [ha0coeff]
  ring

/-- Other special coordinates are unchanged by a shear in coordinate `k`. -/
theorem polynomialSectionSpecialPoint_elementaryUnshear_of_ne
    (k : Fin 4)
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K)
    {i : Fin 4}
    (hik : i ≠ k) :
    polynomialSectionSpecialPoint
        (elementaryUnshearSection k c a) i =
      polynomialSectionSpecialPoint a i := by
  simp [polynomialSectionSpecialPoint,
    elementaryUnshearSection, hik]

/-! ## Three-shear canonical pointed normalisation -/

noncomputable def pointedShearCoeffOne
    (b : Fin 4 → Polynomial K) :
    Polynomial K :=
  Polynomial.C
    (polynomialSectionSpecialPoint b (1 : Fin 4))

noncomputable def pointedShearSectionOne
    (b : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  elementaryUnshearSection
    (1 : Fin 4) (pointedShearCoeffOne b) b

noncomputable def pointedShearCoeffTwo
    (b : Fin 4 → Polynomial K) :
    Polynomial K :=
  Polynomial.C
    (polynomialSectionSpecialPoint
      (pointedShearSectionOne b) (2 : Fin 4))

noncomputable def pointedShearSectionTwo
    (b : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  elementaryUnshearSection
    (2 : Fin 4) (pointedShearCoeffTwo b)
    (pointedShearSectionOne b)

noncomputable def pointedShearCoeffThree
    (b : Fin 4 → Polynomial K) :
    Polynomial K :=
  Polynomial.C
    (polynomialSectionSpecialPoint
      (pointedShearSectionTwo b) (3 : Fin 4))

noncomputable def pointedShearNormalisedSection
    (b : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  elementaryUnshearSection
    (3 : Fin 4) (pointedShearCoeffThree b)
    (pointedShearSectionTwo b)

noncomputable def pointedShearFamilyOne
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  elementaryShearHom
    (K := K)
    (1 : Fin 4) (pointedShearCoeffOne b) P

noncomputable def pointedShearFamilyTwo
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  elementaryShearHom
    (K := K)
    (2 : Fin 4) (pointedShearCoeffTwo b)
    (pointedShearFamilyOne P b)

noncomputable def pointedShearNormalisedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  elementaryShearHom
    (K := K)
    (3 : Fin 4) (pointedShearCoeffThree b)
    (pointedShearFamilyTwo P b)

/-- Three transverse shears send every special point with longitudinal
coordinate one exactly to `e0`. -/
theorem pointedShearNormalisedSection_specialPoint
    (b : Fin 4 → Polynomial K)
    (hb0 :
      polynomialSectionSpecialPoint b (0 : Fin 4) = 1) :
    polynomialSectionSpecialPoint
        (pointedShearNormalisedSection b) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  fin_cases i
  · have h1 :
        polynomialSectionSpecialPoint
            (pointedShearSectionOne b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (1 : Fin 4) (by decide)
          (pointedShearCoeffOne b) b).trans hb0
    have h2 :
        polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (2 : Fin 4) (by decide)
          (pointedShearCoeffTwo b)
          (pointedShearSectionOne b)).trans h1
    have h3 :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (3 : Fin 4) (by decide)
          (pointedShearCoeffThree b)
          (pointedShearSectionTwo b)).trans h2
    simpa [coordinateAxisPoint] using h3
  · have h1zero :
        polynomialSectionSpecialPoint
            (pointedShearSectionOne b) 1 = 0 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_k_eq_zero
          (K := K) (1 : Fin 4) (by decide) b hb0
    have h2same :
        polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 1 =
          polynomialSectionSpecialPoint
            (pointedShearSectionOne b) 1 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_of_ne
          (K := K) (2 : Fin 4)
          (pointedShearCoeffTwo b)
          (pointedShearSectionOne b)
          (i := (1 : Fin 4)) (by decide)
    have h3same :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) 1 =
          polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 1 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_of_ne
          (K := K) (3 : Fin 4)
          (pointedShearCoeffThree b)
          (pointedShearSectionTwo b)
          (i := (1 : Fin 4)) (by decide)
    have hz :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) (1 : Fin 4) = 0 :=
      h3same.trans (h2same.trans h1zero)
    simpa [coordinateAxisPoint] using hz
  · have h10 :
        polynomialSectionSpecialPoint
            (pointedShearSectionOne b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (1 : Fin 4) (by decide)
          (pointedShearCoeffOne b) b).trans hb0
    have h2zero :
        polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 2 = 0 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_k_eq_zero
          (K := K) (2 : Fin 4) (by decide)
          (pointedShearSectionOne b) h10
    have h3same :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) 2 =
          polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 2 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_of_ne
          (K := K) (3 : Fin 4)
          (pointedShearCoeffThree b)
          (pointedShearSectionTwo b)
          (i := (2 : Fin 4)) (by decide)
    have hz :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) (2 : Fin 4) = 0 :=
      h3same.trans h2zero
    simpa [coordinateAxisPoint] using hz
  · have h10 :
        polynomialSectionSpecialPoint
            (pointedShearSectionOne b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (1 : Fin 4) (by decide)
          (pointedShearCoeffOne b) b).trans hb0
    have h20 :
        polynomialSectionSpecialPoint
            (pointedShearSectionTwo b) 0 = 1 := by
      exact
        (polynomialSectionSpecialPoint_elementaryUnshear_zero
          (K := K) (2 : Fin 4) (by decide)
          (pointedShearCoeffTwo b)
          (pointedShearSectionOne b)).trans h10
    have h3zero :
        polynomialSectionSpecialPoint
            (pointedShearNormalisedSection b) 3 = 0 := by
      exact
        polynomialSectionSpecialPoint_elementaryUnshear_k_eq_zero
          (K := K) (3 : Fin 4) (by decide)
          (pointedShearSectionTwo b) h20
    simpa [coordinateAxisPoint] using h3zero

/-- Three pointed shears preserve ordinary source homogeneity. -/
theorem pointedShearNormalisedFamily_isHomogeneous
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hP : P.IsHomogeneous D) :
    (pointedShearNormalisedFamily P b).IsHomogeneous D := by
  unfold pointedShearNormalisedFamily
  apply elementaryShearHom_isHomogeneous
  unfold pointedShearFamilyTwo
  apply elementaryShearHom_isHomogeneous
  unfold pointedShearFamilyOne
  exact
    elementaryShearHom_isHomogeneous
      (K := K)
      (1 : Fin 4) (pointedShearCoeffOne b)
      P hP

/-- Three pointed shears preserve the exact Hessian defect. -/
theorem pointedShearNormalisedFamily_preservesHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (pointedShearNormalisedFamily P b)
      Delta := by
  unfold pointedShearNormalisedFamily
  apply
    elementaryShearHom_preservesHessianDefect
      (K := K)
      (3 : Fin 4) (by decide)
      (pointedShearCoeffThree b)
  unfold pointedShearFamilyTwo
  apply
    elementaryShearHom_preservesHessianDefect
      (K := K)
      (2 : Fin 4) (by decide)
      (pointedShearCoeffTwo b)
  unfold pointedShearFamilyOne
  exact
    elementaryShearHom_preservesHessianDefect
      (K := K)
      (1 : Fin 4) (by decide)
      (pointedShearCoeffOne b)
      P hdef

/-- Three pointed shears preserve an exact collision from the zero section. -/
theorem pointedShearNormalisedFamily_preservesExactCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b) :
    HasPolynomialFamilyExactGradientCollision
      (pointedShearNormalisedFamily P b)
      (zeroPolynomialSection (K := K))
      (pointedShearNormalisedSection b) := by
  have h1 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K)
      (1 : Fin 4) (by decide)
      (pointedShearCoeffOne b)
      P
      (zeroPolynomialSection (K := K))
      b hcoll
  rw [elementaryUnshearSection_zero] at h1
  have h2 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K)
      (2 : Fin 4) (by decide)
      (pointedShearCoeffTwo b)
      (pointedShearFamilyOne P b)
      (zeroPolynomialSection (K := K))
      (pointedShearSectionOne b)
      (by simpa [pointedShearFamilyOne,
          pointedShearSectionOne] using h1)
  rw [elementaryUnshearSection_zero] at h2
  have h3 :=
    polynomialFamilyExactGradientCollision_elementaryShear
      (K := K)
      (3 : Fin 4) (by decide)
      (pointedShearCoeffThree b)
      (pointedShearFamilyTwo P b)
      (zeroPolynomialSection (K := K))
      (pointedShearSectionTwo b)
      (by simpa [pointedShearFamilyTwo,
          pointedShearSectionTwo] using h2)
  rw [elementaryUnshearSection_zero] at h3
  simpa [pointedShearNormalisedFamily,
    pointedShearNormalisedSection] using h3

/-! ## Application to a separated right Smith wall -/

/-- At a genuine Smith wall the transformed left section coming from the
identically-zero global section is still identically zero. -/
theorem alignedSmithGenuineFirstWallSectionLeft_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b) :
    alignedSmithGenuineFirstWallSectionLeft
        (K := K)
        P (zeroPolynomialSection (K := K)) b hwall =
      zeroPolynomialSection (K := K) := by
  funext i
  unfold alignedSmithGenuineFirstWallSectionLeft
  dsimp
  exact
    alignedSmithSection_zeroCoordinate
      (zeroPolynomialSection (K := K))
      (alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall)
      (alignedSmithGenuineFirstWall_integralSection_left
        P (zeroPolynomialSection (K := K)) b hwall)
      (by simp [zeroPolynomialSection])

/-- After the green `X^10` extraction, a separated right wall has a
canonical zero-section exact collision after the pointed shear. -/
theorem separatedRightSectionWall_pointedShearContinuation
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
      ∃ b' : Fin 4 → Polynomial K,
        P'.IsHomogeneous D ∧
        HasPolynomialFamilyHessianDefect
          (K := K) P'
          (alignedSmithRamificationIndex * (Delta - 2)) ∧
        HasPolynomialFamilyExactGradientCollision
          P'
          (zeroPolynomialSection (K := K))
          b' ∧
        polynomialSectionSpecialPoint b' =
          coordinateAxisPoint (K := K) (0 : Fin 4) := by
  let hwall := Classical.choose hsep
  let Q :=
    alignedSmithGenuineFirstWallFamily
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let a' :=
    alignedSmithGenuineFirstWallSectionLeft
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let b' :=
    alignedSmithGenuineFirstWallSectionRight
      (K := K) P
      (zeroPolynomialSection (K := K))
      b hwall
  let hcommon :=
    separatedRightSectionWall_commonParameterFactor_ten
      P b hsep hb
  let R :=
    commonParameterFactorFamily 10 Q hcommon
  have hRhom :
      R.IsHomogeneous D := by
    dsimp [R, Q, hcommon]
    exact
      separatedRightSectionWall_isHomogeneous_after_factor_ten
        P hP b hsep hb
  have hRdef :
      HasPolynomialFamilyHessianDefect
        (K := K) R
        (alignedSmithRamificationIndex * (Delta - 2)) := by
    dsimp [R, Q, hcommon]
    exact
      separatedRightSectionWall_hasHessianDefect_twenty_mul_sub_two
        P b hsep hdef hb
  have hRcollRaw :
      HasPolynomialFamilyExactGradientCollision
        R a' b' := by
    dsimp [R, Q, a', b', hcommon]
    exact
      separatedRightSectionWall_preservesExactCollision_after_factor_ten
        P b hsep hcoll hb
  have ha' :
      a' = zeroPolynomialSection (K := K) := by
    dsimp [a']
    exact
      alignedSmithGenuineFirstWallSectionLeft_zero
        P b hwall
  have hRcoll :
      HasPolynomialFamilyExactGradientCollision
        R
        (zeroPolynomialSection (K := K))
        b' := by
    rw [← ha']
    exact hRcollRaw
  have hb'0 :
      polynomialSectionSpecialPoint b' (0 : Fin 4) = 1 := by
    dsimp [b']
    exact
      genuineFirstWall_rightSpecialPoint_oneCoordinate
        P (zeroPolynomialSection (K := K)) b
        hwall hb
  let R' :=
    pointedShearNormalisedFamily R b'
  let b'' :=
    pointedShearNormalisedSection b'
  refine ⟨R', b'', ?_, ?_, ?_, ?_⟩
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_isHomogeneous
        R b' hRhom
  · dsimp [R']
    exact
      pointedShearNormalisedFamily_preservesHessianDefect
        R b' hRdef
  · dsimp [R', b'']
    exact
      pointedShearNormalisedFamily_preservesExactCollision
        R b' hRcoll
  · dsimp [b'']
    exact
      pointedShearNormalisedSection_specialPoint
        b' hb'0

/-- **The Phase-93.72 pointed continuation interface is no longer an
assumption.**

Under the actual geometric hypotheses of the canonical global state, every
separated right section wall admits a homogeneous exact-collision
continuation whose right special point is again `e0`.

The defect recorded here is the honest physical defect
`20*(Delta-2)` on the once-ramified scale. -/
theorem hasCanonicalContinuationFromSeparatedRightWall_of_geometricData
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D)
    (b : Fin 4 → Polynomial K)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    HasCanonicalContinuationFromSeparatedRightWall
      (K := K) D P b := by
  intro hsep
  rcases
      separatedRightSectionWall_pointedShearContinuation
        P hP b hsep hdef hcoll hb with
    ⟨P', b', hhom', hdef', hcoll', hb'⟩
  refine
    ⟨alignedSmithRamificationIndex * (Delta - 2),
      rankOneRepairState 0,
      P', b',
      hhom', hdef', hcoll', hb'⟩

/-!
The physical scale descent is intentionally left to the next phase.

This file now does one job only: it proves the pointed coordinate
continuation.  In particular, it no longer includes the premature y/z-vs-w
wall decomposition from the first 93.73 draft.
-/

end

end HC4.Valuation
