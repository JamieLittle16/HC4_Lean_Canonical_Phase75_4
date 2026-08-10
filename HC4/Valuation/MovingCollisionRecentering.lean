import HC4.Valuation.ParameterRamification
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import Mathlib.Tactic

/-!
# Exact recentering of a polynomial-family gradient collision

A terminal direct jump is an affine/local object.  Before taking a source
lattice initial form we must centre the family at one of the two moving
collision sections.

For

    P : K[tau][X_0,...,X_3]
    a : Fin 4 -> K[tau]

put

    Q(Y) = P(Y + a).

This file constructs that translation as an honest `MvPolynomial` ring
homomorphism and proves, without Laurent coefficients:

* exact evaluation covariance;
* partial derivatives commute with translation;
* Hessians and Hessian determinants commute with translation;
* a pure parameter Hessian defect is unchanged;
* an exact moving gradient collision `(a,b)` becomes the pointed collision
  `(0,b-a)`;
* the two special points are translated by the same affine difference.

Unlike the determinant-one shears used in the homogeneous restart spine,
translation need not preserve ordinary source homogeneity.  That is intended
here: after recentering, lower Taylor degrees can appear and the terminal
associated-graded fibre can have a nondegenerate quadratic part.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Coordinatewise difference of two polynomial moving sections. -/
def polynomialSectionDifference
    (a b : Fin 4 -> Polynomial K) :
    Fin 4 -> Polynomial K :=
  fun i => b i - a i

/-- Image of one source variable under translation by the moving section
`a`: `X_i |-> X_i + a_i`. -/
def polynomialFamilyTranslationVariable
    (a : Fin 4 -> Polynomial K)
    (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.X i + MvPolynomial.C (a i)

/-- Honest polynomial-ring translation by a moving section. -/
noncomputable def polynomialFamilyTranslationHom
    (a : Fin 4 -> Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom
    MvPolynomial.C
    (polynomialFamilyTranslationVariable (K := K) a)

@[simp] theorem polynomialFamilyTranslationHom_C
    (a : Fin 4 -> Polynomial K)
    (c : Polynomial K) :
    polynomialFamilyTranslationHom (K := K) a (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [polynomialFamilyTranslationHom]

@[simp] theorem polynomialFamilyTranslationHom_X
    (a : Fin 4 -> Polynomial K)
    (i : Fin 4) :
    polynomialFamilyTranslationHom (K := K) a (MvPolynomial.X i) =
      polynomialFamilyTranslationVariable (K := K) a i := by
  simp [polynomialFamilyTranslationHom]

/-- Evaluating the translated family at `b-a` recovers evaluation of the
original family at `b`. -/
theorem eval_polynomialFamilyTranslationHom_difference
    (a b : Fin 4 -> Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.eval
        (polynomialSectionDifference a b)
        (polynomialFamilyTranslationHom (K := K) a P) =
      MvPolynomial.eval b P := by
  change
    MvPolynomial.eval
        (polynomialSectionDifference a b)
        (MvPolynomial.eval₂
          MvPolynomial.C
          (polynomialFamilyTranslationVariable (K := K) a)
          P) =
      MvPolynomial.eval b P
  rw [← MvPolynomial.eval_assoc
    (polynomialFamilyTranslationVariable (K := K) a)
    (polynomialSectionDifference a b)
    P]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext i
  simp [polynomialFamilyTranslationVariable,
    polynomialSectionDifference]

/-- Recentring a section at itself gives the identically-zero section. -/
@[simp] theorem polynomialSectionDifference_self
    (a : Fin 4 -> Polynomial K) :
    polynomialSectionDifference a a =
      (fun _ : Fin 4 => (0 : Polynomial K)) := by
  funext i
  simp [polynomialSectionDifference]

/-- Partial derivatives commute exactly with translation. -/
theorem pderiv_polynomialFamilyTranslationHom
    (a : Fin 4 -> Polynomial K)
    (i : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv i
        (polynomialFamilyTranslationHom (K := K) a P) =
      polynomialFamilyTranslationHom (K := K) a
        (MvPolynomial.pderiv i P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp only [map_mul, polynomialFamilyTranslationHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hni : n = i
    · subst n
      simp [polynomialFamilyTranslationVariable]
    · simp [polynomialFamilyTranslationVariable, hni]

/-- Hessian entries commute with translation. -/
theorem hessian_polynomialFamilyTranslationHom_entry
    (a : Fin 4 -> Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (polynomialFamilyTranslationHom (K := K) a P) i j =
      polynomialFamilyTranslationHom (K := K) a
        (HC4.Polynomial.hessian P i j) := by
  rw [HC4.Polynomial.hessian_apply]
  rw [pderiv_polynomialFamilyTranslationHom]
  rw [pderiv_polynomialFamilyTranslationHom]
  rw [HC4.Polynomial.hessian_apply]

/-- The complete Hessian matrix is obtained by mapping the old Hessian
through the translation homomorphism. -/
theorem hessian_polynomialFamilyTranslationHom
    (a : Fin 4 -> Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian
        (polynomialFamilyTranslationHom (K := K) a P) =
      (polynomialFamilyTranslationHom (K := K) a).mapMatrix
        (HC4.Polynomial.hessian P) := by
  apply Matrix.ext
  intro i j
  exact hessian_polynomialFamilyTranslationHom_entry a P i j

/-- Hessian determinant is exactly translation-covariant. -/
theorem hessianDeterminant_polynomialFamilyTranslationHom
    (a : Fin 4 -> Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (polynomialFamilyTranslationHom (K := K) a P) =
      polynomialFamilyTranslationHom (K := K) a
        (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_polynomialFamilyTranslationHom]
  exact
    (RingHom.map_det
      (polynomialFamilyTranslationHom (K := K) a)
      (HC4.Polynomial.hessian P)).symm

/-- Pure parameter Hessian defect is unchanged by source translation. -/
theorem polynomialFamilyTranslationHom_preservesHessianDefect
    (a : Fin 4 -> Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (polynomialFamilyTranslationHom (K := K) a P)
      Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_polynomialFamilyTranslationHom]
  rw [hdef]
  simp

/-- Exact gradient collision becomes a pointed exact collision after
translation by the left moving section. -/
theorem polynomialFamilyExactGradientCollision_recenter
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 -> Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (polynomialFamilyTranslationHom (K := K) a P)
      (fun _ : Fin 4 => (0 : Polynomial K))
      (polynomialSectionDifference a b) := by
  intro i
  rw [pderiv_polynomialFamilyTranslationHom]
  calc
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (polynomialFamilyTranslationHom (K := K) a
          (MvPolynomial.pderiv i P)) =
      MvPolynomial.eval a (MvPolynomial.pderiv i P) := by
        simpa using
          (eval_polynomialFamilyTranslationHom_difference
            (K := K) a a (MvPolynomial.pderiv i P))
    _ = MvPolynomial.eval b (MvPolynomial.pderiv i P) := hcoll i
    _ = MvPolynomial.eval
        (polynomialSectionDifference a b)
        (polynomialFamilyTranslationHom (K := K) a
          (MvPolynomial.pderiv i P)) := by
        symm
        exact
          eval_polynomialFamilyTranslationHom_difference
            (K := K) a b (MvPolynomial.pderiv i P)

/-- Specialisation commutes with taking the coordinatewise section
difference. -/
theorem polynomialSectionSpecialPoint_difference
    (a b : Fin 4 -> Polynomial K) :
    polynomialSectionSpecialPoint
        (polynomialSectionDifference a b) =
      fun i => polynomialSectionSpecialPoint b i -
        polynomialSectionSpecialPoint a i := by
  funext i
  simp [polynomialSectionSpecialPoint, polynomialSectionDifference]

/-- If the old left special point is zero and the old right special point
is `e0`, the recentered right section still specialises to `e0`. -/
theorem polynomialSectionSpecialPoint_difference_eq_axis
    (a b : Fin 4 -> Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (polynomialSectionDifference a b) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  rw [polynomialSectionSpecialPoint_difference, ha, hb]
  funext i
  simp

/-- The recentered pointed collision descends immediately to the special
fibre. -/
theorem recenteredPolynomialFamily_specialFiber_exactCollision
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 -> Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber
        (polynomialFamilyTranslationHom (K := K) a P))
      (fun _ => (0 : K))
      (polynomialSectionSpecialPoint
        (polynomialSectionDifference a b)) := by
  have hrec :=
    polynomialFamilyExactGradientCollision_recenter
      (K := K) P a b hcoll
  have hspecial :=
    polynomialFamilyExactGradientCollision_specialFiber
      (polynomialFamilyTranslationHom (K := K) a P)
      (fun _ : Fin 4 => (0 : Polynomial K))
      (polynomialSectionDifference a b)
      hrec
  simpa [polynomialSectionSpecialPoint] using hspecial


/-- Translation by a moving section whose special point is the origin does
not change the parameter special fibre.  This is the exact compatibility
needed to rebuild the rigid Schur clock *after* affine recentering. -/
theorem polynomialFamilySpecialFiber_translation_eq_of_specialPoint_zero
    (a : Fin 4 -> Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ : Fin 4 => (0 : K)))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber
        (polynomialFamilyTranslationHom (K := K) a P) =
      polynomialFamilySpecialFiber P := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [polynomialFamilySpecialFiber]
  · intro p q hp hq
    have hadd :=
      congrArg₂
        (fun x y : MvPolynomial (Fin 4) K => x + y)
        hp hq
    simpa [polynomialFamilySpecialFiber] using hadd
  · intro p n hp
    have han : Polynomial.constantCoeff (a n) = 0 := by
      exact congrFun ha n
    have hmul :=
      congrArg
        (fun x : MvPolynomial (Fin 4) K =>
          x * MvPolynomial.X n)
        hp
    simpa [polynomialFamilySpecialFiber,
      polynomialFamilyTranslationVariable, han] using hmul

end

end HC4.Valuation
