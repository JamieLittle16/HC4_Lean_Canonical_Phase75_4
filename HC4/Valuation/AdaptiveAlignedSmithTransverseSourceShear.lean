import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Arbitrary transverse determinant-one source shears

`PointedShearContinuation` develops the exact covariance theory for the
special elementary shear

    X_k ↦ X_k + c X_0.

The direct-closing kernel analysis needs the same operation between two
arbitrary distinct source coordinates, while keeping the marked longitudinal
axis fixed.  This file proves the corresponding source-level statements for

    X_k ↦ X_k + c X_ell,   k ≠ ell.

When both `k` and `ell` are transverse (`≠ 0`), the inverse action fixes the
marked point `-e₀`.  Thus these shears may be used to align transverse
quadratic geometry without destroying the source-honest collision.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open Matrix

universe u

variable {K : Type u} [Field K]

/-- Source-variable image for the elementary transvection
`X_k ↦ X_k + c X_ell`. -/
def transverseSourceShearVariable
    (k ell : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  if i = k then
    MvPolynomial.X k +
      MvPolynomial.C c * MvPolynomial.X ell
  else
    MvPolynomial.X i

/-- Ring homomorphism implementing the arbitrary source transvection. -/
noncomputable def transverseSourceShearHom
    (k ell : Fin 4)
    (c : Polynomial K) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom
    MvPolynomial.C
    (transverseSourceShearVariable (K := K) k ell c)

/-- Inverse action of the same transvection on a polynomial moving section. -/
def transverseSourceUnshearSection
    (k ell : Fin 4)
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  fun i =>
    if i = k then
      a i - c * a ell
    else
      a i

@[simp] theorem transverseSourceUnshearSection_zero
    (k ell : Fin 4)
    (c : Polynomial K) :
    transverseSourceUnshearSection
        k ell c (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  by_cases hi : i = k <;>
    simp [transverseSourceUnshearSection,
      zeroPolynomialSection, hi]

/-- Evaluation of a sheared variable at the inverse-sheared section recovers
its original source coordinate. -/
theorem eval_transverseSourceShearVariable_unshear
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K)
    (i : Fin 4) :
    MvPolynomial.eval
        (transverseSourceUnshearSection k ell c a)
        (transverseSourceShearVariable (K := K) k ell c i) =
      a i := by
  by_cases hik : i = k
  · subst i
    have hlk : ell ≠ k := Ne.symm hkl
    simp [transverseSourceShearVariable,
      transverseSourceUnshearSection, hkl, hlk]
  · simp [transverseSourceShearVariable,
      transverseSourceUnshearSection, hik]

/-- Exact evaluation covariance of the arbitrary source transvection. -/
theorem eval_transverseSourceShearHom_unshear
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval
        (transverseSourceUnshearSection k ell c a)
        (transverseSourceShearHom (K := K) k ell c P) =
      MvPolynomial.eval a P := by
  change
    MvPolynomial.eval
        (transverseSourceUnshearSection k ell c a)
        (MvPolynomial.eval₂
          MvPolynomial.C
          (transverseSourceShearVariable (K := K) k ell c)
          P) =
      MvPolynomial.eval a P
  rw [← MvPolynomial.eval_assoc
    (transverseSourceShearVariable (K := K) k ell c)
    (transverseSourceUnshearSection k ell c a)
    P]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext i
  exact eval_transverseSourceShearVariable_unshear
    k ell hkl c a i

/-! ## Homogeneity and degree preservation -/

/-- Every arbitrary shear variable is an ordinary linear source form. -/
theorem transverseSourceShearVariable_isHomogeneous_one
    (k ell : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    (transverseSourceShearVariable (K := K) k ell c i).IsHomogeneous 1 := by
  by_cases hik : i = k
  · subst i
    unfold transverseSourceShearVariable
    simp only [if_pos rfl]
    exact
      (MvPolynomial.isHomogeneous_X
          (Polynomial K) k).add
        (MvPolynomial.isHomogeneous_C_mul_X
          c ell)
  · unfold transverseSourceShearVariable
    rw [if_neg hik]
    exact MvPolynomial.isHomogeneous_X (Polynomial K) i

/-- An arbitrary source transvection preserves ordinary source homogeneity. -/
theorem transverseSourceShearHom_isHomogeneous
    {D : ℕ}
    (k ell : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P.IsHomogeneous D) :
    (transverseSourceShearHom (K := K) k ell c P).IsHomogeneous D := by
  have hout :=
    hP.eval₂
      MvPolynomial.C
      (transverseSourceShearVariable (K := K) k ell c)
      (fun r => MvPolynomial.isHomogeneous_C (Fin 4) r)
      (fun i =>
        transverseSourceShearVariable_isHomogeneous_one
          (K := K) k ell c i)
  simpa [transverseSourceShearHom] using hout

@[simp] theorem transverseSourceShearHom_C
    (k ell : Fin 4)
    (c r : Polynomial K) :
    transverseSourceShearHom (K := K) k ell c (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [transverseSourceShearHom]

@[simp] theorem transverseSourceShearHom_X
    (k ell : Fin 4)
    (c : Polynomial K)
    (i : Fin 4) :
    transverseSourceShearHom (K := K) k ell c (MvPolynomial.X i) =
      transverseSourceShearVariable (K := K) k ell c i := by
  simp [transverseSourceShearHom]

/-- The arbitrary linear transvection preserves every nonlinear source-degree
ceiling. -/
theorem nonlinearDegreeBound_transverseSourceShear
    (m : ℕ)
    (k ell : Fin 4)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m
      (transverseSourceShearHom (K := K) k ell c P) := by
  apply nonlinearDegreeBound_map_of_monomial_homogeneous
    (transverseSourceShearHom (K := K) k ell c) P m hP
  intro n r
  have hhom :
      (MvPolynomial.monomial n r).IsHomogeneous n.degree :=
    MvPolynomial.isHomogeneous_monomial r rfl
  exact transverseSourceShearHom_isHomogeneous k ell c
    (MvPolynomial.monomial n r) hhom

/-! ## First-order chain rule -/

/-- Away from the source coordinate `ell`, the transvection has the identity
chain rule. -/
theorem pderiv_transverseSourceShearHom_of_ne_source
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (j : Fin 4)
    (hjl : j ≠ ell)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv j
        (transverseSourceShearHom (K := K) k ell c P) =
      transverseSourceShearHom (K := K) k ell c
        (MvPolynomial.pderiv j P) := by
  apply MvPolynomial.induction_on P
  · intro r
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp only [map_mul, transverseSourceShearHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnk : n = k
    · subst n
      by_cases hkj : k = j
      · subst j
        simp [transverseSourceShearVariable, hkl] <;> ring
      · have hjk : j ≠ k := Ne.symm hkj
        simp [transverseSourceShearVariable,
          hkl, hkj, hjk, hjl] <;> ring
    · by_cases hnj : n = j
      · subst n
        have hjk : j ≠ k := by
          intro h
          exact hnk h
        simp [transverseSourceShearVariable, hnk, hjk, hjl] <;> ring
      · have hjn : j ≠ n := Ne.symm hnj
        simp [transverseSourceShearVariable,
          hnk, hnj, hjn, hjl] <;> ring

/-- In the source direction `ell`, the chain rule has one additional
`k`-component. -/
theorem pderiv_source_transverseSourceShearHom
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv ell
        (transverseSourceShearHom (K := K) k ell c P) =
      transverseSourceShearHom (K := K) k ell c
          (MvPolynomial.pderiv ell P) +
        MvPolynomial.C c *
          transverseSourceShearHom (K := K) k ell c
            (MvPolynomial.pderiv k P) := by
  apply MvPolynomial.induction_on P
  · intro r
    simp
  · intro p q hp hq
    simp [hp, hq, mul_add, add_mul] <;> ring
  · intro p n hp
    simp only [map_mul, transverseSourceShearHom_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnl : n = ell
    · subst n
      have hlk : ell ≠ k := Ne.symm hkl
      simp [transverseSourceShearVariable, hkl, hlk]
      ring
    · by_cases hnk : n = k
      · subst n
        have hlk : ell ≠ k := Ne.symm hkl
        simp [transverseSourceShearVariable, hkl, hlk]
        ring
      · have hln : ell ≠ n := Ne.symm hnl
        simp [transverseSourceShearVariable, hnl, hln, hnk, hkl]
        ring

/-! ## Hessian congruence -/

/-- Right source matrix of the arbitrary transvection. -/
def transverseSourceShearMatrix
    (k ell : Fin 4)
    (c : Polynomial K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
  Matrix.transvection k ell (MvPolynomial.C c)

/-- Left transpose source matrix of the arbitrary transvection. -/
def transverseSourceShearTransposeMatrix
    (k ell : Fin 4)
    (c : Polynomial K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
  Matrix.transvection ell k (MvPolynomial.C c)

/-- Entrywise Hessian covariance under the arbitrary transvection. -/
theorem hessian_transverseSourceShearHom
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessian
        (transverseSourceShearHom (K := K) k ell c P) =
      transverseSourceShearTransposeMatrix (K := K) k ell c *
        (transverseSourceShearHom (K := K) k ell c).mapMatrix
          (HC4.Polynomial.hessian P) *
        transverseSourceShearMatrix (K := K) k ell c := by
  apply Matrix.ext
  intro i j
  let A :
      Matrix (Fin 4) (Fin 4)
        (MvPolynomial (Fin 4) (Polynomial K)) :=
    (transverseSourceShearHom (K := K) k ell c).mapMatrix
      (HC4.Polynomial.hessian P)
  by_cases hil : i = ell
  · subst i
    by_cases hjl : j = ell
    · subst j
      rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_source_transverseSourceShearHom k ell hkl c P]
      rw [map_add, MvPolynomial.pderiv_C_mul]
      rw [pderiv_source_transverseSourceShearHom
        k ell hkl c (MvPolynomial.pderiv ell P)]
      rw [pderiv_source_transverseSourceShearHom
        k ell hkl c (MvPolynomial.pderiv k P)]
      have hleftell :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              ell ell =
            A ell ell + MvPolynomial.C c * A k ell := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_same
          ell k ell (MvPolynomial.C c) A
      have hleftk :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              ell k =
            A ell k + MvPolynomial.C c * A k k := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_same
          ell k k (MvPolynomial.C c) A
      have hright :
          ((transverseSourceShearTransposeMatrix (K := K) k ell c * A) *
              transverseSourceShearMatrix (K := K) k ell c)
              ell ell =
            (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
                ell ell +
              MvPolynomial.C c *
                (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
                  ell k := by
        unfold transverseSourceShearMatrix
        exact Matrix.mul_transvection_apply_same
          k ell ell (MvPolynomial.C c)
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
      rw [hright, hleftell, hleftk]
      simp [A, HC4.Polynomial.hessian_apply] <;> ring
    · rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_source_transverseSourceShearHom k ell hkl c P]
      rw [map_add, MvPolynomial.pderiv_C_mul]
      rw [pderiv_transverseSourceShearHom_of_ne_source
        k ell hkl c j hjl (MvPolynomial.pderiv ell P)]
      rw [pderiv_transverseSourceShearHom_of_ne_source
        k ell hkl c j hjl (MvPolynomial.pderiv k P)]
      have hleft :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              ell j =
            A ell j + MvPolynomial.C c * A k j := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_same
          ell k j (MvPolynomial.C c) A
      have hright :
          ((transverseSourceShearTransposeMatrix (K := K) k ell c * A) *
              transverseSourceShearMatrix (K := K) k ell c)
              ell j =
            (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              ell j := by
        unfold transverseSourceShearMatrix
        exact Matrix.mul_transvection_apply_of_ne
          k ell ell j hjl (MvPolynomial.C c)
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
      rw [hright, hleft]
      simp [A, HC4.Polynomial.hessian_apply]
  · by_cases hjl : j = ell
    · subst j
      rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_transverseSourceShearHom_of_ne_source
        k ell hkl c i hil P]
      rw [pderiv_source_transverseSourceShearHom
        k ell hkl c (MvPolynomial.pderiv i P)]
      have hleftell :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              i ell =
            A i ell := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_of_ne
          ell k i ell hil (MvPolynomial.C c) A
      have hleftk :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              i k =
            A i k := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_of_ne
          ell k i k hil (MvPolynomial.C c) A
      have hright :
          ((transverseSourceShearTransposeMatrix (K := K) k ell c * A) *
              transverseSourceShearMatrix (K := K) k ell c)
              i ell =
            (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
                i ell +
              MvPolynomial.C c *
                (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
                  i k := by
        unfold transverseSourceShearMatrix
        exact Matrix.mul_transvection_apply_same
          k ell i (MvPolynomial.C c)
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
      rw [hright, hleftell, hleftk]
      simp [A, HC4.Polynomial.hessian_apply]
    · rw [HC4.Polynomial.hessian_apply]
      rw [pderiv_transverseSourceShearHom_of_ne_source
        k ell hkl c i hil P]
      rw [pderiv_transverseSourceShearHom_of_ne_source
        k ell hkl c j hjl (MvPolynomial.pderiv i P)]
      have hleft :
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              i j = A i j := by
        unfold transverseSourceShearTransposeMatrix
        exact Matrix.transvection_mul_apply_of_ne
          ell k i j hil (MvPolynomial.C c) A
      have hright :
          ((transverseSourceShearTransposeMatrix (K := K) k ell c * A) *
              transverseSourceShearMatrix (K := K) k ell c)
              i j =
            (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
              i j := by
        unfold transverseSourceShearMatrix
        exact Matrix.mul_transvection_apply_of_ne
          k ell i j hjl (MvPolynomial.C c)
          (transverseSourceShearTransposeMatrix (K := K) k ell c * A)
      rw [hright, hleft]
      simp [A, HC4.Polynomial.hessian_apply]

/-- Both source-transvection matrices have determinant one. -/
theorem det_transverseSourceShearMatrices
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K) :
    (transverseSourceShearMatrix (K := K) k ell c).det = 1 ∧
      (transverseSourceShearTransposeMatrix (K := K) k ell c).det = 1 := by
  constructor
  · unfold transverseSourceShearMatrix
    exact Matrix.det_transvection_of_ne
      k ell hkl (MvPolynomial.C c)
  · unfold transverseSourceShearTransposeMatrix
    exact Matrix.det_transvection_of_ne
      ell k (Ne.symm hkl) (MvPolynomial.C c)

/-- Exact Hessian-determinant covariance under the arbitrary determinant-one
source transvection. -/
theorem hessianDeterminant_transverseSourceShearHom
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (transverseSourceShearHom (K := K) k ell c P) =
      transverseSourceShearHom (K := K) k ell c
        (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_transverseSourceShearHom k ell hkl c P]
  rw [Matrix.det_mul, Matrix.det_mul]
  rcases det_transverseSourceShearMatrices (K := K) k ell hkl c with
    ⟨hright, hleft⟩
  rw [hleft, hright]
  simp
  exact
    (RingHom.map_det
      (transverseSourceShearHom (K := K) k ell c)
      (HC4.Polynomial.hessian P)).symm

/-- Pure polynomial-family Hessian defect is unchanged by an arbitrary
source transvection. -/
theorem transverseSourceShearHom_preservesHessianDefect
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (transverseSourceShearHom (K := K) k ell c P)
      Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_transverseSourceShearHom k ell hkl c P]
  rw [hdef]
  simp [transverseSourceShearHom]

/-! ## Exact collision covariance -/

/-- An exact family-gradient collision survives the arbitrary source
transvection when both sections are transformed by the inverse shear. -/
theorem polynomialFamilyExactGradientCollision_transverseSourceShear
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (transverseSourceShearHom (K := K) k ell c P)
      (transverseSourceUnshearSection k ell c a)
      (transverseSourceUnshearSection k ell c b) := by
  intro i
  by_cases hil : i = ell
  · subst i
    rw [pderiv_source_transverseSourceShearHom k ell hkl c P]
    have hell := hcoll ell
    have hk := hcoll k
    have hsum :=
      congrArg₂
        (fun x y : Polynomial K => x + c * y)
        hell hk
    simpa [eval_transverseSourceShearHom_unshear
      (K := K) k ell hkl c] using hsum
  · rw [pderiv_transverseSourceShearHom_of_ne_source
      k ell hkl c i hil P]
    rw [eval_transverseSourceShearHom_unshear
      (K := K) k ell hkl c]
    rw [eval_transverseSourceShearHom_unshear
      (K := K) k ell hkl c]
    exact hcoll i

/-! ## Marked-axis preservation for genuinely transverse shears -/

/-- A transvection whose target is transverse fixes coordinate `0` of every
section. -/
theorem polynomialSectionSpecialPoint_transverseUnshear_zero
    (k ell : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K)
    (a : Fin 4 → Polynomial K) :
    polynomialSectionSpecialPoint
        (transverseSourceUnshearSection k ell c a)
        (0 : Fin 4) =
      polynomialSectionSpecialPoint a (0 : Fin 4) := by
  have h0k : (0 : Fin 4) ≠ k := Ne.symm hk0
  simp [polynomialSectionSpecialPoint,
    transverseSourceUnshearSection, h0k]

/-- If both shear directions are transverse, the marked polynomial section
`-e₀` is fixed exactly by the inverse source shear. -/
theorem transverseSourceUnshearSection_negAxis_zero
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (hk0 : k ≠ (0 : Fin 4))
    (hell0 : ell ≠ (0 : Fin 4))
    (c : Polynomial K) :
    transverseSourceUnshearSection
        k ell c
        (fun i : Fin 4 =>
          if i = (0 : Fin 4) then -(1 : Polynomial K) else 0) =
      (fun i : Fin 4 =>
        if i = (0 : Fin 4) then -(1 : Polynomial K) else 0) := by
  funext i
  by_cases hik : i = k
  · subst i
    have hk0' : k ≠ (0 : Fin 4) := hk0
    have hell0' : ell ≠ (0 : Fin 4) := hell0
    simp [transverseSourceUnshearSection, hkl, hk0', hell0']
  · simp [transverseSourceUnshearSection, hik]

end

end HC4.Valuation
