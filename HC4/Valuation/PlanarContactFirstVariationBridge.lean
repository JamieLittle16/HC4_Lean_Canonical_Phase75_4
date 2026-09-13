import HC4.Valuation.ParameterGapDualJet
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeMvSubstitution
import Mathlib.Tactic

/-!
# First actual planar-contact layer -> locked-binomial first variation

This file contains only representation plumbing.  For a polynomial family
`P` with least positive actual parameter layer `q`, it Euler-scales the
spatial Hessian, moves the family parameter to the outer polynomial variable,
specialises the source variables to the standard rank-three line, and takes
the exact `(0,q)` dual-number jet.

Because `q` is the least actual positive source layer, every matrix entry has
the same parameter gap.  Hence singularity of the whole family kills the
nilpotent determinant of the jet.  Once the special fibre and the first layer
are identified with the locked and parallel moment Hessians, the state-free
first-variation factorisation gives the affine two-root Euler equation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact parameter-layer extraction is additive over subtraction. -/
theorem familyParameterLayer_sub_generic
    (F G : MvPolynomial (Fin 4) (Polynomial K)) (q : ℕ) :
    familyParameterLayer (F - G) q =
      familyParameterLayer F q - familyParameterLayer G q := by
  apply MvPolynomial.ext
  intro d
  simp [familyParameterLayer_coeff]

/-- Exact parameter-layer extraction commutes with source Euler operators. -/
theorem familyParameterLayer_mvEuler_generic
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i : Fin 4) :
    familyParameterLayer (HC4.Polynomial.mvEuler i P) n =
      HC4.Polynomial.mvEuler i (familyParameterLayer P n) := by
  apply MvPolynomial.ext
  intro d
  simp only [familyParameterLayer_coeff, coeff_mvEuler]
  have h := Polynomial.coeff_mul_natCast
    (R := K) (p := MvPolynomial.coeff d P) (a := d i) (k := n)
  simpa [mul_comm] using h

/-- Exact parameter layers commute with the Euler-scaled Hessian. -/
theorem familyParameterLayer_eulerScaledHessian_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i j : Fin 4) :
    familyParameterLayer (HC4.Polynomial.eulerScaledHessian P i j) n =
      HC4.Polynomial.eulerScaledHessian (familyParameterLayer P n) i j := by
  unfold HC4.Polynomial.eulerScaledHessian
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [familyParameterLayer_sub_generic,
      familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic]
  · simp only [if_neg hij, sub_zero]
    rw [familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic]

/-- Euler-scaled Hessian with the family parameter outermost. -/
noncomputable def parameterFirstEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstEquiv K).toRingEquiv.mapMatrix
    (HC4.Polynomial.eulerScaledHessian P)

/-- Outer coefficient `n` is the Euler-scaled Hessian of source layer `P_n`. -/
theorem parameterFirstEulerHessian_coeff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i j : Fin 4) :
    (parameterFirstEulerHessian P i j).coeff n =
      HC4.Polynomial.eulerScaledHessian (familyParameterLayer P n) i j := by
  change
    (parameterFirstEquiv K
      (HC4.Polynomial.eulerScaledHessian P i j)).coeff n = _
  rw [parameterFirstEquiv_coeff,
    familyParameterLayer_eulerScaledHessian_apply]

/-- Euler row/column scaling identity over an arbitrary commutative ring. -/
theorem det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant_commRing
    {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin 4) R) :
    (HC4.Polynomial.eulerScaledHessian P).det =
      (∏ i : Fin 4, MvPolynomial.X i)^2 *
        HC4.Polynomial.hessianDeterminant P := by
  let D : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) R) :=
    Matrix.diagonal (fun i => MvPolynomial.X i)
  let H : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) R) :=
    Matrix.transpose (HC4.Polynomial.hessian P)
  have hmatrix : HC4.Polynomial.eulerScaledHessian P = D * H * D := by
    apply Matrix.ext
    intro i j
    simp [D, H, HC4.Polynomial.eulerScaledHessian_apply,
      HC4.Polynomial.hessian_apply]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [D, H, HC4.Polynomial.hessianDeterminant]
  ring

/-- A singular family remains singular after parameter-first Euler scaling. -/
theorem parameterFirstEulerHessian_det_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    (parameterFirstEulerHessian P).det = 0 := by
  calc
    (parameterFirstEulerHessian P).det =
        parameterFirstEquiv K
          ((HC4.Polynomial.eulerScaledHessian P).det) := by
      unfold parameterFirstEulerHessian
      exact
        (RingEquiv.map_det
          (parameterFirstEquiv K).toRingEquiv
          (HC4.Polynomial.eulerScaledHessian P)).symm
    _ = 0 := by
      rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant_commRing,
        hdet, mul_zero]
      simp

/-- Spatial rank-three specialisation of the parameter-first Euler Hessian. -/
noncomputable def specialisedParameterFirstEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  (Polynomial.mapRingHom
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))).mapMatrix
      (parameterFirstEulerHessian P)

/-- Its coefficient `n` is the specialised Euler Hessian of source layer `n`. -/
theorem specialisedParameterFirstEulerHessian_coeff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i j : Fin 4) :
    (specialisedParameterFirstEulerHessian P i j).coeff n =
      HC4.Polynomial.rankThreeLineSpecialisation
        (HC4.Polynomial.eulerScaledHessian
          (familyParameterLayer P n) i j) := by
  unfold specialisedParameterFirstEulerHessian
  simp only [RingHom.mapMatrix_apply, Polynomial.coeff_map]
  rw [parameterFirstEulerHessian_coeff]

/-- Spatial specialisation preserves the zero determinant. -/
theorem specialisedParameterFirstEulerHessian_det_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    (specialisedParameterFirstEulerHessian P).det = 0 := by
  let f := Polynomial.mapRingHom
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))
  calc
    (specialisedParameterFirstEulerHessian P).det =
        f ((parameterFirstEulerHessian P).det) := by
      unfold specialisedParameterFirstEulerHessian
      exact (RingHom.map_det f (parameterFirstEulerHessian P)).symm
    _ = 0 := by
      rw [parameterFirstEulerHessian_det_eq_zero P hdet]
      simp [f]

/-- Minimality of the first positive actual source layer gives a common gap in
all specialised Euler-Hessian entries. -/
theorem specialisedParameterFirstEulerHessian_hasGap
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (i j : Fin 4) :
    HasNoPositiveParameterCoeffBelow
      (firstPositiveActualParameterOrder P h)
      (specialisedParameterFirstEulerHessian P i j) := by
  intro n hnpos hnlt
  rw [specialisedParameterFirstEulerHessian_coeff]
  rw [familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    P h hnpos hnlt]
  simp [HC4.Polynomial.eulerScaledHessian]

/-- Exact `(0,q)` dual jet of the specialised Euler Hessian. -/
noncomputable def firstActualSpecialisedEulerDualJet
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    Matrix (Fin 4) (Fin 4) (DualNumber (Polynomial K)) :=
  matrixParameterGapDualJet
    (firstPositiveActualParameterOrder_pos P h)
    (specialisedParameterFirstEulerHessian P)
    (specialisedParameterFirstEulerHessian_hasGap P h)

@[simp] theorem firstActualSpecialisedEulerDualJet_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (i j : Fin 4) :
    firstActualSpecialisedEulerDualJet P h i j =
      (HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P 0) i j),
       HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P
              (firstPositiveActualParameterOrder P h)) i j)) := by
  rw [firstActualSpecialisedEulerDualJet,
    matrixParameterGapDualJet_apply]
  rw [specialisedParameterFirstEulerHessian_coeff,
    specialisedParameterFirstEulerHessian_coeff]

/-- Singularity kills the nilpotent determinant coefficient of the first jet. -/
theorem firstActualSpecialisedEulerDualJet_det_snd_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    TrivSqZeroExt.snd (firstActualSpecialisedEulerDualJet P h).det = 0 := by
  rw [firstActualSpecialisedEulerDualJet]
  rw [snd_det_matrixParameterGapDualJet]
  rw [specialisedParameterFirstEulerHessian_det_eq_zero P hdet]
  simp

/-- **First-variation moment bridge.**  Exact moment identification of the
special fibre and first actual layer turns family singularity into the
state-free affine two-root Euler equation. -/
theorem affineTwoRootEulerOperator_eq_zero_of_firstActual_moment_identification
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (hdet : HC4.Polynomial.hessianDeterminant P = 0)
    (V ell k j : ℕ)
    (hV : 0 < V) (hell : 0 < ell) (hk : 1 ≤ k)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (phi : Polynomial K)
    (hzero :
      (fun r s =>
        HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P 0) r s)) =
        HC4.Polynomial.lockedBinomialMomentHessian V ell a b)
    (hfirst :
      (fun r s =>
        HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer P
              (firstPositiveActualParameterOrder P h)) r s)) =
        HC4.Polynomial.parallelStaircaseMomentHessian V k j phi) :
    HC4.Polynomial.affineTwoRootEulerOperator
      (a * ((ell : K) + 1)) (b * (ell : K)) (k - 1) phi = 0 := by
  have hjet :
      firstActualSpecialisedEulerDualJet P h =
        HC4.Polynomial.lockedParallelFirstVariationDualPencil
          V ell k j a b phi := by
    apply Matrix.ext
    intro r s
    rw [firstActualSpecialisedEulerDualJet_apply]
    have hz := congrFun (congrFun hzero r) s
    have hf := congrFun (congrFun hfirst r) s
    change (_, _) = (_, _)
    exact Prod.ext hz hf
  have hnil := firstActualSpecialisedEulerDualJet_det_snd_eq_zero P h hdet
  rw [hjet] at hnil
  exact
    HC4.Polynomial.affineTwoRootEulerOperator_eq_zero_of_lockedParallel_snd_det_eq_zero
      V ell k j hV hell hk a b ha hb phi hnil

end

end HC4.Valuation
