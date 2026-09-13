import HC4.Valuation.ParameterGapDualJet
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.RankThreeMvSubstitution
import Mathlib.Tactic

/-!
# First actual planar-contact layer -> locked-binomial first variation

This file is representation plumbing between the singular planar-contact Rees
family and the state-free locked-binomial first-variation calculation.

For an arbitrary polynomial family `P` with a genuine least positive actual
parameter layer `q`, we:

1. Euler-scale the spatial Hessian;
2. move the family parameter to the outer polynomial variable;
3. specialise the spatial rank-three line `x0 = T`, `x1=x2=x3=1`;
4. take the exact `(0,q)` dual-number gap jet.

Because `q` is the least *actual* positive source layer, every entry has the
required coefficient gap.  If `det Hess(P)=0`, the dual determinant has zero
nilpotent part.  Therefore, once the special fibre and first actual layer are
identified with the locked and parallel moment Hessians, the state-free
factorisation forces the affine two-root Euler equation.

No A19 state, blocker clock, JC2 input, or repair object occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact parameter layer extraction commutes with source Euler operators. -/
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

/-- Consequently exact parameter layers commute with the Euler-scaled Hessian. -/
theorem familyParameterLayer_eulerScaledHessian_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) (i j : Fin 4) :
    familyParameterLayer (HC4.Polynomial.eulerScaledHessian P i j) n =
      HC4.Polynomial.eulerScaledHessian (familyParameterLayer P n) i j := by
  unfold HC4.Polynomial.eulerScaledHessian
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [familyParameterLayer_sub_exact,
      familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic]
  · simp only [if_neg hij, sub_zero]
    rw [familyParameterLayer_mvEuler_generic,
      familyParameterLayer_mvEuler_generic]

/-- Euler-scaled Hessian with the family parameter moved to the outer
polynomial variable. -/
noncomputable def parameterFirstEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstEquiv K).toRingEquiv.mapMatrix
    (HC4.Polynomial.eulerScaledHessian P)

/-- Coefficient `n` is exactly the Euler-scaled Hessian of the exact source
layer `P_n`. -/
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

/-- Ring-level Euler scaling identity.  The older owner states this over a
field, but its proof is purely commutative-ring algebra and the family
coefficient ring is `Polynomial K`. -/
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

/-- A singular polynomial family has identically zero determinant after the
parameter-first Euler-Hessian conversion. -/
theorem parameterFirstEulerHessian_det_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    (parameterFirstEulerHessian P).det = 0 := by
  unfold parameterFirstEulerHessian
  rw [← RingHom.map_det]
  rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant_commRing,
    hdet, mul_zero, map_zero]

/-- Specialise the spatial coefficient of the parameter-first Euler Hessian to
the rank-three line. -/
noncomputable def specialisedParameterFirstEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  (Polynomial.mapRingHom
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))).mapMatrix
      (parameterFirstEulerHessian P)

/-- Coefficients of the specialised parameter-first matrix are literally the
specialised Euler-Hessian layers. -/
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

/-- The specialised matrix is still singular as a polynomial matrix. -/
theorem specialisedParameterFirstEulerHessian_det_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    (specialisedParameterFirstEulerHessian P).det = 0 := by
  unfold specialisedParameterFirstEulerHessian
  rw [← RingHom.map_det]
  rw [parameterFirstEulerHessian_det_eq_zero P hdet, map_zero]

/-- The least positive actual source layer gives a genuine coefficient gap in
every specialised Euler-Hessian entry. -/
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

/-- The exact `(0,q)` dual jet of the specialised Euler Hessian. -/
noncomputable def firstActualSpecialisedEulerDualJet
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    Matrix (Fin 4) (Fin 4) (DualNumber (Polynomial K)) :=
  matrixParameterGapDualJet
    (firstPositiveActualParameterOrder_pos P h)
    (specialisedParameterFirstEulerHessian P)
    (specialisedParameterFirstEulerHessian_hasGap P h)

/-- Its constant and nilpotent entries are the specialised Euler Hessians of
the special fibre and first actual layer. -/
theorem firstActualSpecialisedEulerDualJet_apply
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

/-- Singularity of the whole family kills the nilpotent determinant of the
first-actual-layer dual jet. -/
theorem firstActualSpecialisedEulerDualJet_det_snd_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (hdet : HC4.Polynomial.hessianDeterminant P = 0) :
    TrivSqZeroExt.snd (firstActualSpecialisedEulerDualJet P h).det = 0 := by
  rw [firstActualSpecialisedEulerDualJet]
  rw [snd_det_matrixParameterGapDualJet]
  rw [specialisedParameterFirstEulerHessian_det_eq_zero P hdet]
  simp

/-- **First-variation moment bridge.**

If the special fibre and first actual layer specialise to the locked and
parallel rank-three moment Hessians, singularity of the whole family forces
the affine two-root Euler equation on the first-layer profile. -/
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
    simp [HC4.Polynomial.lockedParallelFirstVariationDualPencil,
      hz, hf]
  have hnil := firstActualSpecialisedEulerDualJet_det_snd_eq_zero P h hdet
  rw [hjet] at hnil
  exact
    HC4.Polynomial.affineTwoRootEulerOperator_eq_zero_of_lockedParallel_snd_det_eq_zero
      V ell k j hV hell hk a b ha hb phi hnil

end

end HC4.Valuation
