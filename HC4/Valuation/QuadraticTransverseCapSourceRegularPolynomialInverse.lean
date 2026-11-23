import HC4.Valuation.QuadraticTransverseCapSourceMatrixRiccati
import HC4.Valuation.QuadraticTransverseCapSourceRankThreeRiccatiBridge
import Mathlib.Tactic

/-!
# The regular quadratic-cap source has polynomially invertible transverse Hessian

This closes the missing source-to-Riccati implication in the rank-three
reciprocal-rigidity path: the Riccati equation is DERIVED from the
actual source F, not assumed.

A K-derivation on RatFunc K satisfying D(X)=1 is still a
differential-algebra construction obligation. The next theorem
constructs it; no claim of full source automorphism is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K] [CharZero K]

/-- From the actual determinant-one quadratic-cap source, the regular
transverse block C(x) has a polynomial TWO-SIDED inverse and a
nonzero constant determinant.

The only remaining input is a derivation of the rational function
field with D X = 1; importantly the source Riccati equation is
NO LONGER A HYPOTHESIS. -/
theorem quadraticTransverseCapSource_regularPolynomialInverse_of_derivation
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * P = 1 ∧
      P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
      ∃ d : K, d ≠ 0 ∧
        (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
          Polynomial.C d := by
  classical
  let C : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let f : Polynomial K →+* RatFunc K :=
    algebraMap (Polynomial K) (RatFunc K)
  let Cr : Matrix (Fin 3) (Fin 3) (RatFunc K) := C.map f
  let C' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.derivative (C i j)
  let C'' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.derivative (Polynomial.derivative (C i j))
  let dd := quadraticTransverse_fieldMatrixDerivative D
  have hpoly :=
    quadraticTransverse_ratFunc_derivation_polynomialCompatibility D hX
  have hd1 : dd Cr = C'.map f := by
    ext i j
    change D (f (C i j)) = f (Polynomial.derivative (C i j))
    exact hpoly (C i j)
  have hd2 : dd (dd Cr) = C''.map f := by
    rw [hd1]
    ext i j
    change D (f (Polynomial.derivative (C i j))) =
      f (Polynomial.derivative (Polynomial.derivative (C i j)))
    exact hpoly (Polynomial.derivative (C i j))
  have hdetMap : Cr.det = f C.det := (f.map_det C).symm
  have hprod :
      ((C' * C.adjugate) * C').map f =
        ((C'.map f * Cr.adjugate) * C'.map f) := by
    calc
      ((C' * C.adjugate) * C').map f =
          ((C'.map f * C.adjugate.map f) * C'.map f) := by
            simp only [Matrix.map_mul]
      _ = ((C'.map f * Cr.adjugate) * C'.map f) := by
            rw [f.map_adjugate C]
  have hsrc :=
    quadraticTransverseCapSource_matrixRiccati F hcap hdet
  have hsrcIJ (i j : Fin 3) :
      C.det * C'' i j =
        2 * (((C' * C.adjugate) * C') i j) := by
    have h := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) (Polynomial K) => M i j) hsrc
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  have hmain :
      Cr.det • dd (dd Cr) =
        (2 : RatFunc K) • ((dd Cr * Cr.adjugate) * dd Cr) := by
    rw [hd2, hd1]
    ext i j
    change Cr.det * f (C'' i j) =
      (2 : RatFunc K) * (((C'.map f * Cr.adjugate) * C'.map f) i j)
    rw [hdetMap]
    have hp := congrArg f (hsrcIJ i j)
    have hpe := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) (RatFunc K) => M i j) hprod
    change
      f (((C' * C.adjugate) * C') i j) =
        ((C'.map f * Cr.adjugate) * C'.map f) i j at hpe
    calc
      f C.det * f (C'' i j) = f (C.det * C'' i j) := (map_mul f _ _).symm
      _ = f (2 * (((C' * C.adjugate) * C') i j)) := by
        rw [hsrcIJ]
      _ = (2 : RatFunc K) *
            (((C'.map f * Cr.adjugate) * C'.map f) i j) := by
        rw [map_mul, map_ofNat, hpe]
  have hnonzero : Cr.det ≠ 0 := by
    change (quadraticTransverseCapSource_rationalThreeMatrix F).det ≠ 0
    exact quadraticTransverseCapSource_rationalThreeMatrix_det_ne_zero
      F hregular
  have hunit : IsUnit Cr.det := isUnit_iff_ne_zero.mpr hnonzero
  have hAdj : Cr.adjugate = Cr.det • Cr⁻¹ := by
    calc
      Cr.adjugate = (Cr⁻¹ * Cr) * Cr.adjugate := by
        rw [Matrix.nonsing_inv_mul Cr hunit, one_mul]
      _ = Cr⁻¹ * (Cr * Cr.adjugate) := by rw [mul_assoc]
      _ = Cr.det • Cr⁻¹ := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul]
        simp
  have hinverse :
      dd (dd Cr) =
        (2 : RatFunc K) • ((dd Cr * Cr⁻¹) * dd Cr) := by
    have hscaled :
        ((dd Cr * Cr.adjugate) * dd Cr) =
          Cr.det • ((dd Cr * Cr⁻¹) * dd Cr) := by
      rw [hAdj, Matrix.mul_smul, Matrix.smul_mul]
    calc
      dd (dd Cr) = Cr.det⁻¹ • (Cr.det • dd (dd Cr)) := by
        rw [smul_smul, inv_mul_cancel₀ hnonzero, one_smul]
      _ = Cr.det⁻¹ •
          ((2 : RatFunc K) • ((dd Cr * Cr.adjugate) * dd Cr)) := by
            rw [hmain]
      _ = (2 : RatFunc K) • ((dd Cr * Cr⁻¹) * dd Cr) := by
        rw [hscaled]
        simp only [smul_smul]
        rw [show Cr.det⁻¹ * ((2 : RatFunc K) * Cr.det) = 2 by
          field_simp]
  have hRiccati :
      dd (dd Cr) = 2 * ((dd Cr * Cr⁻¹) * dd Cr) := by
    simpa only [two_mul, two_smul] using hinverse
  exact quadraticTransverseCapSource_rationalRiccati_constantDet
    F hregular D hX hRiccati

end

end HC4.Valuation
