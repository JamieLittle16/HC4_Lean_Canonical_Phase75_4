import HC4.Valuation.QuadraticTransverseCapSourceLongitudinalChain
import Mathlib.Tactic

/-!
# Constant nonzero longitudinal slope on the genuine gradient fibres

The determinant-one Hessian on a polynomial fibre is the original
source Hessian transported by polynomial substitution. Its transverse
block is C(X). The verified longitudinal chain identity is therefore
exactly 1/d, where det C = C(d) and d is nonzero.

This proves the missing regular-branch affine longitudinal drift
without assuming a source normal form or an inverse-gradient endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- The genuine Hessian Schur equation after substitution along an
arbitrary polynomial transverse path. -/
theorem quadraticTransverseCapSource_polynomialPath_schur_unit
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (y : Fin 3 → Polynomial K) :
    let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
    let E := sourcePolynomialPathSubstitution q
    let T := quadraticTransverseCapSourceAxisThreeBlock F
    let v : Fin 3 → Polynomial K :=
      fun i => E (HC4.Polynomial.hessian F 0 i.succ)
    quadraticAxisFourBlockCore (E (HC4.Polynomial.hessian F 0 0))
      (v 0) (v 1) (v 2) T.a T.b T.c T.d T.e T.f = 1 := by
  classical
  dsimp only
  let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
  let E := sourcePolynomialPathSubstitution q
  let T := quadraticTransverseCapSourceAxisThreeBlock F
  let H := (quadraticTransverseCapSourceGlobalFourBlock F).map E.toRingHom
  have hunit : H.determinantCore = 1 := by
    change ((quadraticTransverseCapSourceGlobalFourBlock F).map
      E.toRingHom).determinantCore = 1
    rw [GeneralFourBlock.determinantCore_map,
      quadraticTransverseCapSourceGlobalFourBlock_unit F hdet, map_one]
  rw [← quadraticAxisFourBlockCore_eq_generalFourBlock] at hunit
  have ha : H.d = T.a :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 0 0
  have hb : H.r = T.b :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 0 1
  have hc : H.s = T.c :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 0 2
  have hd : H.x = T.d :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 1 1
  have he : H.y = T.e :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 1 2
  have hf : H.z = T.f :=
    quadraticTransverseCapSource_polynomialPath_transverseHessian F hcap y 2 2
  rw [ha, hb, hc, hd, he, hf] at hunit
  exact hunit

/-- Polynomial Schur complement cancellation for the actual source.
The polynomial inverse is supplied separately by the verified regular
source theorem; no additional property of that inverse is required. -/
theorem quadraticTransverseCapSource_polynomialPath_schur_inverse
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (y : Fin 3 → Polynomial K)
    (P : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hPC : P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1) :
    let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
    let E := sourcePolynomialPathSubstitution q
    let T := quadraticTransverseCapSourceAxisThreeBlock F
    let v : Fin 3 → Polynomial K :=
      fun i => E (HC4.Polynomial.hessian F 0 i.succ)
    T.determinantCore *
      (E (HC4.Polynomial.hessian F 0 0) -
        ∑ i : Fin 3, v i * (P *ᵥ v) i) = 1 := by
  classical
  dsimp only
  let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
  let E := sourcePolynomialPathSubstitution q
  let T := quadraticTransverseCapSourceAxisThreeBlock F
  let C : Matrix (Fin 3) (Fin 3) (Polynomial K) := T.matrix
  let u := E (HC4.Polynomial.hessian F 0 0)
  let v : Fin 3 → Polynomial K :=
    fun i => E (HC4.Polynomial.hessian F 0 i.succ)
  have hcore : quadraticAxisFourBlockCore u (v 0) (v 1) (v 2)
      T.a T.b T.c T.d T.e T.f = 1 :=
    quadraticTransverseCapSource_polynomialPath_schur_unit F hcap hdet y
  have hAdj : C.adjugate = T.determinantCore • P := by
    calc
      C.adjugate = (P * C) * C.adjugate := by rw [hPC, one_mul]
      _ = P * (C * C.adjugate) := by rw [mul_assoc]
      _ = P * (C.det • (1 : Matrix (Fin 3) (Fin 3) (Polynomial K))) := by
        rw [Matrix.mul_adjugate]
      _ = C.det • P := by rw [Matrix.mul_smul, mul_one]
      _ = T.determinantCore • P := by rw [GeneralThreeBlock.matrix_det]
  have hcontract :
      (∑ i : Fin 3, v i * (C.adjugate *ᵥ v) i) =
        v 0 * quadraticTransverseAdjugateVector0 T (v 0) (v 1) (v 2) +
        v 1 * quadraticTransverseAdjugateVector1 T (v 0) (v 1) (v 2) +
        v 2 * quadraticTransverseAdjugateVector2 T (v 0) (v 1) (v 2) := by
    simp [C, Matrix.mulVec, dotProduct, Matrix.adjugate_fin_three,
      Fin.sum_univ_three, GeneralThreeBlock.matrix,
      quadraticTransverseAdjugateVector0, quadraticTransverseAdjugateVector1,
      quadraticTransverseAdjugateVector2] <;> ring
  have hscale :
      (∑ i : Fin 3, v i * (C.adjugate *ᵥ v) i) =
        T.determinantCore * (∑ i : Fin 3, v i * (P *ᵥ v) i) := by
    rw [hAdj, Matrix.smul_mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change v i * (T.determinantCore * (P *ᵥ v) i) =
      T.determinantCore * (v i * (P *ᵥ v) i)
    ring
  rw [quadraticAxisFourBlockCore_eq_transverseAdjugateSchur] at hcore
  rw [← hcontract, hscale] at hcore
  change T.determinantCore *
    (u - ∑ i : Fin 3, v i * (P *ᵥ v) i) = 1
  calc
    T.determinantCore * (u - ∑ i : Fin 3, v i * (P *ᵥ v) i) =
      u * T.determinantCore -
        T.determinantCore * (∑ i : Fin 3, v i * (P *ᵥ v) i) := by ring
    _ = 1 := hcore

/-- Every transverse gradient output has a genuine polynomial
fibre with longitudinal gradient affine of the SAME nonzero slope.
The constant d is independent of the fibre. -/
theorem quadraticTransverseCapSource_regularAffineFibre
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    ∃ d : K, d ≠ 0 ∧
      ∀ p : Fin 3 → K, ∃ (y : Fin 3 → Polynomial K) (k : K),
        (∀ i : Fin 3,
          sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
            (MvPolynomial.pderiv i.succ F) = Polynomial.C (p i)) ∧
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (MvPolynomial.pderiv (0 : Fin 4) F) =
            Polynomial.C d⁻¹ * Polynomial.X + Polynomial.C k := by
  classical
  obtain ⟨_, _, _, d, hdn, hD⟩ :=
    quadraticTransverseCapSource_regularPolynomialInverse F hcap hdet hregular
  refine ⟨d, hdn, ?_⟩
  intro p
  obtain ⟨P, y, hCP, hPC, hgrad, hchain⟩ :=
    quadraticTransverseCapSource_regularLongitudinalChain F hcap hdet hregular p
  let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
  let g := sourcePolynomialPathSubstitution q (MvPolynomial.pderiv (0 : Fin 4) F)
  let v : Fin 3 → Polynomial K :=
    fun i => sourcePolynomialPathSubstitution q (HC4.Polynomial.hessian F 0 i.succ)
  let T := quadraticTransverseCapSourceAxisThreeBlock F
  change Polynomial.derivative g =
    sourcePolynomialPathSubstitution q (HC4.Polynomial.hessian F 0 0) -
      ∑ i : Fin 3, v i * (P *ᵥ v) i at hchain
  have hs : T.determinantCore *
    (sourcePolynomialPathSubstitution q (HC4.Polynomial.hessian F 0 0) -
      ∑ i : Fin 3, v i * (P *ᵥ v) i) = 1 :=
    quadraticTransverseCapSource_polynomialPath_schur_inverse F hcap hdet y P hPC
  rw [← hchain, hD] at hs
  have hm : Polynomial.C d * Polynomial.C d⁻¹ = (1 : Polynomial K) := by
    rw [← map_mul, mul_inv_cancel₀ hdn, map_one]
  have hg : Polynomial.derivative g = Polynomial.C d⁻¹ := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hdn)
    exact hs.trans hm.symm
  let z := g - Polynomial.C d⁻¹ * Polynomial.X
  have hz : Polynomial.derivative z = 0 := by
    simp [z, hg, Polynomial.derivative_mul]
  have hk : z = Polynomial.C (z.coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hz
  refine ⟨y, z.coeff 0, hgrad, ?_⟩
  change g = Polynomial.C d⁻¹ * Polynomial.X + Polynomial.C (z.coeff 0)
  rw [← hk]
  dsimp [z]
  ring

end

end HC4.Valuation
