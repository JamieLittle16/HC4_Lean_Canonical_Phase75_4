import HC4.Newton.MixedDegreeAxisCollision
import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Polynomial.DeterminantFirstJet
import HC4.Valuation.QuadraticTransverseGap
import HC4.Valuation.TransverseAxisKernelDrift

/-!
# A singular transverse axis requires a nonzero cubic correction

For a determinant-one four-variable source with an exact marked collision,
a singular transverse Hessian block on the marked axis forces the *cubic*
transverse grade to contribute to the determinant, not just some term of
grade three or four. All data are taken on the original source.
-/

namespace HC4.Valuation.TransverseAxis

open HC4.Newton HC4.Polynomial MvPolynomial
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

private abbrev P (K : Type*) [Field K] := MvPolynomial (Fin 4) K
private abbrev R (K : Type*) [Field K] := Polynomial K

private def restrict : P K →+* R K :=
  (Polynomial.mapRingHom (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))).comp
    (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom

private lemma restrict_pderiv_zero (p : P K) :
    restrict (pderiv 0 p) = Polynomial.derivative (restrict p) :=
  longitudinalAxisRestriction_pderiv_zero p

/-- The entire Hessian of the original source evaluated on the marked axis. -/
def axisHessian (F : P K) : Matrix (Fin 4) (Fin 4) (R K) :=
  restrict.mapMatrix (hessian F)

/-- The transverse submatrix of the original source Hessian along the axis. -/
def transverseAxisHessian (F : P K) : Matrix (Fin 3) (Fin 3) (R K) :=
  (axisHessian F).submatrix Fin.succ Fin.succ

private def axisGradient (F : P K) (i : Fin 3) : R K :=
  restrict (pderiv i.succ F)

private def cubicJet (F : P K) (j : Fin 3) : Matrix (Fin 3) (Fin 3) (R K) :=
  fun i k => restrict (pderiv j.succ (hessian F i.succ k.succ))

/-- The cofactor contraction of the third transverse derivative on the
marked axis. This is the cubic correction to the linear determinant jet. -/
def cubicCorrection (F : P K) (j : Fin 3) : R K :=
  ((axisHessian F).adjugate * axisBlock 0 0 (cubicJet F j)).trace

/-- Transverse entries of the longitudinal column of the axis adjugate. -/
def axisKernelColumn (F : P K) : Fin 3 → R K :=
  fun i => (axisHessian F).adjugate i.succ 0

private lemma axisHessian_eq_block (F : P K) :
    axisHessian F = axisBlock (axisHessian F 0 0)
      (fun i => Polynomial.derivative (axisGradient F i)) (transverseAxisHessian F) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      rw [axisBlock_zero_succ]
      change restrict (pderiv j.succ (pderiv 0 F)) =
        Polynomial.derivative (restrict (pderiv j.succ F))
      rw [pderiv_comm_backport j.succ 0, restrict_pderiv_zero]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [axisBlock_succ_zero]
      exact restrict_pderiv_zero _
    | succ j => rfl

private lemma transverseAxisHessian_symm (F : P K) :
    (transverseAxisHessian F)ᵀ = transverseAxisHessian F := by
  apply Matrix.ext
  intro i j
  change restrict (pderiv i.succ (pderiv j.succ F)) =
    restrict (pderiv j.succ (pderiv i.succ F))
  rw [pderiv_comm_backport i.succ j.succ]

private lemma axisHessian_det (F : P K) (hdet : hessianDeterminant F = 1) :
    (axisHessian F).det = 1 := by
  change (restrict.mapMatrix (hessian F)).det = 1
  rw [← restrict.map_det, ← hessianDeterminant, hdet, map_one]

private lemma axisMixedJet (F : P K) (i j : Fin 3) :
    restrict (pderiv j.succ (hessian F 0 i.succ)) =
      Polynomial.derivative (transverseAxisHessian F j i) := by
  change restrict (pderiv j.succ (pderiv i.succ (pderiv 0 F))) =
    Polynomial.derivative (restrict (pderiv i.succ (pderiv j.succ F)))
  rw [pderiv_comm_backport i.succ 0, pderiv_comm_backport j.succ 0,
    pderiv_comm_backport j.succ i.succ, restrict_pderiv_zero]

private lemma axisJet_eq_block (F : P K) (j : Fin 3) :
    (hessian F).map (fun p => restrict (pderiv j.succ p)) =
      axisBlock (restrict (pderiv j.succ (hessian F 0 0)))
        (fun i => Polynomial.derivative (transverseAxisHessian F j i)) (cubicJet F j) := by
  apply Matrix.ext
  intro a i
  cases a using Fin.cases with
  | zero =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      rw [axisBlock_zero_succ]
      exact axisMixedJet F i j
  | succ a =>
    cases i using Fin.cases with
    | zero =>
      rw [axisBlock_succ_zero]
      change restrict (pderiv j.succ (pderiv 0 (pderiv a.succ F))) = _
      rw [pderiv_comm_backport 0 a.succ]
      exact axisMixedJet F a j
    | succ i => rfl

private lemma trace_axisJet_eq_zero (F : P K) (hdet : hessianDeterminant F = 1)
    (j : Fin 3) :
    ((axisHessian F).adjugate *
      (hessian F).map (fun p => restrict (pderiv j.succ p))).trace = 0 := by
  have h := restricted_derivation_det_eq_trace restrict (pderiv j.succ)
    (hessian F) (axisHessian_det F hdet)
  change restrict (pderiv j.succ (hessianDeterminant F)) =
    ((axisHessian F).adjugate *
      (hessian F).map (fun p => restrict (pderiv j.succ p))).trace at h
  rw [hdet, pderiv_one, map_zero] at h
  exact h.symm

/-- On a singular transverse axis, the cubic determinant correction is
exactly minus twice the longitudinal drift paired with the axis kernel
column. This uses the determinant equation of the original source. -/
theorem cubicCorrection_eq_neg_two_kernelDrift
    (F : P K) (hdet : hessianDeterminant F = 1)
    (hsing : (transverseAxisHessian F).det = 0) (j : Fin 3) :
    cubicCorrection F j =
      -(2 * (((transverseAxisHessian F).map Polynomial.derivative) *ᵥ
        axisKernelColumn F) j) := by
  have h := trace_axisJet_eq_zero F hdet j
  have hblock := axisHessian_eq_block F
  rw [axisJet_eq_block, hblock,
    trace_axisBlock_singular _ _ _ _ _ _ hsing (transverseAxisHessian_symm F)] at h
  unfold cubicCorrection axisKernelColumn
  rw [hblock]
  change _ = -(2 * ((fun i => Polynomial.derivative (transverseAxisHessian F j i)) ⬝ᵥ
    kernelColumn _ _ _))
  linear_combination h

/-- A singular transverse axis cannot be repaired by the quartic and
higher grades alone. In particular a cubic correction must be visible
in the first determinant jet. -/
theorem exists_cubicCorrection_ne_zero_of_singular
    [CharZero K] (F : P K) (hdet : hessianDeterminant F = 1)
    (hcoll : HasExactGradientCollision F
      (Fin.cons 0 (fun _ : Fin 3 => 0)) (Fin.cons 1 (fun _ : Fin 3 => 0)))
    (hsing : (transverseAxisHessian F).det = 0) :
    ∃ j, cubicCorrection F j ≠ 0 := by
  let a := axisHessian F 0 0
  let b := axisGradient F
  let C := transverseAxisHessian F
  let a₁ := fun j : Fin 3 => restrict (pderiv j.succ (hessian F 0 0))
  let B := cubicJet F
  have hA := axisHessian_det F hdet
  have hblock : axisHessian F = axisBlock a (fun i => Polynomial.derivative (b i)) C :=
    axisHessian_eq_block F
  rw [hblock] at hA
  have hmarked (i : Fin 3) : (b i).eval 0 = (b i).eval 1 := by
    have h := hcoll i.succ
    unfold mvGradientComponentAt at h
    rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
      eval_finCons_zero_eq_longitudinalAxisRestriction] at h
    exact h
  have hjets (j : Fin 3) :
      ((axisBlock a (fun i => Polynomial.derivative (b i)) C).adjugate *
        axisBlock (a₁ j) (fun i => Polynomial.derivative (C j i)) (B j)).trace = 0 := by
    have h := trace_axisJet_eq_zero F hdet j
    rw [hblock, axisJet_eq_block] at h
    exact h
  obtain ⟨j, hj⟩ := exists_nonzero_cubic_trace_of_singular_axis a b C a₁ B
    hA hsing (transverseAxisHessian_symm F) hmarked hjets
  refine ⟨j, ?_⟩
  simpa only [cubicCorrection, hblock] using hj

/-- The nonzero cubic correction vanishes when tested against the axis
kernel itself. This is stronger than the existence of a cubic term. -/
theorem cubicCorrection_selfPairing_eq_zero_of_singular
    (F : P K) (hdet : hessianDeterminant F = 1)
    (hsing : (transverseAxisHessian F).det = 0) :
    axisKernelColumn F ⬝ᵥ cubicCorrection F = 0 := by
  let C := transverseAxisHessian F
  let n := axisKernelColumn F
  have hA := axisHessian_det F hdet
  have hblock := axisHessian_eq_block F
  rw [hblock] at hA
  have hn : C *ᵥ n = 0 := by
    change transverseAxisHessian F *ᵥ axisKernelColumn F = 0
    unfold axisKernelColumn
    rw [hblock]
    exact (kernelColumn_spec _ _ C hA hsing).1
  have h := kernel_drift_selfPairing_eq_zero C n (transverseAxisHessian_symm F) hn
  have hcor : cubicCorrection F = (-(2 : R K)) • ((C.map Polynomial.derivative) *ᵥ n) := by
    funext j
    rw [cubicCorrection_eq_neg_two_kernelDrift F hdet hsing j]
    simp [Pi.smul_apply, smul_eq_mul, C, n]
  rw [hcor, dotProduct_smul]
  change (-(2 : R K)) • (n ⬝ᵥ (C.map Polynomial.derivative) *ᵥ n) = 0
  simp [h]

local notation "w" => TransverseGap.markedAxisWeight

private lemma restrict_initialForm_zero (p : P K) :
    restrict (initialForm w 0 p) = restrict p := by
  change longitudinalAxisRestriction (initialForm w 0 p) = longitudinalAxisRestriction p
  rw [longitudinalAxisRestriction_eq_coefficient_zero,
    longitudinalAxisRestriction_eq_coefficient_zero]
  apply Polynomial.ext
  intro a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff, coeff_initialForm]
  have hweight : Finsupp.weight w ((0 : Fin 3 →₀ ℕ).cons a) = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [TransverseGap.markedAxisWeight, Fin.sum_univ_four]
    · simp
  simp [hweight]

private lemma cubicJet_initialForm (F : P K) (j : Fin 3) :
    cubicJet (initialForm w 3 F) j = cubicJet F j := by
  apply Matrix.ext
  intro i k
  change restrict (pderiv j.succ (pderiv k.succ (pderiv i.succ (initialForm w 3 F)))) =
    restrict (pderiv j.succ (pderiv k.succ (pderiv i.succ F)))
  rw [pderiv_initialForm, pderiv_initialForm, pderiv_initialForm]
  have hs (v : Fin 3) : w v.succ = 1 := by simp [TransverseGap.markedAxisWeight]
  simp only [hs]
  norm_num
  exact restrict_initialForm_zero _

/-- The cubic transverse grade of a marked-colliding determinant-one
source with singular transverse axis is necessarily nonzero. The
quartic grade cannot substitute for it in this branch. -/
theorem cubicGrade_ne_zero_of_singular_axis
    [CharZero K] (F : P K) (hdet : hessianDeterminant F = 1)
    (hcoll : HasExactGradientCollision F
      (Fin.cons 0 (fun _ : Fin 3 => 0)) (Fin.cons 1 (fun _ : Fin 3 => 0)))
    (hsing : (transverseAxisHessian F).det = 0) :
    initialForm w 3 F ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_cubicCorrection_ne_zero_of_singular F hdet hcoll hsing
  intro hzero
  apply hj
  have h := cubicJet_initialForm F j
  rw [hzero] at h
  have hz : cubicJet (0 : P K) j = 0 := by
    apply Matrix.ext
    intro i k
    simp [cubicJet, hessian_apply]
  simp [cubicCorrection, ← h, hz]

end

end HC4.Valuation.TransverseAxis
