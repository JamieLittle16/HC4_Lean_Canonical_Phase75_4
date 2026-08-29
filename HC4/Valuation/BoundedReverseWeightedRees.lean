import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.AdaptiveSmithWallExposure
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# Bounded reverse weighted Rees families

For a polynomial supported in natural weights at most `D`, this file forms
the honest polynomial family whose coefficient at source exponent `d` is
multiplied by `X^(D-weight(d))`. Its special fibre is the maximal weighted
face. The construction is an explicit finite support sum.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Every source monomial has natural weight at most the chosen reverse-Rees
level. -/
def HasReverseWeightBound
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support, Finsupp.weight w d ≤ D

/-- The bounded reverse weighted Rees family
`sum_d c_d X^(D-weight(d)) x^d`. -/
noncomputable def reverseWeightedReesFamily
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (_h : HasReverseWeightBound w D F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  F.sum fun d c =>
    MvPolynomial.monomial d
      (Polynomial.X ^ (D - Finsupp.weight w d) * Polynomial.C c)

/-- Literal source coefficient of the reverse weighted Rees family. -/
theorem reverseWeightedReesFamily_coeff
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (reverseWeightedReesFamily w D F h) =
      if d ∈ F.support then
        Polynomial.X ^ (D - Finsupp.weight w d) *
          Polynomial.C (MvPolynomial.coeff d F)
      else 0 := by
  classical
  unfold reverseWeightedReesFamily
  rw [MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  by_cases hd : d ∈ F.support
  · rw [Finset.sum_eq_single d]
    · simp [hd]
    · intro b hb hbd
      rw [MvPolynomial.coeff_monomial]
      split
      · next heq => exact (hbd heq).elim
      · rfl
    · exact fun hdnot => (hdnot hd).elim
  · simp [hd]

/-- Exact coefficient formula for every parameter layer. -/
theorem reverseWeightedReesFamily_parameterLayer_coeff
    (w : Fin 4 → ℕ) (D n : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (familyParameterLayer (reverseWeightedReesFamily w D F h) n) =
      if d ∈ F.support ∧ D - Finsupp.weight w d = n then
        MvPolynomial.coeff d F
      else 0 := by
  rw [familyParameterLayer_coeff, reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ F.support
  · simp only [hd, if_true, Polynomial.coeff_mul_C,
      Polynomial.coeff_X_pow]
    by_cases heq : D - Finsupp.weight w d = n
    · simp [heq]
    · simp [heq, Ne.symm heq]
  · simp [hd]

/-- The zero parameter layer is the maximal natural-weight face, coefficient
by coefficient. -/
theorem reverseWeightedReesFamily_parameterLayer_zero_coeff
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (familyParameterLayer (reverseWeightedReesFamily w D F h) 0) =
      if d ∈ F.support ∧ Finsupp.weight w d = D then
        MvPolynomial.coeff d F
      else 0 := by
  rw [reverseWeightedReesFamily_parameterLayer_coeff]
  by_cases hd : d ∈ F.support
  · have hle := h d hd
    simp only [hd, true_and]
    by_cases heq : Finsupp.weight w d = D
    · simp [heq]
    · have hne : D - Finsupp.weight w d ≠ 0 := by omega
      simp [heq, hne]
  · simp [hd]

/-- The special fibre of the reverse Rees family is exactly its zero
parameter layer. -/
theorem polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) :
    polynomialFamilySpecialFiber (reverseWeightedReesFamily w D F h) =
      familyParameterLayer (reverseWeightedReesFamily w D F h) 0 := by
  ext d
  rw [coeff_polynomialFamilySpecialFiber, familyParameterLayer_coeff]
  rfl

/-- The special fibre is the maximal weighted initial form. -/
theorem polynomialFamilySpecialFiber_reverseWeightedReesFamily
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) :
    polynomialFamilySpecialFiber (reverseWeightedReesFamily w D F h) =
      initialForm (fun i => (w i : ℤ)) (D : ℤ) F := by
  ext d
  rw [coeff_polynomialFamilySpecialFiber,
    reverseWeightedReesFamily_coeff, HC4.Polynomial.coeff_initialForm]
  by_cases hd : d ∈ F.support
  · have hle := h d hd
    simp only [hd, if_true, map_mul, map_pow]
    have hcast :
        Finsupp.weight (fun i => (w i : ℤ)) d =
          (Finsupp.weight w d : ℤ) := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply]
      push_cast
      rfl
    rw [hcast]
    by_cases heq : Finsupp.weight w d = D
    · subst D
      simp
    · have hpos : 0 < D - Finsupp.weight w d := by omega
      have hne : D - Finsupp.weight w d ≠ 0 := Nat.ne_of_gt hpos
      simp [hne, heq]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hcoeff]

/-! ## Whole-family normalization -/

/-- Inflating the source variables by the original positive weight clears
every reverse exponent to the single common parameter power `D`. -/
theorem adaptiveSmithInflate_reverseWeightedReesFamily_eq
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F) :
    adaptiveSmithInflateHom w (reverseWeightedReesFamily w D F h) =
      MvPolynomial.C (Polynomial.X ^ D) * constantPolynomialFamily F := by
  apply MvPolynomial.funext
  intro a
  rw [eval_adaptiveSmithInflateHom]
  unfold reverseWeightedReesFamily
  rw [MvPolynomial.sum_def]
  rw [MvPolynomial.eval_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  unfold constantPolynomialFamily
  rw [MvPolynomial.eval_map]
  rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hinfl :
      d.prod (fun n e => adaptiveSmithInflateSection w a n ^ e) =
        ∏ i : Fin 4, adaptiveSmithInflateSection w a i ^ d i :=
    Finsupp.prod_fintype d
      (fun n e => adaptiveSmithInflateSection w a n ^ e) (by simp)
  rw [hinfl]
  rw [fin4_adaptiveSmithInflateSection_monomialProduct]
  have hle := h d hd
  calc
    (Polynomial.X ^ (D - Finsupp.weight w d) *
          Polynomial.C (MvPolynomial.coeff d F)) *
        (Polynomial.X ^ Finsupp.weight w d *
          ∏ i : Fin 4, a i ^ d i) =
      Polynomial.X ^ D *
        (Polynomial.C (MvPolynomial.coeff d F) *
          ∏ i : Fin 4, a i ^ d i) := by
      have hpow :
          Polynomial.X ^ (D - Finsupp.weight w d) *
              Polynomial.X ^ Finsupp.weight w d =
            (Polynomial.X : Polynomial K) ^ D := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = (Polynomial.X ^ (D - Finsupp.weight w d) *
              Polynomial.X ^ Finsupp.weight w d) *
              (Polynomial.C (MvPolynomial.coeff d F) *
                ∏ i : Fin 4, a i ^ d i) := by ring
        _ = _ := by rw [hpow]
    _ = Polynomial.X ^ D *
        (Polynomial.C (MvPolynomial.coeff d F) *
          ∏ x ∈ d.support, a x ^ d x) := by
      change Polynomial.X ^ D *
          (Polynomial.C (MvPolynomial.coeff d F) *
            ∏ i : Fin 4, a i ^ d i) =
        Polynomial.X ^ D *
          (Polynomial.C (MvPolynomial.coeff d F) *
            d.prod fun n e => a n ^ e)
      exact congrArg
        (fun z => Polynomial.X ^ D *
          (Polynomial.C (MvPolynomial.coeff d F) * z))
        (Finsupp.prod_fintype d
          (fun n e => a n ^ e) (by simp)).symm

/-! ## Injectivity of the positive diagonal inflation -/

/-- The adaptive diagonal inflation sends one source monomial to the same
source exponent, multiplying only its coefficient by the corresponding
nonzero parameter monomial. -/
theorem adaptiveSmithInflateHom_monomial
    (w : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) (c : Polynomial K) :
    adaptiveSmithInflateHom w (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d
        (Polynomial.X ^ Finsupp.weight w d * c) := by
  classical
  unfold adaptiveSmithInflateHom
  rw [MvPolynomial.eval₂Hom_monomial]
  unfold adaptiveSmithInflateVariable
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hparameter :
      d.prod (fun i e => (Polynomial.X ^ w i) ^ e) =
        (Polynomial.X : Polynomial K) ^ Finsupp.weight w d := by
    rw [Finsupp.prod_fintype d
      (fun i e => (Polynomial.X ^ w i) ^ e) (by simp)]
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [Fin.prod_univ_four, Fin.sum_univ_four]
    simp only [← pow_mul]
    repeat' rw [← pow_add]
    congr 1
    simp [nsmul_eq_mul, Nat.mul_comm, Nat.add_assoc]
  have hcoefficient :
      d.prod (fun i e =>
        (MvPolynomial.C (Polynomial.X ^ w i) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ e) =
        MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^ Finsupp.weight w d) := by
    calc
      d.prod (fun i e =>
          (MvPolynomial.C (Polynomial.X ^ w i) :
            MvPolynomial (Fin 4) (Polynomial K)) ^ e) =
        d.prod (fun i e =>
          MvPolynomial.C ((Polynomial.X ^ w i) ^ e)) := by
            congr 1
            funext i e
            exact (map_pow MvPolynomial.C (Polynomial.X ^ w i) e).symm
      _ = MvPolynomial.C
          (d.prod (fun i e => (Polynomial.X ^ w i) ^ e)) := by
            exact (map_finsuppProd MvPolynomial.C d
              (fun i e => (Polynomial.X ^ w i) ^ e)).symm
      _ = _ := by rw [hparameter]
  rw [hcoefficient]
  rw [MvPolynomial.monomial_eq]
  simp only [← map_mul]
  ring

/-- Coefficients under adaptive diagonal inflation are multiplied by the
nonzero monomial dictated by their source weight. -/
theorem coeff_adaptiveSmithInflateHom
    (w : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d (adaptiveSmithInflateHom w P) =
        Polynomial.X ^ Finsupp.weight w d * MvPolynomial.coeff d P := by
  apply MvPolynomial.induction_on' P
  · intro u a d
    rw [adaptiveSmithInflateHom_monomial]
    rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hdu : d = u
    · subst d
      simp
    · simp [hdu]
  · intro p q hp hq d
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add,
      hp d, hq d]
    ring

/-- The adaptive positive diagonal source inflation is injective over the
polynomial parameter ring. -/
theorem adaptiveSmithInflateHom_injective
    (w : Fin 4 → ℕ) :
    Function.Injective (adaptiveSmithInflateHom (K := K) w) := by
  intro P Q hPQ
  apply MvPolynomial.ext
  intro d
  have hd := congrArg (MvPolynomial.coeff d) hPQ
  rw [coeff_adaptiveSmithInflateHom w P d,
    coeff_adaptiveSmithInflateHom w Q d] at hd
  exact mul_left_cancel₀
    (pow_ne_zero (Finsupp.weight w d) Polynomial.X_ne_zero) hd

/-! ## Exact reverse-Rees Hessian clock -/

/-- A bounded reverse weighted Rees family of a determinant-one source has
an exact pure Hessian determinant clock. -/
theorem reverseWeightedReesFamily_hasHessianDefect
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hnonneg : 2 * ∑ i : Fin 4, w i ≤ 4 * D) :
    HasPolynomialFamilyHessianDefect (K := K)
      (reverseWeightedReesFamily w D F h)
      (4 * D - 2 * ∑ i : Fin 4, w i) := by
  let Q := reverseWeightedReesFamily w D F h
  let S := ∑ i : Fin 4, w i
  let N := 4 * D - 2 * S
  have hnorm := adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h
  have hdetEq := congrArg HC4.Polynomial.hessianDeterminant hnorm
  rw [hessianDeterminant_adaptiveSmithInflateHom] at hdetEq
  rw [hessianDeterminant_C_mul] at hdetEq
  have hconst :
      HC4.Polynomial.hessianDeterminant (constantPolynomialFamily F) =
        constantPolynomialFamily (HC4.Polynomial.hessianDeterminant F) := by
    let phi :
        MvPolynomial (Fin 4) K →+*
          MvPolynomial (Fin 4) (Polynomial K) :=
      MvPolynomial.map Polynomial.C
    unfold HC4.Polynomial.hessianDeterminant
    rw [show
        HC4.Polynomial.hessian (constantPolynomialFamily F) =
          (HC4.Polynomial.hessian F).map phi by
      ext i j
      simp [constantPolynomialFamily, phi,
        HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]]
    exact (phi.map_det (HC4.Polynomial.hessian F)).symm
  rw [hconst, hdet] at hdetEq
  simp [constantPolynomialFamily] at hdetEq
  have hsum : 2 * S + N = 4 * D := by
    dsimp [S, N]
    omega
  have heq :
      (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ (2 * S) *
          adaptiveSmithInflateHom w
            (HC4.Polynomial.hessianDeterminant Q) =
        (MvPolynomial.C Polynomial.X) ^ (4 * D) := by
    dsimp [Q, S] at hdetEq ⊢
    simpa only [map_pow, ← pow_mul, Nat.mul_comm] using hdetEq
  rw [← hsum, pow_add] at heq
  have hcancel :
      adaptiveSmithInflateHom w (HC4.Polynomial.hessianDeterminant Q) =
        (MvPolynomial.C Polynomial.X) ^ N :=
    mul_left_cancel₀
      (pow_ne_zero (2 * S)
        (MvPolynomial.C_ne_zero.mpr Polynomial.X_ne_zero)) heq
  have htarget :
      adaptiveSmithInflateHom w
          (MvPolynomial.C (Polynomial.X ^ N)) =
        MvPolynomial.C (Polynomial.X ^ N) := by
    simp [adaptiveSmithInflateHom]
  have hinflated :
      adaptiveSmithInflateHom w (HC4.Polynomial.hessianDeterminant Q) =
        adaptiveSmithInflateHom w
          (MvPolynomial.C (Polynomial.X ^ N)) := by
    rw [htarget]
    simpa only [map_pow] using hcancel
  have hQ :
      HC4.Polynomial.hessianDeterminant Q =
        MvPolynomial.C (Polynomial.X ^ N) :=
    adaptiveSmithInflateHom_injective w hinflated
  unfold HasPolynomialFamilyHessianDefect
  simpa [Q, N, S] using hQ

end

end HC4.Valuation
