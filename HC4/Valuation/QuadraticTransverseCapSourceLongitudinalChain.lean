import HC4.Valuation.QuadraticTransverseCapSourcePolynomialFibreDrift
import Mathlib.Tactic

/-!
# Longitudinal derivative of the actual gradient along fixed-output fibres

For a determinant-one quadratic-transverse source with nonzero
polynomial transverse Hessian determinant, the verified polynomial
inverse C(X)⁻¹ and exact source polynomial chain rule give

  d/dX F_x(X, y_p(X))
    = H_00(X,y_p(X)) - v(X)^T C(X)⁻¹ v(X)

where v(X) is the ORIGINAL source mixed Hessian row evaluated on
the original source polynomial curve y_p(X).

This is the precise Schur-complement derivative identity. The
next and final regular-branch step evaluates the actual determinant-one
Schur equation along this curve, showing the RHS is 1/d for
d = det C ∈ Kˣ.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- The original source longitudinal derivative along the
polynomial fibre is the exact Schur complement of its
transverse Hessian, with the polynomial inverse supplied
by the already-proved regular source theorem.

No Riccati equation, matrix inverse, moving-fibre equation,
source normal form, or derivative rule is assumed. -/
theorem quadraticTransverseCapSource_regularLongitudinalChain
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (p : Fin 3 → K) :
    ∃ (P : Matrix (Fin 3) (Fin 3) (Polynomial K))
      (y : Fin 3 → Polynomial K),
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix * P = 1 ∧
      P * (quadraticTransverseCapSourceAxisThreeBlock F).matrix = 1 ∧
      (∀ i : Fin 3,
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (MvPolynomial.pderiv i.succ F) = Polynomial.C (p i)) ∧
      (let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
       let v : Fin 3 → Polynomial K :=
         fun i => sourcePolynomialPathSubstitution q
           (HC4.Polynomial.hessian F 0 i.succ)
       Polynomial.derivative
           (sourcePolynomialPathSubstitution q
             (MvPolynomial.pderiv (0 : Fin 4) F)) =
         sourcePolynomialPathSubstitution q
           (HC4.Polynomial.hessian F 0 0) -
           ∑ i : Fin 3, v i * (P *ᵥ v) i) := by
  classical
  obtain ⟨P, hCP, hPC, _⟩ :=
    quadraticTransverseCapSource_regularPolynomialInverse
      F hcap hdet hregular
  obtain ⟨y, hgrad, hdrift⟩ :=
    quadraticTransverseCapSource_regularPolynomialFibre_drift
      F hcap hdet hregular p
  let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
  let C := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let v : Fin 3 → Polynomial K :=
    fun i => sourcePolynomialPathSubstitution q
      (HC4.Polynomial.hessian F 0 i.succ)
  let dy : Fin 3 → Polynomial K :=
    fun i => Polynomial.derivative (y i)
  have hCv : C *ᵥ dy = -v := by
    funext i
    have hi := hdrift i
    change v i + (C *ᵥ dy) i = 0 at hi
    change (C *ᵥ dy) i = -(v i)
    linear_combination hi
  have hdy : dy = -(P *ᵥ v) := by
    calc
      dy = (P * C) *ᵥ dy := by rw [hPC, Matrix.one_mulVec]
      _ = P *ᵥ (C *ᵥ dy) := by rw [Matrix.mulVec_mulVec]
      _ = P *ᵥ (-v) := by rw [hCv]
      _ = -(P *ᵥ v) := by simp
  have hsum :
      (∑ i : Fin 3, dy i * v i) =
        -(∑ i : Fin 3, v i * (P *ᵥ v) i) := by
    have hdy' (i : Fin 3) : dy i = -(P *ᵥ v) i :=
      congrFun hdy i
    calc
      (∑ i : Fin 3, dy i * v i) =
          ∑ i : Fin 3, - (v i * (P *ᵥ v) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdy' i]
        ring
      _ = -(∑ i : Fin 3, v i * (P *ᵥ v) i) := by
        rw [Finset.sum_neg_distrib]
  have hchain :
      Polynomial.derivative
          (sourcePolynomialPathSubstitution q
            (MvPolynomial.pderiv (0 : Fin 4) F)) =
        sourcePolynomialPathSubstitution q
          (HC4.Polynomial.hessian F 0 0) +
        (∑ i : Fin 3, dy i * v i) := by
    exact sourcePolynomialLongitudinalSection_derivative
      (MvPolynomial.pderiv (0 : Fin 4) F) y
  refine ⟨P, y, hCP, hPC, hgrad, ?_⟩
  dsimp only
  rw [hsum] at hchain
  simpa only [sub_eq_add_neg] using hchain

end

end HC4.Valuation
