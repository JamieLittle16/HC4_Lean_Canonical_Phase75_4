import HC4.Valuation.QuadraticTransverseCapSourcePolynomialPathHessian
import Mathlib.Tactic

/-!
# Exact polynomial transverse-gradient fibres for the ORIGINAL source

For the regular branch of a determinant-one transverse-quadratic
four-variable source F, the polynomial matrix inverse P(X)
constructs a genuine polynomial path

  y_p(X) = P(X) (p - b(X))

for any fixed prescribed transverse-gradient output p in K^3.
The actual source transverse-gradient polynomials are literally
constant along this path:

  ∂_{y_i} F(X,y_p(X)) = p_i

in K[X], not just pointwise at selected x values.

The polynomial chain rule can now differentiate this equality to
obtain the moving-fibre Hessian equation. No substitute source,
assumed affine Hessian, or rational endpoint is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- Substitution of ANY polynomial transverse path into the actual
transverse gradient is b(X)+C(X)y(X), as an identity in K[X]. -/
theorem quadraticTransverseCapSource_polynomialPath_transverseGradient
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (y : Fin 3 → Polynomial K) (i : Fin 3) :
    sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
        (MvPolynomial.pderiv i.succ F) =
      (quadraticTransverseCapSourceLinearCoefficients F i) +
        ((quadraticTransverseCapSourceAxisThreeBlock F).matrix *ᵥ y) i := by
  classical
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let C := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let q := Fin.cons Polynomial.X y
  apply Polynomial.funext
  intro t
  have hpoint :
      (fun a : Fin 4 => Polynomial.eval t (q a)) =
        Fin.cons t (fun j : Fin 3 => Polynomial.eval t (y j)) := by
    funext a
    cases a using Fin.cases with
    | zero => simp [q]
    | succ k => rfl
  calc
    Polynomial.eval t
        (sourcePolynomialPathSubstitution q
          (MvPolynomial.pderiv i.succ F)) =
        MvPolynomial.eval
          (Fin.cons t (fun j : Fin 3 => Polynomial.eval t (y j)))
            (MvPolynomial.pderiv i.succ F) := by
      rw [sourcePolynomialPathSubstitution_eval, hpoint]
    _ = Polynomial.eval t (b i + (C *ᵥ y) i) := by
      rw [quadraticTransverseCapSource_transverseGradient_affine
        F hcap t (fun j : Fin 3 => Polynomial.eval t (y j)) i]
      simp [b, C, Matrix.mulVec, dotProduct, Polynomial.eval_add,
        Polynomial.eval_finset_sum, Polynomial.eval_mul]

/-- Polynomial path on which the actual source transverse gradient
attains a chosen fixed output p. -/
noncomputable def quadraticTransverseCapSource_regularPolynomialFibre
    (F : MvPolynomial (Fin 4) K)
    (P : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (p : Fin 3 → K) : Fin 3 → Polynomial K :=
  P *ᵥ (fun i => Polynomial.C (p i) -
    quadraticTransverseCapSourceLinearCoefficients F i)

/-- No additional fibre hypothesis: under the original source cap and
the verified regular source inverse, the actual transverse
derivatives are constant as polynomials along y_p(X). -/
theorem quadraticTransverseCapSource_regularPolynomialFibre_gradient
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (p : Fin 3 → K) :
    ∃ y : Fin 3 → Polynomial K,
      ∀ i : Fin 3,
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (MvPolynomial.pderiv i.succ F) = Polynomial.C (p i) := by
  classical
  obtain ⟨P, hCP, _hPC, _hd⟩ :=
    quadraticTransverseCapSource_regularPolynomialInverse
      F hcap hdet hregular
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let C := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let cp : Fin 3 → Polynomial K := fun i => Polynomial.C (p i)
  let y := quadraticTransverseCapSource_regularPolynomialFibre F P p
  have hconst : b + C *ᵥ y = cp := by
    change b + C *ᵥ (P *ᵥ (cp - b)) = cp
    rw [Matrix.mulVec_mulVec, hCP, Matrix.one_mulVec]
    abel
  refine ⟨y, ?_⟩
  intro i
  have hgrad :=
    quadraticTransverseCapSource_polynomialPath_transverseGradient
      F hcap y i
  calc
    sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
        (MvPolynomial.pderiv i.succ F) =
        b i + (C *ᵥ y) i := hgrad
    _ = (b + C *ᵥ y) i := rfl
    _ = Polynomial.C (p i) := by
      rw [hconst]
      rfl

end

end HC4.Valuation
