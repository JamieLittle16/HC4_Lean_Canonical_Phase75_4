import HC4.Newton.TerminalOneZeroSupport
import HC4.Newton.OneZeroBlockDeterminant
import HC4.Polynomial.HessianDeterminant
import HC4.MongeAmpere.PolynomialInitial
import Mathlib.Tactic

/-!
# Hessian factorisation on the standard one-zero terminal face

For the standard one-zero weight

    (0,d,a,d-a),   0 < a < d,

the previous support theorem gives

    ∂₁₁F = ∂₂₁F = ∂₃₁F = 0.

Write

    S = ∂₀∂₁F

and let

    Δ₂₃ = F₂₂ F₃₃ - F₂₃ F₃₂.

Then the full polynomial Hessian determinant factors exactly as

    det Hess(F) = - S^2 * Δ₂₃.

If `F` satisfies the polynomial Monge--Ampère equation
`det Hess(F)=1`, this becomes

    - S^2 * Δ₂₃ = 1.

In particular neither `S` nor `Δ₂₃` can vanish.  More strongly, the
displayed identity already gives an explicit polynomial inverse relation
for `S`; a later endpoint module will convert that unit relation into
affineness in the zero-weight coordinate.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/- The two-zero branch installs simp lemmas rewriting `pderiv 2 F` and
`pderiv 3 F` to its auxiliary names `standardTwoZeroA/C`.  Those rewrites
are inappropriate in the one-zero Hessian calculation, where we need to
commute mixed partials before applying the sparse `pderiv _ (pderiv 1 F)`
identities. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- Slope in the zero/degree coordinate pair. -/
def standardOneZeroSlope
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 0
    (MvPolynomial.pderiv 1 F)

/-- Hessian determinant of the two interior positive coordinates. -/
def standardOneZeroTransverseDet
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 2 F) *
    MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 3 F) -
  MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 2 F) *
    MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 3 F)

/-- Explicit Hessian model for the standard one-zero face. -/
def standardOneZeroHessianModel
    (F : MvPolynomial (Fin 4) K) :
    Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) K) :=
  oneZeroHessianBlockMatrix
    (MvPolynomial.pderiv 0
      (MvPolynomial.pderiv 0 F))
    (standardOneZeroSlope F)
    (MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 0 F))
    (MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 0 F))
    (standardOneZeroSlope F)
    (MvPolynomial.pderiv 0
      (MvPolynomial.pderiv 2 F))
    (MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 2 F))
    (MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 2 F))
    (MvPolynomial.pderiv 0
      (MvPolynomial.pderiv 3 F))
    (MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 3 F))
    (MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 3 F))

/-- The actual polynomial Hessian equals the sparse one-zero model. -/
theorem standardOneZero_hessian_eq_model
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    HC4.Polynomial.hessian F =
      standardOneZeroHessianModel F := by
  have hz :=
    standardOneZero_pderiv_one_crossHessian_zero
      ha had hhom
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [HC4.Polynomial.hessian_apply,
      standardOneZeroHessianModel,
      oneZeroHessianBlockMatrix,
      standardOneZeroSlope,
      hz.1, hz.2.1, hz.2.2] <;>
    try rw [pderiv_comm_backport] <;>
    simp [hz.1, hz.2.1, hz.2.2]

/-- Exact one-zero Hessian determinant factorisation. -/
theorem standardOneZero_hessianDeterminant_factor
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F) :
    HC4.Polynomial.hessianDeterminant F =
      -(standardOneZeroSlope F)^2 *
        standardOneZeroTransverseDet F := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [standardOneZero_hessian_eq_model ha had hhom]
  simpa [standardOneZeroHessianModel,
    standardOneZeroSlope,
    standardOneZeroTransverseDet,
    pow_two] using
    (det_oneZeroHessianBlockMatrix
      (MvPolynomial.pderiv 0
        (MvPolynomial.pderiv 0 F))
      (standardOneZeroSlope F)
      (MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 0 F))
      (MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 0 F))
      (standardOneZeroSlope F)
      (MvPolynomial.pderiv 0
        (MvPolynomial.pderiv 2 F))
      (MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 2 F))
      (MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 2 F))
      (MvPolynomial.pderiv 0
        (MvPolynomial.pderiv 3 F))
      (MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 3 F))
      (MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 3 F)))

/-- Monge--Ampère turns the one-zero determinant factorisation into an
explicit inverse relation. -/
theorem standardOneZero_mongeAmpere_factor_eq_one
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    -(standardOneZeroSlope F)^2 *
        standardOneZeroTransverseDet F =
      1 := by
  have hfactor :=
    standardOneZero_hessianDeterminant_factor
      ha had hhom
  change HC4.Polynomial.hessianDeterminant F = 1 at hMA
  rw [hfactor] at hMA
  exact hMA

/-- The zero/degree slope cannot vanish on a Monge--Ampère one-zero face. -/
theorem standardOneZero_slope_ne_zero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    standardOneZeroSlope F ≠ 0 := by
  intro hs
  have hfactor :=
    standardOneZero_mongeAmpere_factor_eq_one
      ha had hhom hMA
  rw [hs] at hfactor
  simp at hfactor

/-- The interior `2,3` Hessian determinant cannot vanish either. -/
theorem standardOneZero_transverseDet_ne_zero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    standardOneZeroTransverseDet F ≠ 0 := by
  intro hT
  have hfactor :=
    standardOneZero_mongeAmpere_factor_eq_one
      ha had hhom hMA
  rw [hT] at hfactor
  simp at hfactor

/-- Explicit right inverse for the zero/degree slope in the polynomial
ring.  This avoids relying on any unit API at this stage. -/
theorem standardOneZero_slope_mul_explicitInverse
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    standardOneZeroSlope F *
        (-(standardOneZeroSlope F) *
          standardOneZeroTransverseDet F) =
      1 := by
  have hfactor :=
    standardOneZero_mongeAmpere_factor_eq_one
      ha had hhom hMA
  calc
    standardOneZeroSlope F *
        (-(standardOneZeroSlope F) *
          standardOneZeroTransverseDet F) =
      -(standardOneZeroSlope F)^2 *
        standardOneZeroTransverseDet F := by
          ring
    _ = 1 := hfactor

end

end HC4.Newton
