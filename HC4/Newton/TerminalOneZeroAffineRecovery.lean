import HC4.Newton.TerminalOneZeroHessianFactor
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic

/-!
# Affine recovery of the zero-weight coordinate

Phase 93.34 gives, on the standard one-zero terminal face,

    S * (-S * Δ₂₃) = 1

where

    S = pderiv 0 (pderiv 1 F).

Thus `S` is a unit in the multivariate polynomial ring.  Over a field the
coefficient ring is reduced, and Mathlib's
`MvPolynomial.isUnit_iff_eq_C_of_isReduced` says that every unit
multivariate polynomial is a constant unit.  Hence

    S = C s,   s ≠ 0.

Now put

    A = pderiv 1 F.

Phase 93.34 already proves that `A` depends only on `X₀`, equivalently its
partials in directions `1,2,3` vanish.  Subtracting `C s * X 0` also kills
the remaining `0`-partial.  In characteristic zero, the project-local
derivative-support rigidity theorem then forces the remainder to be a
constant.

Therefore

    pderiv 1 F = C b + C s * X 0,   s ≠ 0.

So equality of the gradient's coordinate `1` immediately recovers the
zero-weight source coordinate `0`.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/- As in the one-zero Hessian factorisation module, the two-zero branch
installs simp lemmas rewriting `pderiv 2` and `pderiv 3` to the auxiliary
names `standardTwoZeroA/C`.  Those rewrites must be disabled here so that
the generic derivation lemma `map_sub` can see the outer partial
derivatives of the affine remainder literally. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- The Phase 93.34 explicit inverse relation makes the one-zero slope a
unit in the ambient multivariate polynomial ring. -/
theorem standardOneZero_slope_isUnit
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    IsUnit (standardOneZeroSlope F) := by
  rw [isUnit_iff_exists_inv]
  refine
    ⟨-(standardOneZeroSlope F) *
        standardOneZeroTransverseDet F, ?_⟩
  exact
    standardOneZero_slope_mul_explicitInverse
      ha had hhom hMA

/-- Over a field, the one-zero slope is a nonzero scalar polynomial. -/
theorem standardOneZero_slope_eq_C_nonzero
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    ∃ s : K,
      s ≠ 0 ∧
      standardOneZeroSlope F = MvPolynomial.C s := by
  have hunit :
      IsUnit (standardOneZeroSlope F) :=
    standardOneZero_slope_isUnit
      ha had hhom hMA
  rcases
      (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit) with
    ⟨s, hsunit, hslope⟩
  exact ⟨s, hsunit.ne_zero, hslope⟩

/-- A four-variable polynomial whose four partial derivatives vanish is
constant in characteristic zero. -/
theorem finFour_eq_C_of_all_pderiv_eq_zero
    [CharZero K]
    (P : MvPolynomial (Fin 4) K)
    (h0 : MvPolynomial.pderiv 0 P = 0)
    (h1 : MvPolynomial.pderiv 1 P = 0)
    (h2 : MvPolynomial.pderiv 2 P = 0)
    (h3 : MvPolynomial.pderiv 3 P = 0) :
    P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · have hmcoeff :
        MvPolynomial.coeff m P = 0 := by
      by_contra hcoeff
      have hm0 :
          m 0 = 0 :=
        exponent_eq_zero_of_pderiv_eq_zero
          0 P h0 m hcoeff
      have hm1 :
          m 1 = 0 :=
        exponent_eq_zero_of_pderiv_eq_zero
          1 P h1 m hcoeff
      have hm2 :
          m 2 = 0 :=
        exponent_eq_zero_of_pderiv_eq_zero
          2 P h2 m hcoeff
      have hm3 :
          m 3 = 0 :=
        exponent_eq_zero_of_pderiv_eq_zero
          3 P h3 m hcoeff
      apply hm
      apply Finsupp.ext
      intro i
      fin_cases i <;>
        simp [hm0, hm1, hm2, hm3]
    rw [hmcoeff]
    have h0m :
        (0 : Fin 4 →₀ ℕ) ≠ m := by
      intro h
      exact hm h.symm
    simp [h0m]

/-- **Affine zero/degree pair.**
On a standard one-zero Monge--Ampère terminal face, the degree-coordinate
gradient component is affine in the unique zero-weight variable with
nonzero slope. -/
theorem standardOneZero_pderiv_one_affine
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    ∃ b s : K,
      s ≠ 0 ∧
      MvPolynomial.pderiv 1 F =
        MvPolynomial.C b +
          MvPolynomial.C s * MvPolynomial.X 0 := by
  rcases
      standardOneZero_slope_eq_C_nonzero
        ha had hhom hMA with
    ⟨s, hs, hslope⟩
  let A : MvPolynomial (Fin 4) K :=
    MvPolynomial.pderiv 1 F
  let R : MvPolynomial (Fin 4) K :=
    A - MvPolynomial.C s * MvPolynomial.X 0
  have hz :=
    standardOneZero_pderiv_one_crossHessian_zero
      ha had hhom
  have hR0 :
      MvPolynomial.pderiv 0 R = 0 := by
    dsimp [R, A]
    rw [map_sub]
    change
      standardOneZeroSlope F -
          MvPolynomial.pderiv 0
            (MvPolynomial.C s * MvPolynomial.X 0) =
        0
    rw [hslope]
    simp
  have hR1 :
      MvPolynomial.pderiv 1 R = 0 := by
    dsimp [R, A]
    rw [map_sub]
    rw [hz.1]
    simp
  have hR2 :
      MvPolynomial.pderiv 2 R = 0 := by
    dsimp [R, A]
    rw [map_sub]
    rw [hz.2.1]
    simp
  have hR3 :
      MvPolynomial.pderiv 3 R = 0 := by
    dsimp [R, A]
    rw [map_sub]
    rw [hz.2.2]
    simp
  have hRconst :
      R = MvPolynomial.C (MvPolynomial.coeff 0 R) :=
    finFour_eq_C_of_all_pderiv_eq_zero
      R hR0 hR1 hR2 hR3
  let b : K := MvPolynomial.coeff 0 R
  refine ⟨b, s, hs, ?_⟩
  dsimp [A] at *
  calc
    MvPolynomial.pderiv 1 F =
        R + MvPolynomial.C s * MvPolynomial.X 0 := by
          dsimp [R]
          ring
    _ =
        MvPolynomial.C b +
          MvPolynomial.C s * MvPolynomial.X 0 := by
          rw [hRconst]

/-- Equality of the degree-coordinate gradient component recovers the
unique zero-weight coordinate. -/
theorem standardOneZero_gradient_component_one_recovers_zero
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (hgrad1 :
      mvGradientMap F p 1 =
        mvGradientMap F q 1) :
    p 0 = q 0 := by
  rcases
      standardOneZero_pderiv_one_affine
        ha had hhom hMA with
    ⟨b, s, hs, hA⟩
  change
    MvPolynomial.eval p
        (MvPolynomial.pderiv 1 F) =
      MvPolynomial.eval q
        (MvPolynomial.pderiv 1 F) at hgrad1
  rw [hA] at hgrad1
  simp only [map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X] at hgrad1
  have hmul :
      s * p 0 = s * q 0 :=
    add_left_cancel hgrad1
  exact
    (mul_left_cancel₀ hs) hmul

/-- Equal full gradients in the standard one-zero branch therefore agree
in the unique zero-weight source coordinate. -/
theorem standardOneZero_gradient_eq_recovers_zero
    [CharZero K]
    {d a : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (ha : 0 < a)
    (had : a < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    {p q : Fin 4 -> K}
    (hgrad :
      mvGradientMap F p =
        mvGradientMap F q) :
    p 0 = q 0 := by
  exact
    standardOneZero_gradient_component_one_recovers_zero
      ha had hhom hMA
      (congrFun hgrad 1)

end

end HC4.Newton
