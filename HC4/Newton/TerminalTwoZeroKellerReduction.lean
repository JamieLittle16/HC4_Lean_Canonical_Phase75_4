import HC4.Newton.TerminalTwoZeroPlanarisation
import HC4.Newton.TerminalTwoZeroHessianSquare
import HC4.MongeAmpere.PolynomialInitial
import HC4.PlanarJC2Interface
import Mathlib.Tactic

/-!
# Planar Keller reduction of the two-zero terminal endpoint

This module completes the algebraic reduction of the `k = 2` terminal
boundary to an honest planar Keller map.

Suppose the standard two-zero terminal potential satisfies the global
polynomial Monge--Ampère equation

    det Hess(F) = 1.

Phase 93.29 proves

    det Hess(F) = Δ^2,

where

    Δ = A₀ C₁ - A₁ C₀.

The ambient coefficient polynomials `A,C` descend to honest planar
polynomials `A₂,C₂`.  Their planar Jacobian determinant renames exactly to
`Δ`.

Injectivity of the variable-renaming map then gives

    Jac(A₂,C₂)^2 = 1.

Over a field, the polynomial ring is a domain, hence

    Jac(A₂,C₂) = 1  or  Jac(A₂,C₂) = -1.

Therefore `(A₂,C₂)` is a planar Keller map in the exact sense required by
`PlanarJC2Injectivity`.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Renaming the planar Jacobian determinant of `(A,C)` gives the ambient
cross determinant of their renamed coefficient polynomials. -/
theorem rename_planarJacobianDet_standardPair
    (A C : MvPolynomial (Fin 2) K) :
    MvPolynomial.rename standardZeroPairEmbedding
        (HC4.planarJacobianDetPolynomial
          (standardPlanarPairMap A C)) =
      MvPolynomial.pderiv 0
          (MvPolynomial.rename
            standardZeroPairEmbedding A) *
        MvPolynomial.pderiv 1
          (MvPolynomial.rename
            standardZeroPairEmbedding C) -
      MvPolynomial.pderiv 1
          (MvPolynomial.rename
            standardZeroPairEmbedding A) *
        MvPolynomial.pderiv 0
          (MvPolynomial.rename
            standardZeroPairEmbedding C) := by
  unfold HC4.planarJacobianDetPolynomial
  simp only [standardPlanarPairMap_zero,
    standardPlanarPairMap_one, map_sub, map_mul]
  rw [← MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective
      (0 : Fin 2) A]
  rw [← MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective
      (1 : Fin 2) C]
  rw [← MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective
      (1 : Fin 2) A]
  rw [← MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective
      (0 : Fin 2) C]
  simp

/-- Exact Keller-model certificate produced from a two-zero terminal
potential. -/
def HasStandardTwoZeroPlanarKellerModel
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∃ A C : MvPolynomial (Fin 2) K,
    MvPolynomial.rename standardZeroPairEmbedding A =
        standardTwoZeroA F ∧
    MvPolynomial.rename standardZeroPairEmbedding C =
        standardTwoZeroC F ∧
    HC4.HasNonzeroConstantPlanarJacobian
      (standardPlanarPairMap A C)

/-- The global Monge--Ampère identity turns the planarised coefficient pair
into a genuine planar Keller map. -/
theorem standardTwoZero_mongeAmpere_hasPlanarKellerModel
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    HasStandardTwoZeroPlanarKellerModel F := by
  have hform :
      HasStandardTwoZeroDoublingForm F :=
    standardTwoZero_hasDoublingForm hd hhom
  rcases
      standardTwoZeroDoublingForm_hasPlanarPair
        hform with
    ⟨A, C, hA, hC⟩
  let G : HC4.PlanarPolynomialMap K :=
    standardPlanarPairMap A C
  have hrename :
      MvPolynomial.rename standardZeroPairEmbedding
          (HC4.planarJacobianDetPolynomial G) =
        standardTwoZeroCrossDet F := by
    dsimp [G]
    rw [rename_planarJacobianDet_standardPair]
    rw [hA, hC]
    rfl
  have hsquareAmbient :
      (standardTwoZeroCrossDet F)^2 = 1 := by
    have hdet :=
      standardTwoZero_hessianDeterminant_eq_crossDet_sq
        hd hhom
    change HC4.Polynomial.hessianDeterminant F = 1 at hMA
    rw [hdet] at hMA
    exact hMA
  have hsquareRename :
      MvPolynomial.rename standardZeroPairEmbedding
          ((HC4.planarJacobianDetPolynomial G)^2) =
        MvPolynomial.rename standardZeroPairEmbedding
          (1 : MvPolynomial (Fin 2) K) := by
    simp only [map_pow, map_one]
    rw [hrename]
    exact hsquareAmbient
  have hsquare :
      (HC4.planarJacobianDetPolynomial G)^2 =
        (1 : MvPolynomial (Fin 2) K) := by
    exact
      (MvPolynomial.rename_injective
        standardZeroPairEmbedding
        standardZeroPairEmbedding.injective)
        hsquareRename
  let J :
      MvPolynomial (Fin 2) K :=
    HC4.planarJacobianDetPolynomial G
  have hfactor :
      (J - 1) * (J + 1) = 0 := by
    calc
      (J - 1) * (J + 1) = J^2 - 1 := by ring
      _ = 0 := by
        dsimp [J]
        rw [hsquare]
        ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have hJ : J = 1 :=
      sub_eq_zero.mp hminus
    refine ⟨A, C, hA, hC, ?_⟩
    refine ⟨(1 : K), one_ne_zero, ?_⟩
    simpa [J, G] using hJ
  · have hJ : J = -1 :=
      eq_neg_of_add_eq_zero_left hplus
    refine ⟨A, C, hA, hC, ?_⟩
    refine ⟨(-1 : K), neg_ne_zero.mpr one_ne_zero, ?_⟩
    simpa [J, G] using hJ

/-- Direct terminal version: once two standard zero weights are present,
the conformal terminal face plus the global Monge--Ampère equation produces
the planar Keller model. -/
theorem nonnegativeTerminalFace_two_standard_zeros_hasPlanarKellerModel
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    HasStandardTwoZeroPlanarKellerModel F := by
  have hd :
      0 < d :=
    nonnegativeTerminalFace_two_standard_zeros_degree_pos
      hface hnonneg h0 h1
  have hlambda :
      lambda =
        standardTwoZeroTerminalWeight d :=
    nonnegativeTerminalFace_two_standard_zeros_weight_eq
      hface hnonneg h0 h1
  have hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F := by
    rw [← hlambda]
    exact hface.2.2.2.1
  exact
    standardTwoZero_mongeAmpere_hasPlanarKellerModel
      hd hhom hMA

/-- Under the explicit `JC2` injectivity hypothesis, the terminal two-zero
branch therefore supplies an injective planar base map. -/
theorem nonnegativeTerminalFace_two_standard_zeros_exists_injective_planarMap
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    ∃ A C : MvPolynomial (Fin 2) K,
      MvPolynomial.rename standardZeroPairEmbedding A =
          standardTwoZeroA F ∧
      MvPolynomial.rename standardZeroPairEmbedding C =
          standardTwoZeroC F ∧
      Function.Injective
        (HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C)) := by
  rcases
      nonnegativeTerminalFace_two_standard_zeros_hasPlanarKellerModel
        hface hnonneg h0 h1 hMA with
    ⟨A, C, hA, hC, hKeller⟩
  exact
    ⟨A, C, hA, hC,
      HC4.planar_injective_of_JC2
        hJC2
        (standardPlanarPairMap A C)
        hKeller⟩

end

end HC4.Newton
