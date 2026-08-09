import HC4.Newton.TerminalOneZeroEndpoint
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
# Coordinate-permutation transport for terminal endpoints

The one-zero and two-zero terminal endpoints were deliberately proved first
in standard coordinates.  This module supplies the invariant coordinate
transport needed to use those endpoints at arbitrary placements.

For a permutation `rho : Equiv.Perm (Fin 4)` put

    F^rho = rename rho F.

Then:

* the Hessian of `F^rho` is the Hessian of `F`, with coefficients renamed
  by `rho` and rows/columns simultaneously reindexed;
* therefore the Hessian determinant is simply `rename rho` of the original
  Hessian determinant;
* hence the polynomial Monge--Ampere equation is invariant;
* the gradient maps are conjugate by the same permutation on source
  coordinates and the inverse permutation on output coordinates;
* consequently gradient injectivity is invariant under coordinate
  permutation.

This is the structural adapter needed before transporting the standard
`k=1` and `k=2` endpoint theorems to arbitrary terminal zero placements.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Relabel an ambient point by the same coordinate permutation used to
rename polynomial variables.  If `rename rho` sends old variable `i` to
new variable `rho i`, then this sends an old point to its new-coordinate
description. -/
def terminalPermutePoint
    (rho : Equiv.Perm (Fin 4))
    (p : Fin 4 -> K) :
    Fin 4 -> K :=
  fun j => p (rho.symm j)

@[simp] theorem terminalPermutePoint_apply
    (rho : Equiv.Perm (Fin 4))
    (p : Fin 4 -> K)
    (j : Fin 4) :
    terminalPermutePoint rho p j =
      p (rho.symm j) := rfl

/-- Point relabelling by a permutation is injective. -/
theorem terminalPermutePoint_injective
    (rho : Equiv.Perm (Fin 4)) :
    Function.Injective
      (terminalPermutePoint (K := K) rho) := by
  intro p q hpq
  funext i
  have h :=
    congrFun hpq (rho i)
  simpa [terminalPermutePoint] using h

/-- Relabelling by `rho.symm` reverses relabelling by `rho`. -/
@[simp] theorem terminalPermutePoint_symm_apply
    (rho : Equiv.Perm (Fin 4))
    (p : Fin 4 -> K) :
    terminalPermutePoint rho.symm
        (terminalPermutePoint rho p) =
      p := by
  funext i
  simp [terminalPermutePoint]

/-- Hessian covariance under a coordinate permutation.

Both matrix indices are reindexed by `rho.symm`, while every polynomial
entry is carried through the coefficient algebra hom `rename rho`. -/
theorem hessian_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (MvPolynomial.rename rho F) =
      (((MvPolynomial.rename rho).toRingHom.mapMatrix
          (HC4.Polynomial.hessian F)).submatrix
        rho.symm rho.symm) := by
  apply Matrix.ext
  intro i j
  have hi :
      MvPolynomial.pderiv i
          (MvPolynomial.rename rho F) =
        MvPolynomial.rename rho
          (MvPolynomial.pderiv (rho.symm i) F) := by
    simpa using
      (MvPolynomial.pderiv_rename
        rho.injective (rho.symm i) F)
  have hj :
      MvPolynomial.pderiv j
          (MvPolynomial.rename rho
            (MvPolynomial.pderiv (rho.symm i) F)) =
        MvPolynomial.rename rho
          (MvPolynomial.pderiv (rho.symm j)
            (MvPolynomial.pderiv (rho.symm i) F)) := by
    simpa using
      (MvPolynomial.pderiv_rename
        rho.injective
        (rho.symm j)
        (MvPolynomial.pderiv (rho.symm i) F))
  calc
    HC4.Polynomial.hessian
        (MvPolynomial.rename rho F) i j =
      MvPolynomial.pderiv j
        (MvPolynomial.pderiv i
          (MvPolynomial.rename rho F)) := rfl
    _ =
      MvPolynomial.pderiv j
        (MvPolynomial.rename rho
          (MvPolynomial.pderiv (rho.symm i) F)) := by
            rw [hi]
    _ =
      MvPolynomial.rename rho
        (MvPolynomial.pderiv (rho.symm j)
          (MvPolynomial.pderiv (rho.symm i) F)) := hj
    _ =
      (((MvPolynomial.rename rho).toRingHom.mapMatrix
          (HC4.Polynomial.hessian F)).submatrix
        rho.symm rho.symm) i j := by
          simp [HC4.Polynomial.hessian_apply]

/-- The formal Hessian determinant commutes with a coordinate permutation. -/
theorem hessianDeterminant_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant
        (MvPolynomial.rename rho F) =
      MvPolynomial.rename rho
        (HC4.Polynomial.hessianDeterminant F) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_rename_perm]
  rw [Matrix.det_submatrix_equiv_self]
  symm
  exact
    (MvPolynomial.rename rho).toRingHom.map_det
      (HC4.Polynomial.hessian F)

/-- The polynomial Monge--Ampere equation is invariant under coordinate
permutation. -/
theorem isPolynomialMongeAmpere_rename_perm
    (rho : Equiv.Perm (Fin 4))
    {F : MvPolynomial (Fin 4) K}
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere
      (MvPolynomial.rename rho F) := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere at hMA ⊢
  rw [hessianDeterminant_rename_perm]
  rw [hMA]
  simp

/-- Exact pointwise gradient conjugacy under coordinate permutation. -/
theorem mvGradientMap_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (p : Fin 4 -> K)
    (j : Fin 4) :
    mvGradientMap
        (MvPolynomial.rename rho F)
        (terminalPermutePoint rho p) j =
      mvGradientMap F p (rho.symm j) := by
  have hderiv :
      MvPolynomial.pderiv j
          (MvPolynomial.rename rho F) =
        MvPolynomial.rename rho
          (MvPolynomial.pderiv (rho.symm j) F) := by
    simpa using
      (MvPolynomial.pderiv_rename
        rho.injective (rho.symm j) F)
  change
    MvPolynomial.eval
        (terminalPermutePoint rho p)
        (MvPolynomial.pderiv j
          (MvPolynomial.rename rho F)) =
      MvPolynomial.eval p
        (MvPolynomial.pderiv (rho.symm j) F)
  rw [hderiv]
  rw [MvPolynomial.eval_rename]
  congr 2
  funext i
  simp [terminalPermutePoint]

/-- If the renamed gradient is injective, so is the original gradient. -/
theorem mvGradientMap_injective_of_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hinj :
      Function.Injective
        (mvGradientMap
          (MvPolynomial.rename rho F))) :
    Function.Injective (mvGradientMap F) := by
  intro p q hpq
  apply terminalPermutePoint_injective rho
  apply hinj
  funext j
  rw [mvGradientMap_rename_perm]
  rw [mvGradientMap_rename_perm]
  exact congrFun hpq (rho.symm j)

/-- Conversely, coordinate permutation cannot destroy gradient
injectivity. -/
theorem mvGradientMap_rename_perm_injective_of_original
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hinj :
      Function.Injective (mvGradientMap F)) :
    Function.Injective
      (mvGradientMap
        (MvPolynomial.rename rho F)) := by
  intro p q hpq
  have hp :
      p =
        terminalPermutePoint rho
          (terminalPermutePoint rho.symm p) := by
    symm
    simpa using
      (terminalPermutePoint_symm_apply
        (K := K) rho.symm p)
  have hq :
      q =
        terminalPermutePoint rho
          (terminalPermutePoint rho.symm q) := by
    symm
    simpa using
      (terminalPermutePoint_symm_apply
        (K := K) rho.symm q)
  rw [hp, hq] at hpq ⊢
  have hold :
      mvGradientMap F
          (terminalPermutePoint rho.symm p) =
        mvGradientMap F
          (terminalPermutePoint rho.symm q) := by
    funext i
    have h :=
      congrFun hpq (rho i)
    simpa [mvGradientMap_rename_perm] using h
  exact congrArg (terminalPermutePoint rho) (hinj hold)

/-- Gradient injectivity is exactly invariant under coordinate
permutation. -/
theorem mvGradientMap_rename_perm_injective_iff
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    Function.Injective
        (mvGradientMap
          (MvPolynomial.rename rho F)) ↔
      Function.Injective (mvGradientMap F) := by
  constructor
  · exact mvGradientMap_injective_of_rename_perm rho F
  · exact mvGradientMap_rename_perm_injective_of_original rho F

end

end HC4.Newton
