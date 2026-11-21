import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactEndpointReduction
import HC4.Newton.TerminalTwoZeroPlanarCollision
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# A19.38: honest first contact produces a planar Keller collision

A19.4 showed that planar JC2 contradicts every honest first-contact terminal.
A19.37 sharpened the standard two-zero endpoint: a distinct four-dimensional
terminal gradient collision already produces a concrete distinct collision of
a planar Keller map, without assuming JC2.

This file composes those two pieces without losing coordinate provenance.  The
first-contact cocharacter has a marked zero weight at coordinate `0`; unique
zero elimination gives a second zero.  According to whether that second zero
is `1`, `2`, or `3`, a coordinate permutation puts the terminal weight into the
standard `(0,0,d,d)` form.  We transport the actual Monge--Ampere fibre and its
exact distinct collision through the same permutation and invoke A19.37.

Thus every genuine first-contact endpoint canonically yields an actual planar
Keller counterexample witness.  No JC2 assumption occurs in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- If a coordinate permutation puts the terminal source weight into standard
two-zero form, then the transported terminal collision gives a concrete
planar Keller collision. -/
theorem hasPlanarKellerCollision_of_standardized
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (rho : Equiv.Perm (Fin 4))
    (hweight :
      (fun j : Fin 4 => (C.weight (rho.symm j) : ℤ)) =
        standardTwoZeroTerminalWeight (C.degree : ℤ)) :
    HC4.HasPlanarKellerCollision K := by
  have hhomRenamed :=
    integralWeightedHomogeneous_rename_perm C.homogeneous rho
  change
    IsIntegralWeightedHomogeneous
      (fun j : Fin 4 => (C.weight (rho.symm j) : ℤ))
      (C.degree : ℤ)
      (MvPolynomial.rename rho T.fibre) at hhomRenamed
  rw [hweight] at hhomRenamed

  have hMARenamed :=
    isPolynomialMongeAmpere_rename_perm rho T.mongeAmpere

  let p : Fin 4 → K := terminalPermutePoint rho T.leftPoint
  let q : Fin 4 → K := terminalPermutePoint rho T.rightPoint

  have hpq : p ≠ q := by
    intro hpq'
    apply T.distinct
    exact terminalPermutePoint_injective rho hpq'

  have hgrad : mvGradientMap T.fibre T.leftPoint =
      mvGradientMap T.fibre T.rightPoint :=
    mvGradientMap_eq_of_exactCollision
      T.fibre T.leftPoint T.rightPoint T.exactCollision

  have hgradRenamed :
      mvGradientMap (MvPolynomial.rename rho T.fibre) p =
        mvGradientMap (MvPolynomial.rename rho T.fibre) q := by
    funext j
    dsimp [p, q]
    rw [mvGradientMap_rename_perm, mvGradientMap_rename_perm]
    exact congrFun hgrad (rho.symm j)

  have hcollRenamed :
      HasExactGradientCollision
        (MvPolynomial.rename rho T.fibre) p q := by
    intro j
    exact congrFun hgradRenamed j

  exact
    standardTwoZero_terminal_hasPlanarKellerCollision
      C.degree_pos hhomRenamed hMARenamed p q hpq hcollRenamed

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

namespace AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint

/-- **A19.38 unconditional endpoint extraction.**

Every honest first-contact endpoint produces an actual planar Keller map with
a distinct collision.  The only case split is the location of the second
terminal zero weight. -/
theorem hasPlanarKellerCollision
    (E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :
    HC4.HasPlanarKellerCollision K := by
  let C := E.cocharacter
  rcases C.hasSecondMarkedTerminalZero with ⟨z, hz0, hzw⟩
  fin_cases z

  · exact (hz0 rfl).elim

  · have h1 : C.weight (1 : Fin 4) = 0 := by
      simpa using hzw
    have h2d : C.weight (2 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        1 2 (by decide) h1 (by decide) (by decide)
    have h3d : C.weight (3 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        1 3 (by decide) h1 (by decide) (by decide)
    let rho : Equiv.Perm (Fin 4) := Equiv.refl (Fin 4)
    have hweight :
        (fun j : Fin 4 => (C.weight (rho.symm j) : ℤ)) =
          standardTwoZeroTerminalWeight (C.degree : ℤ) := by
      funext i
      fin_cases i
      · change (C.weight (rho.symm (0 : Fin 4)) : ℤ) = 0
        simp [rho, C.weight_zero]
      · change (C.weight (rho.symm (1 : Fin 4)) : ℤ) = 0
        simp [rho, h1]
      · change
          (C.weight (rho.symm (2 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        simp [rho, h2d]
      · change
          (C.weight (rho.symm (3 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        simp [rho, h3d]
    exact C.hasPlanarKellerCollision_of_standardized rho hweight

  · have h2 : C.weight (2 : Fin 4) = 0 := by
      simpa using hzw
    have h1d : C.weight (1 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        2 1 (by decide) h2 (by decide) (by decide)
    have h3d : C.weight (3 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        2 3 (by decide) h2 (by decide) (by decide)
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
    have hr0 : rho.symm (0 : Fin 4) = 0 := by decide
    have hr1 : rho.symm (1 : Fin 4) = 2 := by decide
    have hr2 : rho.symm (2 : Fin 4) = 1 := by decide
    have hr3 : rho.symm (3 : Fin 4) = 3 := by decide
    have hweight :
        (fun j : Fin 4 => (C.weight (rho.symm j) : ℤ)) =
          standardTwoZeroTerminalWeight (C.degree : ℤ) := by
      funext i
      fin_cases i
      · change (C.weight (rho.symm (0 : Fin 4)) : ℤ) = 0
        rw [hr0]
        exact_mod_cast C.weight_zero
      · change (C.weight (rho.symm (1 : Fin 4)) : ℤ) = 0
        rw [hr1]
        exact_mod_cast h2
      · change
          (C.weight (rho.symm (2 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        rw [hr2]
        exact_mod_cast h1d
      · change
          (C.weight (rho.symm (3 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        rw [hr3]
        exact_mod_cast h3d
    exact C.hasPlanarKellerCollision_of_standardized rho hweight

  · have h3 : C.weight (3 : Fin 4) = 0 := by
      simpa using hzw
    have h1d : C.weight (1 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        3 1 (by decide) h3 (by decide) (by decide)
    have h2d : C.weight (2 : Fin 4) = C.degree :=
      C.weight_eq_degree_of_secondZero
        3 2 (by decide) h3 (by decide) (by decide)
    let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
    have hr0 : rho.symm (0 : Fin 4) = 0 := by decide
    have hr1 : rho.symm (1 : Fin 4) = 3 := by decide
    have hr2 : rho.symm (2 : Fin 4) = 2 := by decide
    have hr3 : rho.symm (3 : Fin 4) = 1 := by decide
    have hweight :
        (fun j : Fin 4 => (C.weight (rho.symm j) : ℤ)) =
          standardTwoZeroTerminalWeight (C.degree : ℤ) := by
      funext i
      fin_cases i
      · change (C.weight (rho.symm (0 : Fin 4)) : ℤ) = 0
        rw [hr0]
        exact_mod_cast C.weight_zero
      · change (C.weight (rho.symm (1 : Fin 4)) : ℤ) = 0
        rw [hr1]
        exact_mod_cast h3
      · change
          (C.weight (rho.symm (2 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        rw [hr2]
        exact_mod_cast h2d
      · change
          (C.weight (rho.symm (3 : Fin 4)) : ℤ) =
            (C.degree : ℤ)
        rw [hr3]
        exact_mod_cast h1d
    exact C.hasPlanarKellerCollision_of_standardized rho hweight

/-- The same endpoint therefore proves failure of the exact planar JC2
injectivity interface, without assuming its negation as input. -/
theorem not_planarJC2
    (E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :
    ¬ HC4.PlanarJC2Injectivity K :=
  E.hasPlanarKellerCollision.not_planarJC2

end AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint

end

end HC4.Valuation
