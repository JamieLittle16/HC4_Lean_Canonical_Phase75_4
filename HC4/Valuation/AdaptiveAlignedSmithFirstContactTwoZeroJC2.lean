import HC4.Valuation.AdaptiveAlignedSmithFirstContactUniqueZeroElimination
import HC4.Valuation.AdaptiveAlignedSmithFirstContactSquareContactElimination
import HC4.Newton.TerminalTwoZeroJC2Endpoint
import HC4.Newton.TerminalCoordinatePermutation
import Mathlib.Tactic

/-!
# A19.4: JC2 closes every honest first-contact terminal cocharacter

The adaptive first-contact terminal package already carries an actual
polynomial Monge--Ampere fibre, a distinct exact gradient collision, and an
honest nonnegative integral terminal source cocharacter.

The marked longitudinal coordinate has terminal weight zero.  The green
unique-zero elimination theorem forces a second zero-weight coordinate.  In
four variables the complement-weight relation then forces the other two
weights to equal the common terminal degree.  After a coordinate permutation
fixing the first zero and moving the second zero into coordinate `1`, the
weight is therefore exactly

    (0, 0, d, d).

The existing standard two-zero endpoint theorem applies under planar JC2 and
makes the renamed four-dimensional gradient injective.  Coordinate
permutation preserves injectivity, contradicting the exact terminal
collision.

Thus JC2 enters only at the genuine two-zero endpoint.  No terminal
cocharacter, support line, or balance relation is manufactured here: the
cocharacter is an input field of the honest first-contact terminal package.
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

/-- **JC2 closes every honest first-contact terminal cocharacter.** -/
theorem impossible_of_JC2
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    False := by
  rcases C.hasSecondMarkedTerminalZero with ⟨z, hz0, hzw⟩
  fin_cases z

  · exact (hz0 rfl).elim

  · have h1 : C.weight (1 : Fin 4) = 0 := by
      simpa using hzw
    have h1Z : ((C.weight (1 : Fin 4) : ℕ) : ℤ) = 0 := by
      exact_mod_cast h1
    have hinj : Function.Injective (mvGradientMap T.fibre) :=
      nonnegativeTerminalFace_two_standard_zeros_gradient_injective_of_JC2
        hJC2
        C.residualNonScalarJump.1
        C.nonnegative
        C.integralWeight_zero
        h1Z
        T.mongeAmpere
    exact
      exactGradientCollision_impossible_of_injective
        T.fibre T.leftPoint T.rightPoint T.distinct hinj T.exactCollision

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
      · rw [hr0]
        simp [standardTwoZeroTerminalWeight, C.weight_zero]
      · rw [hr1]
        simp [standardTwoZeroTerminalWeight, h2]
      · rw [hr2]
        simp [standardTwoZeroTerminalWeight, h1d]
      · rw [hr3]
        simp [standardTwoZeroTerminalWeight, h3d]
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
    have hinjRenamed :
        Function.Injective
          (mvGradientMap (MvPolynomial.rename rho T.fibre)) :=
      standardTwoZero_terminal_gradient_injective_of_JC2
        hJC2 C.degree_pos hhomRenamed hMARenamed
    have hinj : Function.Injective (mvGradientMap T.fibre) :=
      mvGradientMap_injective_of_rename_perm rho T.fibre hinjRenamed
    exact
      exactGradientCollision_impossible_of_injective
        T.fibre T.leftPoint T.rightPoint T.distinct hinj T.exactCollision

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
      · rw [hr0]
        simp [standardTwoZeroTerminalWeight, C.weight_zero]
      · rw [hr1]
        simp [standardTwoZeroTerminalWeight, h3]
      · rw [hr2]
        simp [standardTwoZeroTerminalWeight, h2d]
      · rw [hr3]
        simp [standardTwoZeroTerminalWeight, h1d]
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
    have hinjRenamed :
        Function.Injective
          (mvGradientMap (MvPolynomial.rename rho T.fibre)) :=
      standardTwoZero_terminal_gradient_injective_of_JC2
        hJC2 C.degree_pos hhomRenamed hMARenamed
    have hinj : Function.Injective (mvGradientMap T.fibre) :=
      mvGradientMap_injective_of_rename_perm rho T.fibre hinjRenamed
    exact
      exactGradientCollision_impossible_of_injective
        T.fibre T.leftPoint T.rightPoint T.distinct hinj T.exactCollision

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
