import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedEulerFamily
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfaceSchur
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import Mathlib.Tactic

/-!
# A19.R18: weighted-Euler straightening of the cyclic contact Schur quotient

The three genuine other-facet branches use different active transverse pairs,
but the final contact calculation should see the same ordered quotient in every
case:

    (active₀, active₁ | longitudinal x₀, omitted transverse coordinate).

The historical `.sp` permutation places those last two coordinates in the
opposite order.  We therefore expose closing permutations with a uniform
complement order.

On the Euler-scaled contact Hessian, replace the omitted transverse direction
by the contact weighted-Euler direction

    omitted + profileWeight * x₀ + active₀ + active₁.

This is exactly `GeneralFourBlock.shearSecondComplement` with `lam = 1`.
Consequently the denominator-cleared Schur determinant is unchanged.  The
support-wide weighted Euler identities in the imported R18 owner can now be
applied entrywise to this straightened block without any endpoint
extrapolation, localization, or division.

The raw complementary determinant is not the cleared Schur determinant.  The
exact correction formula recorded below shows that their difference is
controlled by the three bordered `3 x 3` Schur minors, the full determinant,
and one final mixed coupling minor square.  Thus later product-clock code has a
precise algebraic target and cannot silently discard the active/profile
coupling terms.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe v
variable {R : Type v} [CommRing R]

namespace GeneralFourBlock

/-- **Exact raw-complement / Schur correction identity.**

For the symmetric `2+2` block with active block

    A = [[a,b],[b,d]],

coupling block `B = [[p,q],[r,s]]`, and raw complementary block
`C = [[x,y],[y,z]]`, the active-pivot multiple of `det C` is the sum of the
three bordered `3 x 3` Schur numerators and the full determinant correction,
plus the square of the mixed coupling minor `p*s-q*r`.

In particular, vanishing of the cleared Schur determinant or even of the full
determinant does not by itself identify `activeDet * det C` with zero: the
mixed coupling square is a genuine residual term. -/
theorem activeDet_mul_rawComplementDet_eq_schur_coupling_correction
    (H : GeneralFourBlock R) :
    H.activeDet * (H.x * H.z - H.y * H.y) =
      H.x * H.schurC + H.z * H.schurA - 2 * H.y * H.schurB -
        H.determinantCore + (H.p * H.s - H.q * H.r) ^ 2 := by
  unfold HC4.Newton.GeneralFourBlock.schurA
    HC4.Newton.GeneralFourBlock.schurB
    HC4.Newton.GeneralFourBlock.schurC
    HC4.Newton.GeneralFourBlock.determinantCore
  unfold HC4.Newton.GeneralFourBlock.activeDet
  ring

end GeneralFourBlock

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- `.pr`: active pair `(2,3)`, then longitudinal `0`, then omitted `1`. -/
def qsPrContactSchurPermutation : Equiv.Perm (Fin 4) :=
  qsPrSuperfaceSchurPermutation

/-- `.sp`: active pair `(1,3)`, then longitudinal `0`, then omitted `2`.
The existing superface permutation has the two complementary coordinates in
reverse order, so precomposing by the domain swap `(2 3)` fixes only that
ordering. -/
def qsSpContactSchurPermutation : Equiv.Perm (Fin 4) :=
  (Equiv.swap (2 : Fin 4) 3).trans qsSpSuperfaceSchurPermutation

/-- `.rq`: active pair `(1,2)`, then longitudinal `0`, then omitted `3`. -/
def qsRqContactSchurPermutation : Equiv.Perm (Fin 4) :=
  qsRqSuperfaceSchurPermutation

@[simp] theorem qsPrContactSchurPermutation_zero :
    qsPrContactSchurPermutation (0 : Fin 4) = 2 := by
  decide

@[simp] theorem qsPrContactSchurPermutation_one :
    qsPrContactSchurPermutation (1 : Fin 4) = 3 := by
  decide

@[simp] theorem qsPrContactSchurPermutation_two :
    qsPrContactSchurPermutation (2 : Fin 4) = 0 := by
  decide

@[simp] theorem qsPrContactSchurPermutation_three :
    qsPrContactSchurPermutation (3 : Fin 4) = 1 := by
  decide

@[simp] theorem qsSpContactSchurPermutation_zero :
    qsSpContactSchurPermutation (0 : Fin 4) = 1 := by
  decide

@[simp] theorem qsSpContactSchurPermutation_one :
    qsSpContactSchurPermutation (1 : Fin 4) = 3 := by
  decide

@[simp] theorem qsSpContactSchurPermutation_two :
    qsSpContactSchurPermutation (2 : Fin 4) = 0 := by
  decide

@[simp] theorem qsSpContactSchurPermutation_three :
    qsSpContactSchurPermutation (3 : Fin 4) = 2 := by
  decide

@[simp] theorem qsRqContactSchurPermutation_zero :
    qsRqContactSchurPermutation (0 : Fin 4) = 1 := by
  decide

@[simp] theorem qsRqContactSchurPermutation_one :
    qsRqContactSchurPermutation (1 : Fin 4) = 2 := by
  decide

@[simp] theorem qsRqContactSchurPermutation_two :
    qsRqContactSchurPermutation (2 : Fin 4) = 0 := by
  decide

@[simp] theorem qsRqContactSchurPermutation_three :
    qsRqContactSchurPermutation (3 : Fin 4) = 3 := by
  decide

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Euler-scaled source Hessian in a closing cyclic coordinate order. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.contactEulerHessianFourBlock
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.eulerScaledHessian P.contactFamily).submatrix rho rho)

/-- Replace the uniformly ordered omitted transverse direction by the full
contact weighted-Euler direction. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  (P.contactEulerHessianFourBlock rho).shearSecondComplement
    1 (P.profileWeight : MvPolynomial (Fin 4) (Polynomial K)) 1 1

/-- **R18 Schur straightening covariance.**  Because the omitted direction
enters the weighted-Euler direction with coefficient one, straightening does
not change the denominator-cleared Schur determinant. -/
@[simp] theorem QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear_schurDetCore
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.contactWeightedEulerShear rho).schurDetCore =
      (P.contactEulerHessianFourBlock rho).schurDetCore := by
  simp [QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear]

/-- The straightening also leaves the active pivot literally unchanged. -/
@[simp] theorem QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear_activeDet
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.contactWeightedEulerShear rho).activeDet =
      (P.contactEulerHessianFourBlock rho).activeDet := by
  simp [QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear]

/-- Euler-scaled Hessian symmetry over the contact coefficient ring. -/
private theorem contactEulerScaledHessian_symmetric
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.eulerScaledHessian F i j =
      HC4.Polynomial.eulerScaledHessian F j i := by
  rw [HC4.Polynomial.eulerScaledHessian_apply,
    HC4.Polynomial.eulerScaledHessian_apply]
  rw [pderiv_comm_commRing]
  ring

/-- **R18.21 `.pr` straightened mixed complement entry.**  The second
complement after weighted-Euler straightening is the full source weighted
Euler direction, so its pairing with the longitudinal direction is exactly the
falling weighted-Euler row with the parameter-Euler term moved to the right. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contactWeightedEulerShear_y
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    (P.contactWeightedEulerShear qsPrContactSchurPermutation).y =
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) - (P.profileWeight : K))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily -
      familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) := by
  have h := P.contactFamily_fallingWeightedEulerRow (0 : Fin 4)
  simp only [if_pos rfl] at h
  rw [QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear,
    QsOtherFacetContactQuadraticReesPackage.contactEulerHessianFourBlock]
  simp only [GeneralFourBlock.shearSecondComplement,
    GeneralFourBlock.ofSymmetricMatrix, Matrix.submatrix_apply,
    qsPrContactSchurPermutation_zero, qsPrContactSchurPermutation_one,
    qsPrContactSchurPermutation_two, qsPrContactSchurPermutation_three,
    one_mul]
  rw [contactEulerScaledHessian_symmetric P.contactFamily (2 : Fin 4) 0,
    contactEulerScaledHessian_symmetric P.contactFamily (3 : Fin 4) 0]
  have hr :
      (P.profileWeight : MvPolynomial (Fin 4) (Polynomial K)) =
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) := by
    norm_num
  rw [hr]
  linear_combination h

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
