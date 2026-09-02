import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedEuler
import Mathlib.Tactic

/-!
# A19.R18: second-order weighted Euler identities for the contact Rees

The support-wide contact Euler equation must be used at Hessian level before
the final cyclic Schur straightening.  For a source exponent `d`, write `m`
for the parameter exponent of its coefficient in the honest contact Rees.  The
falling Hessian factors satisfy

    m dᵢ + r d₀(dᵢ-δᵢ₀) + Σⱼ₌₁³ dⱼ(dᵢ-δᵢⱼ)
      = (D-wᵢ)dᵢ,

where `w₀=r` and `w₁=w₂=w₃=1`.  Likewise the parameter row satisfies

    m(m-1) + m(r d₀+d₁+d₂+d₃) = (D-1)m.

These are exactly the second-order equations needed to replace the omitted
unit-weight transverse row/column by the parameter direction modulo the active
source directions.  Both statements are proved coefficientwise on the actual
reverse Rees and therefore introduce no global homogeneity assumption on the
represented source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 falling source-row weighted Euler identity.**  The parameter/source
mixed entry plus the contact-weighted source Euler-Hessian row is the expected
`D-wᵢ` multiple of the first source Euler derivative. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_fallingWeightedEulerRow_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i : Fin 4) (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d (HC4.Polynomial.mvEuler i P.contactFamily)) +
      Polynomial.C (P.profileWeight : K) *
        MvPolynomial.coeff d
          (HC4.Polynomial.eulerScaledHessian P.contactFamily i (0 : Fin 4)) +
      MvPolynomial.coeff d
          (HC4.Polynomial.eulerScaledHessian P.contactFamily i (1 : Fin 4)) +
      MvPolynomial.coeff d
          (HC4.Polynomial.eulerScaledHessian P.contactFamily i (2 : Fin 4)) +
      MvPolynomial.coeff d
          (HC4.Polynomial.eulerScaledHessian P.contactFamily i (3 : Fin 4)) =
      Polynomial.C
          ((T.topFace.degree : K) -
            (if i = (0 : Fin 4) then (P.profileWeight : K) else 1)) *
        MvPolynomial.coeff d (HC4.Polynomial.mvEuler i P.contactFamily) := by
  have hnat (n : ℕ) :
      (n : Polynomial K) = Polynomial.C (n : K) := by
    exact (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  fin_cases i <;>
    rw [P.contactFamily_parameterEuler_sourceEuler_coeff] <;>
    simp only [coeff_eulerScaledHessian, coeff_mvEuler] <;>
    rw [hnat (d (0 : Fin 4)), hnat (d (1 : Fin 4)),
      hnat (d (2 : Fin 4)), hnat (d (3 : Fin 4))] <;>
    simp only [map_sub, map_add, map_mul] <;>
    norm_num <;>
    (try simp only [h02, h03, h12, h13, if_false]) <;>
    ring

/-- **R18 falling parameter-row weighted Euler identity.**  The second
parameter-Euler entry plus the contact-weighted parameter/source mixed row is
`D-1` times the first parameter-Euler entry. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_fallingWeightedEulerParameterRow_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative (MvPolynomial.coeff d P.contactFamily)) +
      Polynomial.C (P.profileWeight : K) *
        (Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily))) +
      Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (1 : Fin 4) P.contactFamily)) +
      Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (2 : Fin 4) P.contactFamily)) +
      Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (3 : Fin 4) P.contactFamily)) =
      Polynomial.C ((T.topFace.degree : K) - 1) *
        (Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d P.contactFamily)) := by
  have hnat (n : ℕ) :
      (n : Polynomial K) = Polynomial.C (n : K) := by
    exact (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
  rw [P.contactFamily_parameterSecondEuler_coeff,
    P.contactFamily_parameterEuler_sourceEuler_coeff,
    P.contactFamily_parameterEuler_sourceEuler_coeff,
    P.contactFamily_parameterEuler_sourceEuler_coeff,
    P.contactFamily_parameterEuler_sourceEuler_coeff,
    P.contactFamily_parameterEuler_coeff]
  rw [hnat (d (0 : Fin 4)), hnat (d (1 : Fin 4)),
    hnat (d (2 : Fin 4)), hnat (d (3 : Fin 4))]
  simp only [map_sub, map_add, map_mul]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation