import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalResidualLayers
import Mathlib.Tactic

/-!
# A19.R18.34: leading PR weighted-complement contact layers

The first exposed PR coefficient is now reduced to literal finite contact
layers.  R18.29--R18.33 already identify the leading contact slice, the
parameter/source Euler scalars, and the extremal support ceiling.  Here we
consume the actual straightened PR mixed-complement formula and compute its
leading `(qN,N)` layer.

The result is the exact scalar entering the self-pair calculation:

    y_N = N (D - r - qN) S_N.

The two small transport lemmas below are private.  They merely state that an
honest coefficient-field constant survives exact parameter-layer extraction
and longitudinal coefficient extraction as the same constant; they are not a
new product clock or filtration interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

private theorem familyParameterLayer_constant_mul
    (c : K)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) :
    familyParameterLayer
        (MvPolynomial.C (Polynomial.C c) * F) q =
      MvPolynomial.C c * familyParameterLayer F q := by
  apply MvPolynomial.ext
  intro d
  rw [familyParameterLayer_coeff]
  rw [MvPolynomial.coeff_C_mul]
  rw [Polynomial.coeff_C_mul]
  rw [MvPolynomial.coeff_C_mul]
  rw [familyParameterLayer_coeff]

private theorem finSuccEquiv_coeff_constant_mul
    (c : K)
    (F : MvPolynomial (Fin 4) K)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C c * F)).coeff n =
      MvPolynomial.C c * (MvPolynomial.finSuccEquiv K 3 F).coeff n := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]

/-- **R18.34 leading mixed-complement layer.**  The straightened PR mixed
complement entry on the retained leading slice is exactly
`N (D-r-qN) S_N`.  No determinant or Schur vanishing is used. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingWeightedEulerShear_yLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (P.contactWeightedEulerShear qsPrContactSchurPermutation).y E.qN)).coeff
        E.next.N =
      MvPolynomial.C
          ((E.next.N : K) *
            ((T.topFace.degree : K) - (P.profileWeight : K) - (E.qN : K))) *
        E.leading.slice := by
  rw [P.pr_contactWeightedEulerShear_y]
  rw [familyParameterLayer_sub_exact]
  rw [map_sub, Polynomial.coeff_sub]
  have hfirst :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (MvPolynomial.C
              (Polynomial.C
                ((T.topFace.degree : K) - (P.profileWeight : K))) *
            HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qN)).coeff
          E.next.N =
        MvPolynomial.C
            ((T.topFace.degree : K) - (P.profileWeight : K)) *
          (MvPolynomial.C (E.next.N : K) * E.leading.slice) := by
    rw [familyParameterLayer_constant_mul]
    rw [finSuccEquiv_coeff_constant_mul]
    rw [E.contactLeadingSourceEulerLayer_eq]
  have hsecond :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily)) E.qN)).coeff
          E.next.N =
        MvPolynomial.C (E.qN : K) *
          (MvPolynomial.C (E.next.N : K) * E.leading.slice) := by
    rw [familyParameterLayer_familyParameterEuler]
    rw [← MvPolynomial.C_eq_coe_nat]
    rw [finSuccEquiv_coeff_constant_mul]
    rw [E.contactLeadingSourceEulerLayer_eq]
  rw [hfirst, hsecond]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
