import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalResidualLayers
import Mathlib.Tactic

/-!
# A19.R18.34-R18.35: leading PR weighted-complement contact layers

The first exposed PR coefficient is now reduced to literal finite contact
layers.  R18.29--R18.33 already identify the leading contact slice, the
parameter/source Euler scalars, and the extremal support ceiling.  Here we
consume the actual straightened PR mixed and quadratic complement formulas
and compute their leading `(qN,N)` layers.

The mixed entry is

    y_N = N (D - r - qN) S_N,

while the quadratic entry is

    z_N =
      [D(D-1) - 2(D-1)qN + qN(qN-1) + r(1-r)N] S_N.

The small transport lemmas below are private.  They merely state that honest
coefficient-field constants and finite sums survive exact parameter-layer
extraction in the expected way; they are not a new product clock or
filtration interface.
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

private theorem familyParameterLayer_add_exact
    (F G : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) :
    familyParameterLayer (F + G) q =
      familyParameterLayer F q + familyParameterLayer G q := by
  apply MvPolynomial.ext
  intro d
  simp [familyParameterLayer_coeff]

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

private theorem familyParameterLayer_two_constant_mul
    (c : K)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) :
    familyParameterLayer
        (2 * MvPolynomial.C (Polynomial.C c) * F) q =
      MvPolynomial.C ((2 : K) * c) * familyParameterLayer F q := by
  have hc :
      (2 * MvPolynomial.C (Polynomial.C c) :
        MvPolynomial (Fin 4) (Polynomial K)) =
        MvPolynomial.C (Polynomial.C ((2 : K) * c)) := by
    simp only [map_mul, map_ofNat]
  rw [hc]
  exact familyParameterLayer_constant_mul ((2 : K) * c) F q

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
  simp only [map_mul, map_sub]
  ring

/-- **R18.35 leading quadratic-complement layer.**  The straightened weighted
source self-pair on the retained leading slice is the literal quadratic Euler
scalar obtained from the contact, first-parameter-Euler,
second-parameter-Euler, and longitudinal-source-Euler layers. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingWeightedEulerShear_zLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (P.contactWeightedEulerShear qsPrContactSchurPermutation).z E.qN)).coeff
        E.next.N =
      MvPolynomial.C
          ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1) -
            (2 : K) * ((T.topFace.degree : K) - 1) * (E.qN : K) +
            (E.qN : K) * ((E.qN : K) - 1) +
            (P.profileWeight : K) * (1 - (P.profileWeight : K)) *
              (E.next.N : K)) *
        E.leading.slice := by
  rw [P.pr_contactWeightedEulerShear_z]
  simp only [familyParameterLayer_add_exact, familyParameterLayer_sub_exact,
    map_add, map_sub, Polynomial.coeff_add, Polynomial.coeff_sub]
  have hfirst :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (MvPolynomial.C
              (Polynomial.C
                ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1))) *
            P.contactFamily) E.qN)).coeff E.next.N =
        MvPolynomial.C
            ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1)) *
          E.leading.slice := by
    rw [familyParameterLayer_constant_mul]
    rw [finSuccEquiv_coeff_constant_mul]
    change MvPolynomial.C _ * R.contactLongitudinalParameterLayer E.qN E.next.N = _
    rw [E.contactLeadingParameterLayer_eq]
  have hsecond :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (2 * MvPolynomial.C
              (Polynomial.C ((T.topFace.degree : K) - 1)) *
            familyParameterEuler P.contactFamily) E.qN)).coeff E.next.N =
        MvPolynomial.C
            ((2 : K) * ((T.topFace.degree : K) - 1)) *
          (MvPolynomial.C (E.qN : K) * E.leading.slice) := by
    rw [familyParameterLayer_two_constant_mul]
    rw [finSuccEquiv_coeff_constant_mul]
    rw [E.contactLeadingParameterEulerLayer_eq]
  have hthird := E.contactLeadingParameterSecondEulerLayer_eq
  have hfourth :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (MvPolynomial.C
              (Polynomial.C
                ((P.profileWeight : K) * (1 - (P.profileWeight : K)))) *
            HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) E.qN)).coeff
          E.next.N =
        MvPolynomial.C
            ((P.profileWeight : K) * (1 - (P.profileWeight : K))) *
          (MvPolynomial.C (E.next.N : K) * E.leading.slice) := by
    rw [familyParameterLayer_constant_mul]
    rw [finSuccEquiv_coeff_constant_mul]
    rw [E.contactLeadingSourceEulerLayer_eq]
  simp only [map_add, map_sub] at hfirst hsecond hthird hfourth
  rw [hfirst, hsecond, hthird, hfourth]
  simp only [map_mul, map_sub, map_add, map_one]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
