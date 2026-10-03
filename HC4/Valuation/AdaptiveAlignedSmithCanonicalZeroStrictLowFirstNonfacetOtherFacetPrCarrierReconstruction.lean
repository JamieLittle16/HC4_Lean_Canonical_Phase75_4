import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrCarrierContactLayer
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceNormalForm
import Mathlib.Tactic

/-!
# A19 source-honest PR carrier reconstruction data

The normalized planar carrier and the primitive highest pair slice are already
available separately.  This file starts the final reconstruction by joining
those two pieces of infrastructure without recreating any support point.

For every actual planar-carrier monomial we package, in one place,

* membership in the represented zero-clock source;
* nonvanishing of the literal carrier and source coefficients; and
* the unchanged, nonzero coefficient in the exact canonical contact-Rees
  layer.

Applying this to the two monomials of the primitive highest slice gives the
left/right source-honest normal forms needed by the final two-function carrier
adapter.  In particular the next file can name the two genuine source
coefficients directly instead of repeatedly reconstructing provenance from
initial forms.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Literal coefficient provenance for one monomial of the normalized planar
carrier.  The contact coefficient is taken in its exact source-deficit layer;
no contact/ray/blocker clock identification is made. -/
structure QsOtherFacetPrCarrierCoefficientProvenance
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (e : Fin 4 →₀ ℕ) where
  carrier_mem : e ∈ P.carrier.support
  source_mem :
    e ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support
  carrier_coeff_ne : MvPolynomial.coeff e P.carrier ≠ 0
  source_coeff_ne :
    MvPolynomial.coeff e
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) ≠ 0
  contact_coeff_eq_source :
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0))) =
      MvPolynomial.coeff e
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
  contact_coeff_ne :
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0))) ≠ 0

/-- Every actual planar-carrier support point has the preceding literal
source/contact provenance package. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_coefficientProvenance
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    QsOtherFacetPrCarrierCoefficientProvenance C P R e := by
  have hsource := P.support_source he
  have hcontact := P.contactFamily_coeff_at_source_deficit R he
  exact {
    carrier_mem := he
    source_mem := hsource
    carrier_coeff_ne := MvPolynomial.mem_support_iff.mp he
    source_coeff_ne := MvPolynomial.mem_support_iff.mp hsource
    contact_coeff_eq_source := hcontact.1
    contact_coeff_ne := hcontact.2
  }

/-- Left primitive highest-slice orientation, together with the two genuine
source/contact coefficients. -/
structure QsOtherFacetPrHighestSliceLeftSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  n : ℕ
  V : ℕ
  e0 : Fin 4 →₀ ℕ
  e1 : Fin 4 →₀ ℕ
  n_two_le : 2 ≤ n
  V_pos : 0 < V
  slice_support_eq : S.slice.support = {e0, e1}
  e0_zero : e0 0 = 0
  e0_one : e0 1 = n
  e0_two : e0 2 = 1
  e0_three : e0 3 = V * n
  e1_zero : e1 0 = 1
  e1_one : e1 1 = n - 1
  e1_two : e1 2 = 0
  e1_three : e1 3 = V * (n - 1)
  e0_provenance : QsOtherFacetPrCarrierCoefficientProvenance C P R e0
  e1_provenance : QsOtherFacetPrCarrierCoefficientProvenance C P R e1
  e0_slice_coeff_eq_source :
    MvPolynomial.coeff e0 S.slice =
      MvPolynomial.coeff e0
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
  e1_slice_coeff_eq_source :
    MvPolynomial.coeff e1 S.slice =
      MvPolynomial.coeff e1
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)

/-- Right/transverse-swapped primitive highest-slice orientation, again with
literal source/contact coefficient provenance. -/
structure QsOtherFacetPrHighestSliceRightSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C) where
  n : ℕ
  V : ℕ
  e0 : Fin 4 →₀ ℕ
  e1 : Fin 4 →₀ ℕ
  n_two_le : 2 ≤ n
  V_pos : 0 < V
  slice_support_eq : S.slice.support = {e0, e1}
  e0_zero : e0 0 = 0
  e0_one : e0 1 = n
  e0_two : e0 2 = V * n
  e0_three : e0 3 = 1
  e1_zero : e1 0 = 1
  e1_one : e1 1 = n - 1
  e1_two : e1 2 = V * (n - 1)
  e1_three : e1 3 = 0
  e0_provenance : QsOtherFacetPrCarrierCoefficientProvenance C P R e0
  e1_provenance : QsOtherFacetPrCarrierCoefficientProvenance C P R e1
  e0_slice_coeff_eq_source :
    MvPolynomial.coeff e0 S.slice =
      MvPolynomial.coeff e0
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
  e1_slice_coeff_eq_source :
    MvPolynomial.coeff e1 S.slice =
      MvPolynomial.coeff e1
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)

/-- **Source-honest primitive highest-slice reconstruction frontier.**
The two abstract support points supplied by the existing normal-form theorem
are immediately upgraded to literal nonzero carrier/source/contact
coefficients. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_highest_slice_source_data_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrHighestSliceLeftSourceData C P S R) ∨
      Nonempty (QsOtherFacetPrHighestSliceRightSourceData C P S R) := by
  rcases S.pr_highest_slice_normal_form_of_nontrivial
      hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with
      ⟨n, V, e0, e1, hn, hV, hsupp,
        he00, he01, he02, he03, he10, he11, he12, he13⟩
    have he0S : e0 ∈ S.slice.support := by
      rw [hsupp]
      simp
    have he1S : e1 ∈ S.slice.support := by
      rw [hsupp]
      simp
    have he0P := (S.support_parent_and_pairLevel he0S).1
    have he1P := (S.support_parent_and_pairLevel he1S).1
    left
    exact ⟨{
      n := n
      V := V
      e0 := e0
      e1 := e1
      n_two_le := hn
      V_pos := hV
      slice_support_eq := hsupp
      e0_zero := he00
      e0_one := he01
      e0_two := he02
      e0_three := he03
      e1_zero := he10
      e1_one := he11
      e1_two := he12
      e1_three := he13
      e0_provenance := P.pr_coefficientProvenance R he0P
      e1_provenance := P.pr_coefficientProvenance R he1P
      e0_slice_coeff_eq_source := S.coeff_eq_source_of_mem he0S
      e1_slice_coeff_eq_source := S.coeff_eq_source_of_mem he1S
    }⟩
  · rcases hright with
      ⟨n, V, e0, e1, hn, hV, hsupp,
        he00, he01, he02, he03, he10, he11, he12, he13⟩
    have he0S : e0 ∈ S.slice.support := by
      rw [hsupp]
      simp
    have he1S : e1 ∈ S.slice.support := by
      rw [hsupp]
      simp
    have he0P := (S.support_parent_and_pairLevel he0S).1
    have he1P := (S.support_parent_and_pairLevel he1S).1
    right
    exact ⟨{
      n := n
      V := V
      e0 := e0
      e1 := e1
      n_two_le := hn
      V_pos := hV
      slice_support_eq := hsupp
      e0_zero := he00
      e0_one := he01
      e0_two := he02
      e0_three := he03
      e1_zero := he10
      e1_one := he11
      e1_two := he12
      e1_three := he13
      e0_provenance := P.pr_coefficientProvenance R he0P
      e1_provenance := P.pr_coefficientProvenance R he1P
      e0_slice_coeff_eq_source := S.coeff_eq_source_of_mem he0S
      e1_slice_coeff_eq_source := S.coeff_eq_source_of_mem he1S
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
