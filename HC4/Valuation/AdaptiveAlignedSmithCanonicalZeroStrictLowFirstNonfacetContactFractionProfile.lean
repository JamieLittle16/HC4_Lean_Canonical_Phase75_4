import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLongitudinalProfile
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# A19.115: inject the symbolic contact profile into a field

A19.114 deliberately keeps the transverse coefficients symbolic in
`MvPolynomial (Fin 3) K`, an integral domain.  The existing stationary profile
rigidity theorem is field-valued, so we now apply the canonical injective map
into the fraction field of that transverse polynomial ring.

Injectivity preserves the constant coefficient and ordinary polynomial degree
exactly.  Consequently the degree-at-least-two witness and the
`natDegree * profileWeight <= D` support bound pass across unchanged.  No
transverse evaluation and hence no coefficient cancellation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Fraction field of the symbolic transverse coefficient ring. -/
abbrev qsContactProfileField (K : Type u) [Field K] :=
  FractionRing (MvPolynomial (Fin 3) K)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Fraction-field profile retaining all raw longitudinal coefficient data. -/
noncomputable def qsContactFractionLongitudinalProfile :
    Polynomial (qsContactProfileField K) :=
  Polynomial.map
    (algebraMap (MvPolynomial (Fin 3) K) (qsContactProfileField K))
    (qsContactRawLongitudinalProfile (K := K) (T := T))

/-- All non-residual data needed by the field-valued staircase rigidity
argument. -/
structure QsOtherFacetContactFractionProfilePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetContactQuadraticReesPackage C) where
  profile : Polynomial (qsContactProfileField K)
  profile_eq : profile = qsContactFractionLongitudinalProfile (K := K) (T := T)
  coeff_zero_ne : profile.coeff 0 ≠ 0
  support_bound : profile.natDegree * P.profileWeight ≤ T.topFace.degree
  degree_two_le : 2 ≤ profile.natDegree

/-- **A19.115 field lift of the exact raw profile.** -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.fractionProfilePackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Nonempty (QsOtherFacetContactFractionProfilePackage C P) := by
  let A := MvPolynomial (Fin 3) K
  let L := qsContactProfileField K
  let ι : A →+* L := algebraMap A L
  have hι : Function.Injective ι := IsFractionRing.injective A L
  let h : Polynomial L := Polynomial.map ι R.profile
  have hdegree : h.natDegree = R.profile.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective hι R.profile
  have hzero : h.coeff 0 ≠ 0 := by
    intro hz
    apply R.coeff_zero_ne
    apply hι
    simpa [h, ι] using hz
  have hsupport : h.natDegree * P.profileWeight ≤ T.topFace.degree := by
    rw [hdegree]
    exact R.support_bound
  have htwo : 2 ≤ h.natDegree := by
    rw [hdegree]
    exact R.degree_two_le
  exact ⟨{
    profile := h
    profile_eq := by
      dsimp [h, qsContactFractionLongitudinalProfile, A, L, ι]
      rw [R.profile_eq]
    coeff_zero_ne := hzero
    support_bound := hsupport
    degree_two_le := htwo
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
