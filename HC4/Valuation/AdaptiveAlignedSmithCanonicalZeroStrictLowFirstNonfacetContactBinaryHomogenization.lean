import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLayerGrading
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTransverseReesLayer
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# A19.123: contact Rees as an honest binary profile homogenization

The canonical contact reverse Rees assigns a source monomial `d` parameter
order

    D - (transverseDegree(d) + profileWeight * d₀).

Now perform the already-existing unit transverse source inflation

    x₀ |-> x₀,
    xᵢ |-> tau xᵢ,  i=1,2,3.

The added parameter power is exactly `transverseDegree(d)`, so it cancels the
transverse part of the contact deficit.  The transformed family therefore has
literal source coefficient

    tau^(D - profileWeight*d₀) * c_d.

After `finSuccEquiv`, its coefficient at longitudinal exponent `n` is exactly

    tau^(D - profileWeight*n) * A_n,

where `A_n` is the coefficient of the symbolic A19.114 longitudinal profile.
This is the honest binary weighted homogenization needed by the staircase
Hessian identity; no global weighted homogeneity of the original source is
asserted.
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

/-- Transversely inflated contact Rees.  This is the family in which the
contact grading becomes a pure binary grading in parameter and longitudinal
source degree. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  unitTransverseInflateFamily (K := K) P.contactFamily

/-- Exact source coefficient of the binary-homogenized contact family. -/
theorem QsOtherFacetContactQuadraticReesPackage.coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d P.binaryHomogenizedFamily =
      Polynomial.X ^
          (T.topFace.degree - P.profileWeight * d (0 : Fin 4)) *
        Polynomial.C
          (MvPolynomial.coeff d
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family)) := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily]
  rw [coeff_unitTransverseInflateFamily]
  rw [QsOtherFacetContactQuadraticReesPackage.contactFamily]
  rw [reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ F.support
  · rw [if_pos hd]
    have hbound := P.bound d hd
    have hordinary :
        HC4.Polynomial.ordinaryDegree4 d =
          d (0 : Fin 4) + pureLongitudinalTransverseDegree d := by
      simp [HC4.Polynomial.ordinaryDegree4,
        pureLongitudinalTransverseDegree]
      ring
    have hweight :
        Finsupp.weight (qsIntegralContactWeight P.contactGap) d =
          pureLongitudinalTransverseDegree d +
            P.profileWeight * d (0 : Fin 4) := by
      rw [qsIntegralContactWeight_finsupp, hordinary, P.profileWeight_eq]
      ring
    rw [hweight] at hbound ⊢
    rw [← pow_add]
    have hexp :
        pureLongitudinalTransverseDegree d +
            (T.topFace.degree -
              (pureLongitudinalTransverseDegree d +
                P.profileWeight * d (0 : Fin 4))) =
          T.topFace.degree - P.profileWeight * d (0 : Fin 4) := by
      omega
    rw [hexp]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hcoeff]

/-- Binary source-inflation weight: only the longitudinal source coordinate
carries the profile weight. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryInflationWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) : Fin 4 → ℕ :=
  fun i => if i = (0 : Fin 4) then P.profileWeight else 0

/-- The binary inflation weight of a source exponent is exactly profile weight
times longitudinal degree. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryInflationWeight_degree
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight P.binaryInflationWeight d =
      P.profileWeight * d (0 : Fin 4) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  rw [Fin.sum_univ_four]
  simp [QsOtherFacetContactQuadraticReesPackage.binaryInflationWeight,
    nsmul_eq_mul]

/-- **Binary normalization identity.**  Inflating only the longitudinal source
coordinate by `tau^profileWeight` clears the binary reverse grading completely:
the honest binary family becomes the represented source multiplied by the
single common parameter power `tau^D`.

This is the coefficientwise replacement for any illicit global homogeneity
claim about the represented source. -/
theorem QsOtherFacetContactQuadraticReesPackage.adaptiveSmithInflate_binaryHomogenizedFamily_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    adaptiveSmithInflateHom P.binaryInflationWeight P.binaryHomogenizedFamily =
      MvPolynomial.C (Polynomial.X ^ T.topFace.degree) *
        constantPolynomialFamily
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  apply MvPolynomial.ext
  intro d
  rw [coeff_adaptiveSmithInflateHom]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [P.binaryInflationWeight_degree]
  have hright :
      MvPolynomial.coeff d
          (MvPolynomial.C (Polynomial.X ^ T.topFace.degree) *
            constantPolynomialFamily F) =
        Polynomial.X ^ T.topFace.degree *
          Polynomial.C (MvPolynomial.coeff d F) := by
    simp [coeff_constantPolynomialFamily]
  rw [hright]
  by_cases hd : d ∈ F.support
  · have hsource := P.source_weight_le hd
    have hcoord :
        d (0 : Fin 4) ≤ HC4.Polynomial.ordinaryDegree4 d := by
      unfold HC4.Polynomial.ordinaryDegree4
      omega
    have hle : P.profileWeight * d (0 : Fin 4) ≤ T.topFace.degree := by
      rw [P.profileWeight_eq]
      calc
        (P.contactGap + 1) * d (0 : Fin 4) =
            d (0 : Fin 4) + P.contactGap * d (0 : Fin 4) := by ring
        _ ≤ HC4.Polynomial.ordinaryDegree4 d +
              P.contactGap * d (0 : Fin 4) := Nat.add_le_add_right hcoord _
        _ ≤ T.topFace.degree := hsource
    have hexp :
        P.profileWeight * d (0 : Fin 4) +
            (T.topFace.degree - P.profileWeight * d (0 : Fin 4)) =
          T.topFace.degree := by omega
    rw [← pow_add, hexp]
    ring
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hcoeff]

/-- Longitudinal polynomial form of the binary-homogenized contact family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedLongitudinal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    Polynomial (MvPolynomial (Fin 3) (Polynomial K)) :=
  MvPolynomial.finSuccEquiv (Polynomial K) 3 P.binaryHomogenizedFamily

/-- Each longitudinal coefficient is the corresponding A19.114 transverse
coefficient multiplied by the single expected binary parameter monomial. -/
theorem QsOtherFacetContactQuadraticReesPackage.coeff_binaryHomogenizedLongitudinal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (n : ℕ) :
    P.binaryHomogenizedLongitudinal.coeff n =
      MvPolynomial.C
          (Polynomial.X ^ (T.topFace.degree - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C
          ((qsContactRawLongitudinalProfile (K := K) (T := T)).coeff n) := by
  ext m
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedLongitudinal]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [P.coeff_binaryHomogenizedFamily]
  simp only [MvPolynomial.coeff_mul, MvPolynomial.coeff_C,
    MvPolynomial.coeff_map]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation