import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerE2Frontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisPotentialTiming
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamLongitudinalConfinement
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesLowLayerOrder
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerCausality
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.MongeAmpere.MaximalInitial
import HC4.Polynomial.FourExponent
import HC4.Polynomial.WeightedInitial
import HC4.Newton.ScaledContact
import HC4.Newton.FiniteSupportSingularBoundaryVertex
import HC4.Newton.FiniteSupportSingularBoundaryCarrierKernel
import HC4.Newton.FiniteSupportSingularBoundaryKernelOpening
import HC4.Valuation.CoordinateMaxKernelOpeningDegenerateClassification
import HC4.Valuation.CoordinateMaxKernelOpeningLinearPowerFirstBreak
import HC4.Newton.FirstNonfacetLowDegreeSquareSplit
import HC4.Newton.FirstContactNonlinearSupport
import HC4.Newton.FirstContactCrossFacetCarrier
import Mathlib.Tactic

/-!
# E3: balance-free first contact below a pure longitudinal top face

The marked-axis E2 frontier has one especially rigid constructor

    topFace = c * X₀^D,    c ≠ 0.

The represented determinant-one source cannot have all nonlinear support on
the longitudinal axis (G8).  Hence some lower nonlinear monomial leaves one of
the three coordinate facets containing the X₀-axis.  On that chosen facet the
actual maximal ordinary face is completely confined, so the generic
balance-free first-nonfacet selector applies whenever the low-degree source is
tame.

Failure of low-degree tameness is already rigid: it is a literal quadratic
square in the omitted coordinate.  Thus the pure-longitudinal E2 branch
reduces to exactly:

* an honest singular first-contact polynomial together with its genuine
  secondary cross-facet face; or
* an explicit transverse quadratic square on the represented source.

No toric balance, repair progress, terminal weight or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Honest balance-free first-contact data produced below a pure X₀ top face. -/
structure PureLongitudinalBalanceFreeFirstContactData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  coefficient : K
  coefficient_ne_zero : coefficient ≠ 0
  topFace_eq :
    T.topFace.face =
      MvPolynomial.C coefficient *
        (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree
  facet : ToricFacet
  omitted_ne_zero :
    HC4.Polynomial.facetOmittedCoordinate facet ≠ (0 : Fin 4)
  scale : ℕ
  bump : ℕ
  carrier : MvPolynomial (Fin 4) K
  carrier_eq :
    carrier =
      HC4.Polynomial.initialForm
        (scaledContactWeight (HC4.Polynomial.facetOmittedCoordinate facet) scale bump)
        ((scale * T.topFace.degree : ℕ) : ℤ)
        T.representedSpecialFiber
  scale_pos : 0 < scale
  bump_pos : 0 < bump
  source_weight_bound :
    HC4.Polynomial.IsWeightLE
      (scaledContactWeight (HC4.Polynomial.facetOmittedCoordinate facet) scale bump)
      ((scale * T.topFace.degree : ℕ) : ℤ)
      T.representedSpecialFiber
  hessian_zero : HC4.Polynomial.hessianDeterminant carrier = 0
  nonlinear :
    ∀ d ∈ carrier.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d
  not_on_starting_facet :
    ¬ HC4.Polynomial.MvSupportOnFacet facet carrier
  crossFacet :
    CrossFacetInitialData carrier
      (crossFacetOppositeCoordinate (HC4.Polynomial.facetOmittedCoordinate facet))
      (HC4.Polynomial.facetOmittedCoordinate facet)
  contact :
    ∀ d ∈ carrier.support,
      scaledContactExponentWeight
        (HC4.Polynomial.facetOmittedCoordinate facet) scale bump d =
        ((scale * T.topFace.degree : ℕ) : ℤ)

/-- Exhaustive balance-free frontier for the pure longitudinal top-face case. -/
inductive PureLongitudinalFirstContactFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | firstContact
      (data : P.PureLongitudinalBalanceFreeFirstContactData)
  | quadraticSquare
      (facet : ToricFacet)
      (omitted_ne_zero :
        HC4.Polynomial.facetOmittedCoordinate facet ≠ (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (mem_source : d ∈ T.representedSpecialFiber.support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (omitted_two : d (HC4.Polynomial.facetOmittedCoordinate facet) = 2)
      (pure :
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0)

/-- The low-degree square exception is automatically a genuine
codimension-two source exponent: all coordinates other than the omitted
square coordinate vanish. -/
theorem PureLongitudinalFirstContactFrontier.quadraticSquare_codimensionTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {facet : ToricFacet}
    {d : Fin 4 →₀ ℕ}
    (homit : HC4.Polynomial.facetOmittedCoordinate facet ≠ (0 : Fin 4))
    (hpure :
      ∀ i : Fin 4,
        i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0) :
    MvExponentOnCodimensionTwoBoundary d := by
  cases facet with
  | qs =>
      exact (homit rfl).elim
  | pr =>
      refine ⟨(0 : Fin 4), (2 : Fin 4), by decide, ?_, ?_⟩
      · exact hpure 0 (by decide)
      · exact hpure 2 (by decide)
  | rq =>
      refine ⟨(0 : Fin 4), (1 : Fin 4), by decide, ?_, ?_⟩
      · exact hpure 0 (by decide)
      · exact hpure 1 (by decide)
  | sp =>
      refine ⟨(0 : Fin 4), (1 : Fin 4), by decide, ?_, ?_⟩
      · exact hpure 0 (by decide)
      · exact hpure 1 (by decide)

/-- Downstream-facing compression of the pure-longitudinal branch: either an
honest balance-free first-contact cross-facet carrier, or an actual
codimension-two quadratic source exponent. -/
inductive PureLongitudinalContactOrCodimensionTwoSource
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | firstContact
      (data : P.PureLongitudinalBalanceFreeFirstContactData)
  | codimensionTwoSource
      (d : Fin 4 →₀ ℕ)
      (mem_source : d ∈ T.representedSpecialFiber.support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (boundary : MvExponentOnCodimensionTwoBoundary d)

/-- Forget only the irrelevant identity of the square facet; retain either the
full first-contact packet or honest source codimension-two data. -/
theorem PureLongitudinalFirstContactFrontier.toContactOrCodimensionTwoSource
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (F : P.PureLongitudinalFirstContactFrontier) :
    Nonempty P.PureLongitudinalContactOrCodimensionTwoSource := by
  cases F with
  | firstContact data =>
      exact ⟨.firstContact data⟩
  | quadraticSquare facet homit d hd hdeg htwo hpure =>
      exact ⟨.codimensionTwoSource d hd hdeg
        (PureLongitudinalFirstContactFrontier.quadraticSquare_codimensionTwo P homit hpure)⟩

/-- The final seam cannot have all nonlinear represented support on X₀, hence
some nonlinear source monomial has a positive transverse coordinate. -/
theorem exists_nonlinear_transverse_source
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
        (0 < d (1 : Fin 4) ∨
          0 < d (2 : Fin 4) ∨
          0 < d (3 : Fin 4)) := by
  by_contra hnone
  push_neg at hnone
  have hconf : T.RepresentedNonlinearSupportLongitudinal := by
    intro d hd hdeg
    have h := hnone d hd hdeg
    exact ⟨by omega, by omega, by omega⟩
  exact T.impossible_of_representedNonlinearSupportLongitudinal hconf

/-- A pure longitudinal top face lies on every coordinate facet whose omitted
coordinate is transverse. -/
theorem pureLongitudinal_topFaceOnFacet
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (_coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (facet : ToricFacet)
    (homit : HC4.Polynomial.facetOmittedCoordinate facet ≠ (0 : Fin 4)) :
    HC4.Polynomial.MvSupportOnFacet facet T.topFace.face := by
  have hderiv :
      MvPolynomial.pderiv (HC4.Polynomial.facetOmittedCoordinate facet)
          T.topFace.face = 0 := by
    rw [topFace_eq, MvPolynomial.pderiv_C_mul]
    simp [homit]
  intro d hd
  rw [HC4.Polynomial.onFacet_toToricExponent_iff]
  exact exponent_eq_zero_of_pderiv_eq_zero
    (HC4.Polynomial.facetOmittedCoordinate facet) T.topFace.face hderiv d
    (MvPolynomial.mem_support_iff.mp hd)

/-- In the pure-longitudinal branch, the top monomial itself is a concrete
low layer for the determinant-closing positive-transverse Rees transform of
the marked-axis collision family.

Its transverse degree is zero and its parameter order is at most the top
degree `D`, while the marked-axis Hessian clock is `4D - 6`.  Since
`D ≥ 3`, this monomial violates the closing coefficient bound strictly.
Thus the auxiliary positive-clock family reaches the mature low-layer
interface without any balance assumption. -/
theorem pureLongitudinal_markedAxis_positiveTransverseLowLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    Nonempty
      (CanonicalPositiveTransverseReesLowLayer
        (4 * T.topFace.degree - 6)
        T.topKernelMarkedAxisFirstContactFamily) := by
  let d : Fin 4 →₀ ℕ :=
    Finsupp.single (0 : Fin 4) T.topFace.degree
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    simp [d, HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  have hdTop :
      MvPolynomial.coeff d T.topFace.face ≠ 0 := by
    rw [topFace_eq, MvPolynomial.coeff_C_mul]
    simpa [d, MvPolynomial.coeff_X_pow] using coefficient_ne_zero
  have hdSourceCoeff :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 := by
    change
      MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ≠ 0
    rw [← T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact hdTop
  have hdSource : d ∈ T.topKernelReesSource.support :=
    MvPolynomial.mem_support_iff.mpr hdSourceCoeff
  have hfamilyCoeff :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily =
        Polynomial.X ^ T.topFace.degree *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
      reverseWeightedReesFamily_coeff, if_pos hdSource,
      weight_topKernelMarkedAxisNatWeight]
    simp [d]
  have hfamilyCoeffNe :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily ≠ 0 := by
    rw [hfamilyCoeff]
    exact mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr hdSourceCoeff)
  have hdFamily :
      d ∈ T.topKernelMarkedAxisFirstContactFamily.support :=
    MvPolynomial.mem_support_iff.mpr hfamilyCoeffNe
  have hcoeffAtDegree :
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily).coeff
        T.topFace.degree ≠ 0 := by
    rw [hfamilyCoeff]
    simpa using hdSourceCoeff
  have horderLe :
      smithFamilyCoefficientOrder
          T.topKernelMarkedAxisFirstContactFamily d ≤
        T.topFace.degree := by
    rw [smithFamilyCoefficientOrder_eq
      T.topKernelMarkedAxisFirstContactFamily hdFamily]
    exact polynomialParameterOrder_le_of_coeff_ne_zero
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily)
      hfamilyCoeffNe hcoeffAtDegree
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  have hearly :
      2 * smithFamilyCoefficientOrder
            T.topKernelMarkedAxisFirstContactFamily d +
          Finsupp.weight
            (canonicalPositiveTransverseReesWeight
              (4 * T.topFace.degree - 6)) d <
        2 * (4 * T.topFace.degree - 6) := by
    rw [canonicalPositiveTransverseReesWeight_finsupp]
    have htrans : canonicalTransverseDegree d = 0 := by
      simp [canonicalTransverseDegree, d]
    rw [htrans]
    simp only [Nat.mul_zero, Nat.add_zero]
    omega
  have htransLe : canonicalTransverseDegree d ≤ 1 := by
    simp [canonicalTransverseDegree, d]
  have hpattern :
      IsPureLongitudinalSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
    simp [IsPureLongitudinalSmithPattern, smithSupportExponentOf, d]
  exact ⟨{
    exponent := d
    mem := hdFamily
    early := hearly
    transverseDegree_le_one := htransLe
    pattern := Or.inl hpattern
  }⟩

/-- The distinguished pure top monomial has exact parameter order equal to
the maximal ordinary degree in the marked-axis first-contact family.

This sharpens the preceding low-layer witness: its coefficient is literally
`X^D * C(c)` with `c ≠ 0`, so no larger parameter power divides it. -/
theorem pureLongitudinal_markedAxis_topCoefficientOrder_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    smithFamilyCoefficientOrder
        T.topKernelMarkedAxisFirstContactFamily
        (Finsupp.single (0 : Fin 4) T.topFace.degree) =
      T.topFace.degree := by
  let d : Fin 4 →₀ ℕ :=
    Finsupp.single (0 : Fin 4) T.topFace.degree
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    simp [d, HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  have hdTop :
      MvPolynomial.coeff d T.topFace.face ≠ 0 := by
    rw [topFace_eq, MvPolynomial.coeff_C_mul]
    simpa [d, MvPolynomial.coeff_X_pow] using coefficient_ne_zero
  have hdSourceCoeff :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 := by
    change
      MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ≠ 0
    rw [← T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact hdTop
  have hdSource : d ∈ T.topKernelReesSource.support :=
    MvPolynomial.mem_support_iff.mpr hdSourceCoeff
  have hfamilyCoeff :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily =
        Polynomial.X ^ T.topFace.degree *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
      reverseWeightedReesFamily_coeff, if_pos hdSource,
      weight_topKernelMarkedAxisNatWeight]
    simp [d]
  have hfamilyCoeffNe :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily ≠ 0 := by
    rw [hfamilyCoeff]
    exact mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr hdSourceCoeff)
  have hdFamily :
      d ∈ T.topKernelMarkedAxisFirstContactFamily.support :=
    MvPolynomial.mem_support_iff.mpr hfamilyCoeffNe
  have hcoeffAtDegree :
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily).coeff
        T.topFace.degree ≠ 0 := by
    rw [hfamilyCoeff]
    simpa using hdSourceCoeff
  rw [smithFamilyCoefficientOrder_eq
    T.topKernelMarkedAxisFirstContactFamily hdFamily]
  apply Nat.le_antisymm
  · exact polynomialParameterOrder_le_of_coeff_ne_zero
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily)
      hfamilyCoeffNe hcoeffAtDegree
  · apply polynomial_X_pow_dvd_le_parameterOrder
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily)
      hfamilyCoeffNe T.topFace.degree
    rw [hfamilyCoeff]
    refine ⟨Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource), ?_⟩
    rfl

/-- Consequently the distinguished pure top coefficient occurs at a genuinely
positive order strictly before the marked-axis determinant-closing clock. -/
theorem pureLongitudinal_markedAxis_topCoefficientOrder_pos_lt_defect
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    0 <
        smithFamilyCoefficientOrder
          T.topKernelMarkedAxisFirstContactFamily
          (Finsupp.single (0 : Fin 4) T.topFace.degree) ∧
      smithFamilyCoefficientOrder
          T.topKernelMarkedAxisFirstContactFamily
          (Finsupp.single (0 : Fin 4) T.topFace.degree) <
        4 * T.topFace.degree - 6 := by
  rw [P.pureLongitudinal_markedAxis_topCoefficientOrder_eq
    coefficient_ne_zero topFace_eq]
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  omega

/-- In the pure-longitudinal branch the marked-axis associated graded is
literally zero.  The marked fibre only retains top-face exponents with
coordinate `0` equal to zero, whereas the pure `X₀^D` top face has no such
nonzero exponent for `D ≥ 3`. -/
theorem pureLongitudinal_markedAxis_specialFiber_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily = 0 := by
  apply MvPolynomial.ext
  intro d
  have hnot :
      d ∉ (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support := by
    intro hd
    have hslice :=
      (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
        d).1 hd
    have hpr :
        HC4.Polynomial.MvSupportOnFacet .pr T.topFace.face :=
      P.pureLongitudinal_topFaceOnFacet
        coefficient_ne_zero topFace_eq .pr (by decide)
    have hsp :
        HC4.Polynomial.MvSupportOnFacet .sp T.topFace.face :=
      P.pureLongitudinal_topFaceOnFacet
        coefficient_ne_zero topFace_eq .sp (by decide)
    have hrq :
        HC4.Polynomial.MvSupportOnFacet .rq T.topFace.face :=
      P.pureLongitudinal_topFaceOnFacet
        coefficient_ne_zero topFace_eq .rq (by decide)
    have h1 : d (1 : Fin 4) = 0 := by
      have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .pr d).1 (hpr d hslice.1)
      simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
    have h2 : d (2 : Fin 4) = 0 := by
      have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .sp d).1 (hsp d hslice.1)
      simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
    have h3 : d (3 : Fin 4) = 0 := by
      have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .rq d).1 (hrq d hslice.1)
      simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
    have hdeg :=
      T.topFace.face_support_ordinaryDegree_eq hslice.1
    have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
    simp [HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four,
      hslice.2, h1, h2, h3] at hdeg
    omega
  rw [MvPolynomial.notMem_support_iff.mp hnot]
  simp

/-- The zero marked fibre sharpens first-layer causality from `q ≤ Delta` to
`4q ≤ Delta`.  Since the marked-axis clock is `4D-6`, its first positive
actual layer occurs at least two orders before the pure top coefficient. -/
theorem pureLongitudinal_markedAxis_firstActualLayerOrder_le_degree_sub_two
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    T.topKernelMarkedAxisFirstActualLayerOrder ≤ T.topFace.degree - 2 := by
  have hspecial :=
    P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq
  have hfour :=
    four_mul_firstPositiveActualParameterOrder_le_hessianDefect_of_specialFiber_zero
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
      hspecial
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  have hfour' :
      4 * T.topKernelMarkedAxisFirstActualLayerOrder ≤
        4 * T.topFace.degree - 6 := by
    simpa [topKernelMarkedAxisFirstActualLayerOrder] using hfour
  omega

/-- In particular the first actual marked-axis source layer is strictly
earlier than the distinguished pure `X₀^D` coefficient, whose exact order is
`D`. -/
theorem pureLongitudinal_markedAxis_firstActualLayerOrder_lt_topCoefficientOrder
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    T.topKernelMarkedAxisFirstActualLayerOrder <
      smithFamilyCoefficientOrder
        T.topKernelMarkedAxisFirstContactFamily
        (Finsupp.single (0 : Fin 4) T.topFace.degree) := by
  rw [P.pureLongitudinal_markedAxis_topCoefficientOrder_eq
    coefficient_ne_zero topFace_eq]
  have hle :=
    P.pureLongitudinal_markedAxis_firstActualLayerOrder_le_degree_sub_two
      coefficient_ne_zero topFace_eq
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  omega

/-- Minimality of the first actual marked-axis layer improves the original
marked-axis reverse-weight bound from level `D` to level `D-q`.  Every
represented-source monomial occurs in the reverse-Rees family at parameter
order `D - wt(d)`; the zero special fibre makes that order positive, and the
least-positive-layer property forces it to be at least `q`. -/
theorem pureLongitudinal_markedAxis_firstActual_sourceWeightBound
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    HasReverseWeightBound
      topKernelMarkedAxisNatWeight
      (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder)
      T.topKernelReesSource := by
  intro d hd
  let q := T.topKernelMarkedAxisFirstActualLayerOrder
  let n := T.topFace.degree -
    Finsupp.weight topKernelMarkedAxisNatWeight d
  have hsourceCoeff :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hboundD :
      Finsupp.weight topKernelMarkedAxisNatWeight d ≤
        T.topFace.degree :=
    T.topKernelReesSource_hasMarkedAxisReverseWeightBound d hd
  have hfamilyCoeff :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily =
        Polynomial.X ^ n *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
      reverseWeightedReesFamily_coeff, if_pos hd]
  have hcoeffn :
      (MvPolynomial.coeff d
        T.topKernelMarkedAxisFirstContactFamily).coeff n ≠ 0 := by
    rw [hfamilyCoeff]
    simpa [n] using hsourceCoeff
  have hspecial :=
    P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq
  have hdiv :
      Polynomial.X ^ q ∣
        MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily := by
    simpa [q, topKernelMarkedAxisFirstActualLayerOrder] using
      sourceCoefficient_X_pow_firstPositiveActualOrder_dvd_of_specialFiber_zero
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
        hspecial d
  rw [Polynomial.X_pow_dvd_iff] at hdiv
  have hqle : q ≤ n := by
    by_contra hnot
    exact hcoeffn (hdiv n (Nat.lt_of_not_ge hnot))
  dsimp [q, n] at hqle ⊢
  omega

/-- The first actual marked-axis layer is therefore an exact lower
transverse-weight initial form of the represented determinant-one source. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder =
      HC4.Polynomial.initialForm
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
        ((T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder : ℕ) : ℤ)
        T.topKernelReesSource := by
  have hlayer :
      familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0 :=
    firstPositiveActualParameterLayer_ne_zero
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees] at hlayer ⊢
  exact
    (reverseWeightedReesFamily_parameterLayer_eq_initialForm_of_ne_zero
      topKernelMarkedAxisNatWeight T.topFace.degree
      T.topKernelMarkedAxisFirstActualLayerOrder T.topKernelReesSource
      T.topKernelReesSource_hasMarkedAxisReverseWeightBound hlayer).2

/-- The complementary transverse degree of that first actual layer is
nontrivial and strictly smaller than the original pure top degree. -/
theorem pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    2 ≤ T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder ∧
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder <
        T.topFace.degree := by
  have hqle :=
    P.pureLongitudinal_markedAxis_firstActualLayerOrder_le_degree_sub_two
      coefficient_ne_zero topFace_eq
  have hqpos := T.topKernelMarkedAxisFirstActualLayerOrder_pos
  have hD := T.topFace.degree_ge_three
  omega


/-- Every monomial on the first actual marked-axis layer has ordinary degree
strictly below the original maximal top degree.

Indeed the layer is an exact transverse-weight face of the represented source.
A monomial of ordinary degree `D` would therefore lie on the original pure
top face `c * X₀^D`, forcing all transverse exponents to vanish.  But every
monomial on the lower face has positive transverse degree `D - q ≥ 2`. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_ordinaryDegree_lt_topFace
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    ∀ d ∈ (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder).support,
      HC4.Polynomial.ordinaryDegree4 d < T.topFace.degree := by
  intro d hd
  let r :=
    T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  have hfaceEq :=
    P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      coefficient_ne_zero topFace_eq
  have hdInit := hd
  rw [hfaceEq] at hdInit
  have hdSource :
      d ∈ T.representedSpecialFiber.support := by
    exact HC4.Polynomial.support_initialForm_subset
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (r : ℤ) T.representedSpecialFiber
      (by simpa [r] using hdInit)
  have hle : HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
    by_cases hthree : 3 ≤ HC4.Polynomial.ordinaryDegree4 d
    · have hbound :
          NonlinearDegreeBound T.topFace.degree T.representedSpecialFiber :=
        T.representedSpecialFiber_nonlinearDegreeBound_topFace
      exact hbound d hdSource hthree
    · have hD := T.topFace.degree_ge_three
      omega
  by_contra hnot
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    omega
  have hdTop : d ∈ T.topFace.face.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact MvPolynomial.mem_support_iff.mp hdSource
  have hpr :
      HC4.Polynomial.MvSupportOnFacet .pr T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      coefficient_ne_zero topFace_eq .pr (by decide)
  have hsp :
      HC4.Polynomial.MvSupportOnFacet .sp T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      coefficient_ne_zero topFace_eq .sp (by decide)
  have hrq :
      HC4.Polynomial.MvSupportOnFacet .rq T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      coefficient_ne_zero topFace_eq .rq (by decide)
  have h1 : d (1 : Fin 4) = 0 := by
    have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .pr d).1 (hpr d hdTop)
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
  have h2 : d (2 : Fin 4) = 0 := by
    have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .sp d).1 (hsp d hdTop)
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
  have h3 : d (3 : Fin 4) = 0 := by
    have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .rq d).1 (hrq d hdTop)
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hdInit
  rw [HC4.Polynomial.coeff_initialForm] at hcoeff
  have hweight :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
        (r : ℤ) := by
    by_contra hne
    simp [hne, r] at hcoeff
  rw [weight_topKernelMarkedAxisIntWeight] at hweight
  have htrans :
      d 1 + d 2 + d 3 = r := by
    exact_mod_cast hweight
  rcases
      P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq with
    ⟨hrtwo, _hrlt⟩
  dsimp [r] at htrans hrtwo
  rw [h1, h2, h3] at htrans
  omega

/-- The lower transverse face therefore carries a strict ordinary nonlinear
degree cap as well. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_nonlinearDegreeBound
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    NonlinearDegreeBound
      (T.topFace.degree - 1)
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder) := by
  intro d hd hthree
  have hlt :=
    P.pureLongitudinal_markedAxis_firstActualLayer_ordinaryDegree_lt_topFace
      coefficient_ne_zero topFace_eq d hd
  omega

/-- Every monomial on the first actual marked-axis layer has the exact
transverse degree `D-q`. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_exactTransverseDegree
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    ∀ d ∈ (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder).support,
      d 1 + d 2 + d 3 =
        T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder := by
  intro d hd
  have hfaceEq :=
    P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      coefficient_ne_zero topFace_eq
  have hdInit := hd
  rw [hfaceEq] at hdInit
  have hcoeff := MvPolynomial.mem_support_iff.mp hdInit
  rw [HC4.Polynomial.coeff_initialForm] at hcoeff
  have hweight :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
        ((T.topFace.degree -
          T.topKernelMarkedAxisFirstActualLayerOrder : ℕ) : ℤ) := by
    by_contra hne
    simp [hne] at hcoeff
  rw [weight_topKernelMarkedAxisIntWeight] at hweight
  exact_mod_cast hweight

/-- If the first canonical kernel opening of the nonlinear lower face opens
the longitudinal coordinate, then the child is genuinely ordinary-homogeneous
of the lower transverse degree.  This uses only support provenance and the
literal child kernel. -/
theorem pureLongitudinal_lowerFirstOpening_child_isHomogeneous_of_kernel_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (D : CanonicalCoordinateMaxKernelOpeningData
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder))
    (hk : D.kernelCoordinate = (0 : Fin 4)) :
    D.child.IsHomogeneous
      (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder) := by
  intro d hdcoeff
  have hd : d ∈ D.child.support :=
    MvPolynomial.mem_support_iff.mpr hdcoeff
  have hdLower :
      d ∈ (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder).support :=
    D.child_support_subset_source hd
  have htrans :=
    P.pureLongitudinal_markedAxis_firstActualLayer_exactTransverseDegree
      coefficient_ne_zero topFace_eq d hdLower
  have hkernel0 :
      MvPolynomial.pderiv (0 : Fin 4) D.child = 0 := by
    simpa [hk] using D.child_kernel
  have h0 : d (0 : Fin 4) = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      (0 : Fin 4) D.child hkernel0 d hdcoeff
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [h0]
    exact htrans
  · intro i
    simp

/-- Longitudinal first kernel opening on the pure lower face is therefore
already in the mature homogeneous rank-two/linear-power dichotomy. -/
theorem pureLongitudinal_lowerFirstOpening_rankTwo_or_linearPower_of_kernel_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (D : CanonicalCoordinateMaxKernelOpeningData
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder))
    (hk : D.kernelCoordinate = (0 : Fin 4)) :
    D.ChildHessianRankTwoWitness ∨
      Nonempty
        (D.ChildLinearPowerData
          (T.topFace.degree -
            T.topKernelMarkedAxisFirstActualLayerOrder)) := by
  rcases D.childHessian_rankTwoWitness_or_rankAtMostOne with htwo | hall
  · exact Or.inl htwo
  · right
    have hhom :=
      P.pureLongitudinal_lowerFirstOpening_child_isHomogeneous_of_kernel_zero
        coefficient_ne_zero topFace_eq D hk
    have hm :
        2 ≤ T.topFace.degree -
          T.topKernelMarkedAxisFirstActualLayerOrder :=
      (P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq).1
    rcases rankOneHomogeneousLogGradientData_of_allMinors
        D.child
        (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder)
        hhom D.child_ne_zero hm hall with
      ⟨L⟩
    rcases rankOneHomogeneousLogGradientData_four_global L with
      ⟨ratio, hratio⟩
    rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
        (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder)
        D.child hhom (by omega)
        L.pivot L.pivot_ne_zero ratio hratio with
      ⟨a, ha⟩
    exact ⟨{
      coefficient := a
      ratio := ratio
      eq_power := ha
    }⟩

/-- Lossless nonlinear lower-face packet.  Unlike the older boundary frontier,
this record retains the exact hypotheses used to construct the canonical
exposed singular boundary vertex, so a codimension-two outcome can immediately
recover the canonical carrier kernel. -/
structure PureLongitudinalMarkedAxisLowerNonlinearData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  level_ge_three :
    3 ≤ T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  face_ne :
    familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0
  hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder) = 0
  support_degree_ge_three :
    ∀ d ∈ (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d


/-- A longitudinal first kernel-opening step on a nonlinear lower face is
already completely rank-two resolved: either the child itself has a nonzero
Hessian `2 x 2` minor, or its homogeneous linear-power alternative opens to
rank-two geometry at the canonical first kernel-row break. -/
theorem pureLongitudinal_lowerFirstOpening_longitudinal_rankTwoResolved
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
    (D : CanonicalCoordinateMaxKernelOpeningData
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder))
    (hk : D.kernelCoordinate = (0 : Fin 4)) :
    D.ChildHessianRankTwoWitness ∨
      ∃ LP :
          D.ChildLinearPowerData
            (T.topFace.degree -
              T.topKernelMarkedAxisFirstActualLayerOrder),
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        let hrow := D.kernelLastBlock_kernelRow_ne_zero
          N.support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j := by
  rcases
      P.pureLongitudinal_lowerFirstOpening_rankTwo_or_linearPower_of_kernel_zero
        coefficient_ne_zero topFace_eq D hk with
    htwo | hpower
  · exact Or.inl htwo
  · rcases hpower with ⟨LP⟩
    right
    refine ⟨LP, ?_⟩
    exact
      CanonicalCoordinateMaxKernelOpeningData.ChildLinearPowerData.firstBreakRankTwoOutcome
        D LP N.level_ge_three N.support_degree_ge_three

/-- The first actual lower transverse face is Hessian-singular.  The improved
`D-q` reverse-weight bound makes it a genuine maximal initial form of the
represented determinant-one source, and `D-q ≥ 2` makes the induced Hessian
weight strictly positive. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_hessian_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    HC4.Polynomial.hessianDeterminant
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder) = 0 := by
  rw [P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
    coefficient_ne_zero topFace_eq]
  apply HC4.MongeAmpere.maximal_initial_hessianDeterminant_eq_zero
  · intro d hd
    have hnat :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq d hd
    rw [weight_topKernelMarkedAxisIntWeight]
    rw [weight_topKernelMarkedAxisNatWeight] at hnat
    exact_mod_cast hnat
  · unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    exact T.topKernelReesSource_hessianDeterminant_eq_one
  · rcases
      P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq with
      ⟨hrtwo, _hrlt⟩
    have hrtwoZ :
        (2 : ℤ) ≤
          (T.topFace.degree -
            T.topKernelMarkedAxisFirstActualLayerOrder : ℕ) := by
      exact_mod_cast hrtwo
    rw [Fin.sum_univ_four]
    simp [topKernelMarkedAxisNatWeight]
    omega

/-- Finite frontier for the first nonzero lower transverse face forced by
the pure-longitudinal branch.  The only low-degree exception is transverse
degree two; at degree at least three the existing finite singular-support
theorem produces an honest exposed nonlinear boundary vertex. -/
inductive PureLongitudinalMarkedAxisLowerFaceFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | quadratic
      (level_eq_two :
        T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2)
  | nonlinearBoundary
      (level_ge_three :
        3 ≤ T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder)
      (vertex :
        ExposedSingularNonlinearBoundaryVertexData
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder))

/-- The pure-longitudinal branch reaches the finite lower-face frontier above:
either a concrete transverse quadratic layer, or an honest nonlinear singular
boundary vertex at strictly smaller transverse degree. -/
theorem pureLongitudinal_markedAxis_lowerFaceFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    Nonempty P.PureLongitudinalMarkedAxisLowerFaceFrontier := by
  let r :=
    T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  rcases
      P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq with
    ⟨hrtwo, _hrlt⟩
  by_cases hr : r = 2
  · exact ⟨.quadratic (by simpa [r] using hr)⟩
  · have hrthree : 3 ≤ r := by omega
    have hfaceNe :
        familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0 :=
      firstPositiveActualParameterLayer_ne_zero
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    have hzero :=
      P.pureLongitudinal_markedAxis_firstActualLayer_hessian_zero
        coefficient_ne_zero topFace_eq
    have hnonlinear :
        ∀ d ∈ (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder).support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
      intro d hd
      have hfaceEq :=
        P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
          coefficient_ne_zero topFace_eq
      have hdInit := hd
      rw [hfaceEq] at hdInit
      have hcoeff := MvPolynomial.mem_support_iff.mp hdInit
      rw [HC4.Polynomial.coeff_initialForm] at hcoeff
      have hweight :
          Finsupp.weight
              (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
            (r : ℤ) := by
        by_contra hne
        simp [hne, r] at hcoeff
      rw [weight_topKernelMarkedAxisIntWeight] at hweight
      have htrans :
          d 1 + d 2 + d 3 = r := by
        exact_mod_cast hweight
      simp only [HC4.Polynomial.ordinaryDegree4]
      omega
    exact ⟨.nonlinearBoundary
      (by simpa [r] using hrthree)
      (exposedSingularNonlinearBoundaryVertex
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder)
        hfaceNe hzero hnonlinear)⟩

/-- At nonlinear lower transverse degree, every supported first-actual-layer
monomial is genuinely nonlinear in ordinary degree as well.  This is the
source-facing form needed by the canonical singular-boundary carrier. -/
theorem pureLongitudinal_markedAxis_firstActualLayer_support_degree_ge_three
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (hrthree :
      3 ≤ T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder) :
    ∀ d ∈ (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
  intro d hd
  let r :=
    T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  have hfaceEq :=
    P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      coefficient_ne_zero topFace_eq
  have hdInit := hd
  rw [hfaceEq] at hdInit
  have hcoeff := MvPolynomial.mem_support_iff.mp hdInit
  rw [HC4.Polynomial.coeff_initialForm] at hcoeff
  have hweight :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
        (r : ℤ) := by
    by_contra hne
    simp [hne, r] at hcoeff
  rw [weight_topKernelMarkedAxisIntWeight] at hweight
  have htrans :
      d 1 + d 2 + d 3 = r := by
    exact_mod_cast hweight
  simp only [HC4.Polynomial.ordinaryDegree4]
  dsimp [r] at htrans hrthree
  omega

/-- Canonical exposed boundary vertex attached to the retained nonlinear lower
face. -/
noncomputable def PureLongitudinalMarkedAxisLowerNonlinearData.vertex
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (N : P.PureLongitudinalMarkedAxisLowerNonlinearData) :
    ExposedSingularNonlinearBoundaryVertexData
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder) :=
  exposedSingularNonlinearBoundaryVertex
    (familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder)
    N.face_ne N.hessian_zero N.support_degree_ge_three

/-- Strengthened pure-longitudinal lower-face frontier.

The quadratic lower face is retained explicitly.  At nonlinear degree, the
canonical exposed boundary vertex is either rank three on one coordinate
facet, or codimension two; in the latter case the canonical coordinate-max
construction retains either a kernel on the whole lower face or the first
exact coordinate-max opening where that kernel appears. -/
inductive PureLongitudinalMarkedAxisLowerBoundaryFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | quadratic
      (level_eq_two :
        T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2)
  | rankThree
      (data : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (facet : ToricFacet)
      (rankThree : MvRankThreeOnFacet facet data.vertex.exponent)
  | kernelOpening
      (data : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (outcome :
        CanonicalCodimensionTwoKernelOutcome
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder))

/-- **Pure-longitudinal lower-face rank/kernel compression.**

The first actual marked-axis source layer is either transverse quadratic, or
its genuinely nonlinear singular boundary geometry already reaches a
rank-three facet or the canonical top-kernel/first-opening packet.  No balance relation,
terminal cocharacter, or repair progress is used. -/
theorem pureLongitudinal_markedAxis_lowerBoundaryFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    Nonempty P.PureLongitudinalMarkedAxisLowerBoundaryFrontier := by
  let r :=
    T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  rcases
      P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq with
    ⟨hrtwo, _hrlt⟩
  by_cases hr : r = 2
  · exact ⟨.quadratic (by simpa [r] using hr)⟩
  · have hrthree : 3 ≤ r := by omega
    have hfaceNe :
        familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0 :=
      firstPositiveActualParameterLayer_ne_zero
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    have hzero :=
      P.pureLongitudinal_markedAxis_firstActualLayer_hessian_zero
        coefficient_ne_zero topFace_eq
    have hnonlinear :=
      P.pureLongitudinal_markedAxis_firstActualLayer_support_degree_ge_three
        coefficient_ne_zero topFace_eq (by simpa [r] using hrthree)
    let N : P.PureLongitudinalMarkedAxisLowerNonlinearData := {
      level_ge_three := by simpa [r] using hrthree
      face_ne := hfaceNe
      hessian_zero := hzero
      support_degree_ge_three := hnonlinear
    }
    have hsplit :
        (∃ facet : ToricFacet, MvRankThreeOnFacet facet N.vertex.exponent) ∨
          MvExponentOnCodimensionTwoBoundary N.vertex.exponent :=
      mvBoundary_rankThreeFacet_or_codimensionTwo N.vertex.exponent_boundary
    rcases hsplit with hthree | hcodim
    · rcases hthree with ⟨facet, hfacet⟩
      exact ⟨.rankThree N facet hfacet⟩
    · have houtcome :=
        exposedSingularNonlinearBoundaryVertex_codimensionTwoKernelOutcome
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder)
          N.face_ne N.hessian_zero N.support_degree_ge_three
          (by
            simpa [PureLongitudinalMarkedAxisLowerNonlinearData.vertex]
              using hcodim)
      exact ⟨.kernelOpening N houtcome⟩

/-- The actual maximal ordinary degree is attained in the represented source. -/
theorem topFace_degree_attained_in_source
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
  rcases MvPolynomial.support_nonempty.mpr T.topFace.face_ne_zero with
    ⟨d, hdFace⟩
  have hdeg := T.topFace.ordinaryDegree_eq_of_mem_support hdFace
  have hdSource : d ∈ T.representedSpecialFiber.support := by
    have hdInit := hdFace
    rw [T.topFace.face_eq] at hdInit
    exact
      HC4.Polynomial.support_initialForm_subset
        (fun _ : Fin 4 => (1 : ℤ))
        (T.topFace.degree : ℤ)
        T.representedSpecialFiber hdInit
  exact ⟨d, hdSource, hdeg⟩

/-- The near endpoint of the balance-free first-contact carrier is not a
new lower-degree point.  Because its bumped coordinate vanishes, the exact
contact equation forces it back to maximal ordinary degree.  The retained pure
longitudinal top-face equality then makes it an honest represented-source
codimension-two exponent. -/
theorem PureLongitudinalBalanceFreeFirstContactData.near_sourceCodimensionTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalBalanceFreeFirstContactData) :
    D.crossFacet.facetExponent ∈ T.representedSpecialFiber.support ∧
      HC4.Polynomial.ordinaryDegree4 D.crossFacet.facetExponent = T.topFace.degree ∧
      MvExponentOnCodimensionTwoBoundary D.crossFacet.facetExponent := by
  let d : Fin 4 →₀ ℕ := D.crossFacet.facetExponent
  have hdCarrier : d ∈ D.carrier.support := by
    simpa [d] using D.crossFacet.facet_mem
  have hdSource : d ∈ T.representedSpecialFiber.support := by
    have h := hdCarrier
    rw [D.carrier_eq] at h
    exact HC4.Polynomial.support_initialForm_subset
      (scaledContactWeight (HC4.Polynomial.facetOmittedCoordinate D.facet) D.scale D.bump)
      ((D.scale * T.topFace.degree : ℕ) : ℤ)
      T.representedSpecialFiber h
  have hcontact := D.contact d hdCarrier
  have hcoord :
      d (HC4.Polynomial.facetOmittedCoordinate D.facet) = 0 := by
    simpa [d] using D.crossFacet.facet_coordinate_zero
  unfold scaledContactExponentWeight at hcontact
  rw [hcoord] at hcontact
  simp only [Nat.cast_zero, mul_zero, add_zero] at hcontact
  push_cast at hcontact
  have hscaleZ : (0 : ℤ) < D.scale := by
    exact_mod_cast D.scale_pos
  have hdegZ :
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) = (T.topFace.degree : ℤ) := by
    nlinarith
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    exact_mod_cast hdegZ
  have hdTop : d ∈ T.topFace.face.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact MvPolynomial.mem_support_iff.mp hdSource
  have hpr :
      HC4.Polynomial.MvSupportOnFacet .pr T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      D.coefficient_ne_zero D.topFace_eq .pr (by decide)
  have hsp :
      HC4.Polynomial.MvSupportOnFacet .sp T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      D.coefficient_ne_zero D.topFace_eq .sp (by decide)
  have h1 : d (1 : Fin 4) = 0 := by
    have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .pr d).1 (hpr d hdTop)
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
  have h2 : d (2 : Fin 4) = 0 := by
    have hz := (HC4.Polynomial.onFacet_toToricExponent_iff .sp d).1 (hsp d hdTop)
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hz
  refine ⟨?_, ?_, ?_⟩
  · simpa [d] using hdSource
  · simpa [d] using hdeg
  · simpa [d] using
      (show MvExponentOnCodimensionTwoBoundary d from
        ⟨(1 : Fin 4), (2 : Fin 4), by decide, h1, h2⟩)

/-- Source-only compression of the pure-longitudinal branch.  At this stage
the degree provenance is no longer needed: both the honest first-contact near
endpoint and the low-degree square are literal represented-source exponents on
two coordinate boundaries. -/
structure PureLongitudinalCodimensionTwoSourceData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  exponent : Fin 4 →₀ ℕ
  mem_source : exponent ∈ T.representedSpecialFiber.support
  boundary : MvExponentOnCodimensionTwoBoundary exponent

/-- Every pure-longitudinal first-contact frontier already contains honest
represented-source codimension-two data.  In the first-contact branch the
near endpoint is forced back to the pure top face; in the square branch this
is the literal omitted-coordinate square. -/
theorem PureLongitudinalFirstContactFrontier.toCodimensionTwoSourceData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (F : P.PureLongitudinalFirstContactFrontier) :
    Nonempty P.PureLongitudinalCodimensionTwoSourceData := by
  cases F with
  | firstContact data =>
      rcases data.near_sourceCodimensionTwo P with ⟨hd, _hdeg, hboundary⟩
      exact ⟨{
        exponent := data.crossFacet.facetExponent
        mem_source := hd
        boundary := hboundary
      }⟩
  | quadraticSquare facet homit d hd _hdeg _htwo hpure =>
      exact ⟨{
        exponent := d
        mem_source := hd
        boundary := PureLongitudinalFirstContactFrontier.quadraticSquare_codimensionTwo P homit hpure
      }⟩


/-- Run the balance-free first-contact selector on one transverse facet. -/
private theorem pureLongitudinal_firstContact_or_square_at_facet
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (facet : ToricFacet)
    (homit : HC4.Polynomial.facetOmittedCoordinate facet ≠ (0 : Fin 4))
    (dstar : Fin 4 →₀ ℕ)
    (hdstar : dstar ∈ T.representedSpecialFiber.support)
    (hdstarDeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 dstar)
    (hdstarPos : 0 < dstar (HC4.Polynomial.facetOmittedCoordinate facet)) :
    Nonempty P.PureLongitudinalFirstContactFrontier := by
  have htopFace :
      HC4.Polynomial.MvSupportOnFacet facet T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      coefficient_ne_zero topFace_eq facet homit
  have htop :
      TopDegreeOnFacet facet T.topFace.degree T.representedSpecialFiber :=
    T.topFaceOnFacet_topDegreeOnFacet facet htopFace
  have hdeg :
      NonlinearDegreeBound T.topFace.degree T.representedSpecialFiber :=
    T.representedSpecialFiber_nonlinearDegreeBound_topFace
  have hout :
      HasNonlinearOutsideFacet facet T.representedSpecialFiber := by
    refine ⟨dstar, hdstar, hdstarDeg, ?_⟩
    intro hfacet
    have hz :=
      (HC4.Polynomial.onFacet_toToricExponent_iff facet dstar).1 hfacet
    exact (Nat.ne_of_gt hdstarPos) hz
  have hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        T.representedSpecialFiber :=
    T.representedSpecialFiber_isPolynomialMongeAmpere
  have hattained :
      ∃ d ∈ T.representedSpecialFiber.support,
        HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree :=
    topFace_degree_attained_in_source T

  rcases lowDegreeTame_or_exists_omittedQuadraticSquare
      facet T.representedSpecialFiber with htame | hsquare
  · rcases exists_singular_first_nonfacet_contact_with_nonlinear_support_and_weightBound
        T.topFace.degree_ge_three hdeg htop hout htame hMA with
      ⟨d₀, scale, bump, G, hG, hd₀G, hd₀deg, hd₀pos,
        hscale, hbump, hbound, hzero, hnot, hnonlinear⟩
    have hsupp :=
      firstContactCarrier_crossFacet_supports
        htop hattained hG hnot
    let D : CrossFacetInitialData G
        (crossFacetOppositeCoordinate (HC4.Polynomial.facetOmittedCoordinate facet))
        (HC4.Polynomial.facetOmittedCoordinate facet) :=
      crossFacetInitialData hsupp.1 hsupp.2.1
    refine ⟨.firstContact {
      coefficient := coefficient
      coefficient_ne_zero := coefficient_ne_zero
      topFace_eq := topFace_eq
      facet := facet
      omitted_ne_zero := homit
      scale := scale
      bump := bump
      carrier := G
      carrier_eq := hG
      scale_pos := hscale
      bump_pos := hbump
      source_weight_bound := hbound
      hessian_zero := hzero
      nonlinear := hnonlinear
      not_on_starting_facet := hnot
      crossFacet := D
      contact := ?_
    }⟩
    exact hsupp.2.2
  · rcases hsquare with ⟨d, hd, hdeg2, htwo, hpure⟩
    exact ⟨.quadraticSquare facet homit d hd hdeg2 htwo hpure⟩

/-- **Pure-longitudinal E2 branch -> honest first contact or literal square.**

G8 supplies a lower nonlinear transverse escape.  Choosing the corresponding
coordinate facet, which automatically contains the pure X₀ maximal face,
gives the balance-free first-contact reduction above. -/
theorem pureLongitudinalFirstContactFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    Nonempty P.PureLongitudinalFirstContactFrontier := by
  rcases exists_nonlinear_transverse_source T with
    ⟨d, hd, hdeg, h1 | h2 | h3⟩
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .pr (by decide)
      d hd hdeg (by simpa [HC4.Polynomial.facetOmittedCoordinate] using h1)
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .sp (by decide)
      d hd hdeg (by simpa [HC4.Polynomial.facetOmittedCoordinate] using h2)
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .rq (by decide)
      d hd hdeg (by simpa [HC4.Polynomial.facetOmittedCoordinate] using h3)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
