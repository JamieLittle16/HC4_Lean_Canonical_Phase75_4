import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerE2Frontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamLongitudinalConfinement
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
    facetOmittedCoordinate facet ≠ (0 : Fin 4)
  scale : ℕ
  bump : ℕ
  carrier : MvPolynomial (Fin 4) K
  carrier_eq :
    carrier =
      initialForm
        (scaledContactWeight (facetOmittedCoordinate facet) scale bump)
        ((scale * T.topFace.degree : ℕ) : ℤ)
        T.representedSpecialFiber
  scale_pos : 0 < scale
  bump_pos : 0 < bump
  source_weight_bound :
    IsWeightLE
      (scaledContactWeight (facetOmittedCoordinate facet) scale bump)
      ((scale * T.topFace.degree : ℕ) : ℤ)
      T.representedSpecialFiber
  hessian_zero : hessianDeterminant carrier = 0
  nonlinear :
    ∀ d ∈ carrier.support, 3 ≤ ordinaryDegree4 d
  not_on_starting_facet :
    ¬ MvSupportOnFacet facet carrier
  crossFacet :
    CrossFacetInitialData carrier
      (crossFacetOppositeCoordinate (facetOmittedCoordinate facet))
      (facetOmittedCoordinate facet)
  contact :
    ∀ d ∈ carrier.support,
      scaledContactExponentWeight
        (facetOmittedCoordinate facet) scale bump d =
        ((scale * T.topFace.degree : ℕ) : ℤ)

/-- Exhaustive balance-free frontier for the pure longitudinal top-face case. -/
inductive PureLongitudinalFirstContactFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | firstContact
      (data : P.PureLongitudinalBalanceFreeFirstContactData)
  | quadraticSquare
      (facet : ToricFacet)
      (omitted_ne_zero :
        facetOmittedCoordinate facet ≠ (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (mem_source : d ∈ T.representedSpecialFiber.support)
      (degree_two : ordinaryDegree4 d = 2)
      (omitted_two : d (facetOmittedCoordinate facet) = 2)
      (pure :
        ∀ i : Fin 4,
          i ≠ facetOmittedCoordinate facet → d i = 0)

/-- The low-degree square exception is automatically a genuine
codimension-two source exponent: all coordinates other than the omitted
square coordinate vanish. -/
theorem PureLongitudinalFirstContactFrontier.quadraticSquare_codimensionTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {facet : ToricFacet}
    {d : Fin 4 →₀ ℕ}
    (homit : facetOmittedCoordinate facet ≠ (0 : Fin 4))
    (hpure :
      ∀ i : Fin 4,
        i ≠ facetOmittedCoordinate facet → d i = 0) :
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
      (degree_two : ordinaryDegree4 d = 2)
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
        (F.quadraticSquare_codimensionTwo P homit hpure)⟩

/-- The final seam cannot have all nonlinear represented support on X₀, hence
some nonlinear source monomial has a positive transverse coordinate. -/
theorem exists_nonlinear_transverse_source
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      3 ≤ ordinaryDegree4 d ∧
        (0 < d (1 : Fin 4) ∨
          0 < d (2 : Fin 4) ∨
          0 < d (3 : Fin 4)) := by
  by_contra hnone
  push_neg at hnone
  have hconf : T.RepresentedNonlinearSupportLongitudinal := by
    intro d hd hdeg
    have h := hnone d hd hdeg
    exact ⟨Nat.eq_zero_of_not_pos h.1,
      Nat.eq_zero_of_not_pos h.2.1,
      Nat.eq_zero_of_not_pos h.2.2⟩
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
    (homit : facetOmittedCoordinate facet ≠ (0 : Fin 4)) :
    MvSupportOnFacet facet T.topFace.face := by
  have hderiv :
      MvPolynomial.pderiv (facetOmittedCoordinate facet)
          T.topFace.face = 0 := by
    rw [topFace_eq, MvPolynomial.pderiv_C_mul]
    simp [homit]
  intro d hd
  rw [onFacet_toToricExponent_iff]
  exact exponent_eq_zero_of_pderiv_eq_zero
    (facetOmittedCoordinate facet) T.topFace.face hderiv d
    (MvPolynomial.mem_support_iff.mp hd)

/-- The actual maximal ordinary degree is attained in the represented source. -/
theorem topFace_degree_attained_in_source
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ∃ d ∈ T.representedSpecialFiber.support,
      ordinaryDegree4 d = T.topFace.degree := by
  rcases MvPolynomial.support_nonempty.mpr T.topFace.face_ne_zero with
    ⟨d, hdFace⟩
  have hdeg := T.topFace.ordinaryDegree_eq_of_mem_support hdFace
  have hdSource : d ∈ T.representedSpecialFiber.support := by
    have hdInit := hdFace
    rw [T.topFace.face_eq] at hdInit
    exact
      support_initialForm_subset
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
      ordinaryDegree4 D.crossFacet.facetExponent = T.topFace.degree ∧
      MvExponentOnCodimensionTwoBoundary D.crossFacet.facetExponent := by
  let d : Fin 4 →₀ ℕ := D.crossFacet.facetExponent
  have hdCarrier : d ∈ D.carrier.support := by
    simpa [d] using D.crossFacet.facet_mem
  have hdSource : d ∈ T.representedSpecialFiber.support := by
    have h := hdCarrier
    rw [D.carrier_eq] at h
    exact support_initialForm_subset
      (scaledContactWeight (facetOmittedCoordinate D.facet) D.scale D.bump)
      ((D.scale * T.topFace.degree : ℕ) : ℤ)
      T.representedSpecialFiber h
  have hcontact := D.contact d hdCarrier
  have hcoord :
      d (facetOmittedCoordinate D.facet) = 0 := by
    simpa [d] using D.crossFacet.facet_coordinate_zero
  unfold scaledContactExponentWeight at hcontact
  rw [hcoord] at hcontact
  simp only [Nat.cast_zero, mul_zero, add_zero] at hcontact
  push_cast at hcontact
  have hscaleZ : (0 : ℤ) < D.scale := by
    exact_mod_cast D.scale_pos
  have hdegZ :
      (ordinaryDegree4 d : ℤ) = (T.topFace.degree : ℤ) := by
    nlinarith
  have hdeg : ordinaryDegree4 d = T.topFace.degree := by
    exact_mod_cast hdegZ
  have hdTop : d ∈ T.topFace.face.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact MvPolynomial.mem_support_iff.mp hdSource
  have hpr :
      MvSupportOnFacet .pr T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      D.coefficient_ne_zero D.topFace_eq .pr (by decide)
  have hsp :
      MvSupportOnFacet .sp T.topFace.face :=
    P.pureLongitudinal_topFaceOnFacet
      D.coefficient_ne_zero D.topFace_eq .sp (by decide)
  have h1 : d (1 : Fin 4) = 0 := by
    have hz := (onFacet_toToricExponent_iff .pr d).1 (hpr d hdTop)
    simpa [facetOmittedCoordinate] using hz
  have h2 : d (2 : Fin 4) = 0 := by
    have hz := (onFacet_toToricExponent_iff .sp d).1 (hsp d hdTop)
    simpa [facetOmittedCoordinate] using hz
  refine ⟨?_, ?_, ?_⟩
  · simpa [d] using hdSource
  · simpa [d] using hdeg
  · simpa [d] using
      (show MvExponentOnCodimensionTwoBoundary d from
        ⟨(1 : Fin 4), (2 : Fin 4), by decide, h1, h2⟩)

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
    (homit : facetOmittedCoordinate facet ≠ (0 : Fin 4))
    (dstar : Fin 4 →₀ ℕ)
    (hdstar : dstar ∈ T.representedSpecialFiber.support)
    (hdstarDeg : 3 ≤ ordinaryDegree4 dstar)
    (hdstarPos : 0 < dstar (facetOmittedCoordinate facet)) :
    Nonempty P.PureLongitudinalFirstContactFrontier := by
  have htopFace :
      MvSupportOnFacet facet T.topFace.face :=
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
      (onFacet_toToricExponent_iff facet dstar).1 hfacet
    exact (Nat.ne_of_gt hdstarPos) hz
  have hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        T.representedSpecialFiber :=
    T.representedSpecialFiber_isPolynomialMongeAmpere
  have hattained :
      ∃ d ∈ T.representedSpecialFiber.support,
        ordinaryDegree4 d = T.topFace.degree :=
    T.topFace_degree_attained_in_source

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
        (crossFacetOppositeCoordinate (facetOmittedCoordinate facet))
        (facetOmittedCoordinate facet) :=
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
  rcases T.exists_nonlinear_transverse_source with
    ⟨d, hd, hdeg, h1 | h2 | h3⟩
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .pr (by decide)
      d hd hdeg (by simpa [facetOmittedCoordinate] using h1)
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .sp (by decide)
      d hd hdeg (by simpa [facetOmittedCoordinate] using h2)
  · exact P.pureLongitudinal_firstContact_or_square_at_facet
      coefficient_ne_zero topFace_eq .rq (by decide)
      d hd hdeg (by simpa [facetOmittedCoordinate] using h3)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
