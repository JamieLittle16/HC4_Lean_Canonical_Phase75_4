import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeSourceSplit
import HC4.Newton.FirstNonfacetLowDegreeSquareSplit
import HC4.Newton.FirstContactCrossFacetCarrier
import HC4.Newton.FirstContactNonlinearSupport
import HC4.Newton.FiniteSupportCrossFacetRay
import Mathlib.Tactic

/-!
# A19.66: tame lower nonlinear escape gives an honest cross-facet contact

A19.60 isolates the only source-side first-nonfacet situation: the maximal
ordinary face is confined to a coordinate facet, but a lower nonlinear source
monomial lies outside it.  A19.65 makes the remaining low-degree hypothesis
exhaustive: either the source is tame at that facet or it contains a literal
quadratic square in the omitted coordinate.

In the tame branch we now run the generic finite-support first-contact selector
on the actual represented special fibre.  The selected top degree is genuinely
attained by the retained A18.5.12 witness.  Therefore A18.5.70 supplies actual
support on both sides of the first-contact carrier, and A18.5.65c constructs a
genuine exact cross-facet face.

The resulting carrier retains only facts proved without torus balance:

* positive first-contact scale and bump;
* exact first-contact initial-form identity;
* zero Hessian determinant;
* every supported monomial is genuinely nonlinear;
* non-confinement to the starting facet;
* an honest `CrossFacetInitialData`; and
* the exact first-contact equation on every supported exponent.

A19.67 can then refine that finite carrier through all three non-contact
coordinates to an honest affine support ray, still without torus balance.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Balance-free exact cross-facet carrier obtained from a genuine first
non-facet contact on the represented strict-low zero-clock source. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet) : Type (u + 1) where
  scale : ℕ
  bump : ℕ
  face : MvPolynomial (Fin 4) K
  face_eq :
    face = HC4.Polynomial.initialForm
      (HC4.Newton.scaledContactWeight
        (HC4.Polynomial.facetOmittedCoordinate facet) scale bump)
      ((scale * T.topFace.degree : ℕ) : ℤ)
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  scale_pos : 0 < scale
  bump_pos : 0 < bump
  hessian_zero : HC4.Polynomial.hessianDeterminant face = 0
  support_degree_ge_three :
    ∀ d ∈ face.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d
  not_on_facet : ¬ HC4.Polynomial.MvSupportOnFacet facet face
  crossFacet : HC4.Newton.CrossFacetInitialData face
    (HC4.Newton.crossFacetOppositeCoordinate
      (HC4.Polynomial.facetOmittedCoordinate facet))
    (HC4.Polynomial.facetOmittedCoordinate facet)
  contact_eq :
    ∀ d ∈ face.support,
      HC4.Newton.scaledContactExponentWeight
          (HC4.Polynomial.facetOmittedCoordinate facet) scale bump d =
        ((scale * T.topFace.degree : ℕ) : ℤ)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {facet : ToricFacet}

/-- The exact first-contact carrier has support on both sides of its contact
facet, literally witnessed by the already-retained cross-facet data. -/
theorem zero_and_positive_support_nonempty
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    (HC4.Newton.zeroCoordinateSupport
        (HC4.Polynomial.facetOmittedCoordinate facet) D.face).Nonempty ∧
      (HC4.Newton.positiveCoordinateSupport
        (HC4.Polynomial.facetOmittedCoordinate facet) D.face).Nonempty := by
  constructor
  · exact ⟨D.crossFacet.facetExponent,
      HC4.Newton.mem_zeroCoordinateSupport.mpr
        ⟨D.crossFacet.facet_mem, D.crossFacet.facet_coordinate_zero⟩⟩
  · exact ⟨D.crossFacet.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D.crossFacet.outside_mem, D.crossFacet.outside_coordinate_pos⟩⟩

/-- **Balance-free affine ray carried by every tame first-nonfacet contact.** -/
noncomputable def ray
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    HC4.Newton.CrossFacetRayData D.face
      (HC4.Polynomial.facetOmittedCoordinate facet) :=
  HC4.Newton.crossFacetRayData
    D.zero_and_positive_support_nonempty.1
    D.zero_and_positive_support_nonempty.2

/-- Hessian singularity passes through all three ray-exposure stages. -/
theorem ray_hessian_zero
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    HC4.Polynomial.hessianDeterminant D.ray.face = 0 :=
  D.ray.hessian_zero_of_source D.hessian_zero

/-- Every ray exponent is still genuinely nonlinear. -/
theorem ray_support_degree_ge_three
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    ∀ d ∈ D.ray.face.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
  intro d hd
  exact D.support_degree_ge_three d (D.ray.support_subset hd)

/-- The genuine first-contact equation restricts unchanged to the extracted
balance-free affine ray. -/
theorem ray_contact_eq
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    ∀ d ∈ D.ray.face.support,
      HC4.Newton.scaledContactExponentWeight
          (HC4.Polynomial.facetOmittedCoordinate facet) D.scale D.bump d =
        ((D.scale * T.topFace.degree : ℕ) : ℤ) := by
  intro d hd
  exact D.contact_eq d (D.ray.support_subset hd)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **Tame lower nonlinear escape produces the honest balance-free
first-contact cross-facet carrier.** -/
noncomputable def firstNonfacetCrossFacetData_of_tame
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (htop : HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
    (hout : HC4.Newton.HasNonlinearOutsideFacet facet
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
    (htame : HC4.Newton.LowDegreeTameAtFacet facet
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) :
    HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet := by
  let psi := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  have hfirst := HC4.Newton.exists_singular_first_nonfacet_contact
    T.topFace_degree_ge_three
    T.representedSpecialFiber_nonlinearDegreeBound_topFace
    htop hout htame T.representedSpecialFiber_isPolynomialMongeAmpere
  have hnonempty : Nonempty
      (HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        T facet) := by
    rcases hfirst with
      ⟨d₀, scale, bump, hdpsi, hddeg, hdpos, hscaleEq, hbumpEq,
        hscale, hbump, hbound, hzero, hdG, hnot⟩
    let G : MvPolynomial (Fin 4) K :=
      HC4.Polynomial.initialForm
        (HC4.Newton.scaledContactWeight
          (HC4.Polynomial.facetOmittedCoordinate facet) scale bump)
        ((scale * T.topFace.degree : ℕ) : ℤ) psi
    have hGeq :
        G = HC4.Polynomial.initialForm
          (HC4.Newton.scaledContactWeight
            (HC4.Polynomial.facetOmittedCoordinate facet) scale bump)
          ((scale * T.topFace.degree : ℕ) : ℤ) psi := rfl
    have hnotG : ¬ HC4.Polynomial.MvSupportOnFacet facet G := by
      simpa [G, psi] using hnot
    have hzeroG : HC4.Polynomial.hessianDeterminant G = 0 := by
      simpa [G, psi] using hzero
    have hdcontact :
        HC4.Newton.scaledContactExponentWeight
            (HC4.Polynomial.facetOmittedCoordinate facet) scale bump d₀ =
          ((scale * T.topFace.degree : ℕ) : ℤ) := by
      exact HC4.Newton.scaledContactInitialForm_support_contact_eq hdG
    have hbumpBound :
        bump ≤ scale * (T.topFace.degree - 3) := by
      exact HC4.Newton.bump_le_scale_mul_m_sub_three
        hscale hdpos hddeg hdcontact
    have hlow :
        ∀ d ∈ psi.support,
          HC4.Polynomial.ordinaryDegree4 d < 3 →
            d (HC4.Polynomial.facetOmittedCoordinate facet) ≤ 1 := by
      simpa [HC4.Newton.LowDegreeTameAtFacet, psi] using htame
    have hnonlinear :
        ∀ d ∈ G.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
      dsimp [G]
      exact HC4.Newton.firstContact_initialForm_support_degree_ge_three
        T.topFace_degree_ge_three hscale hbumpBound hlow
    have hattained :
        ∃ v ∈ psi.support, HC4.Polynomial.ordinaryDegree4 v = T.topFace.degree := by
      exact ⟨T.topFace.witness, by simpa [psi] using T.topFace.witness_mem,
        T.topFace.witness_degree⟩
    have hsupports := HC4.Newton.firstContactCarrier_crossFacet_supports
      (F := facet) (m := T.topFace.degree) (scale := scale) (bump := bump)
      (psi := psi) (G := G) htop hattained hGeq hnotG
    have hfacet :
        (HC4.Newton.zeroCoordinateSupport
          (HC4.Polynomial.facetOmittedCoordinate facet) G).Nonempty :=
      hsupports.1
    have houtside :
        (HC4.Newton.positiveCoordinateSupport
          (HC4.Polynomial.facetOmittedCoordinate facet) G).Nonempty :=
      hsupports.2.1
    let D : HC4.Newton.CrossFacetInitialData G
        (HC4.Newton.crossFacetOppositeCoordinate
          (HC4.Polynomial.facetOmittedCoordinate facet))
        (HC4.Polynomial.facetOmittedCoordinate facet) :=
      HC4.Newton.crossFacetInitialData hfacet houtside
    exact ⟨{
      scale := scale
      bump := bump
      face := G
      face_eq := by simpa [G, psi]
      scale_pos := hscale
      bump_pos := hbump
      hessian_zero := hzeroG
      support_degree_ge_three := hnonlinear
      not_on_facet := hnotG
      crossFacet := D
      contact_eq := hsupports.2.2
    }⟩
  exact Classical.choice hnonempty

/-- Refine the A19.60 rank-three source trichotomy by splitting the lower
outside-support branch into an actual first-contact cross-facet carrier or a
literal omitted-coordinate quadratic square. -/
theorem rankThree_crossFacet_or_firstNonfacetCrossFacet_or_quadraticSquare_or_nonlinearConfined
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree : MvRankThreeOnFacet facet
      T.exposedSingularBoundaryVertex.exponent) :
    Nonempty
        (HC4.Newton.CrossFacetInitialData T.topFace.face
          (HC4.Newton.crossFacetOppositeCoordinate
            (HC4.Polynomial.facetOmittedCoordinate facet))
          (HC4.Polynomial.facetOmittedCoordinate facet)) ∨
      Nonempty
        (HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          T facet) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
        d (HC4.Polynomial.facetOmittedCoordinate facet) = 2 ∧
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0) ∨
      (∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) := by
  rcases T.rankThree_crossFacet_or_nonlinearOutside_or_nonlinearConfined
      facet hthree with hcross | hlower | hconfined
  · exact Or.inl hcross
  · rcases hlower with ⟨hout, htop⟩
    rcases HC4.Newton.lowDegreeTame_or_exists_omittedQuadraticSquare facet
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) with
      htame | hsquare
    · exact Or.inr (Or.inl
        ⟨T.firstNonfacetCrossFacetData_of_tame facet htop hout htame⟩)
    · exact Or.inr (Or.inr (Or.inl hsquare))
  · exact Or.inr (Or.inr (Or.inr hconfined))

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
