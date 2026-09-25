import HC4.Newton.FirstContactCrossFacetExtremeRayPositive
import HC4.Newton.InteriorVertex
import Mathlib.Tactic

/-!
# Far boundary endpoint of the genuine first-contact cross-facet line

The positive extreme-ray first-contact packet fixes the near endpoint of the
exact secondary face on a positive ray adjacent to `.qs`.  The same face is
already known to be one-dimensional: its contact coordinate is injective on
support.

This file exposes the opposite endpoint without introducing convex geometry.
Maximise the contact coordinate on the finite support of the exact cross-facet
face.  Injectivity makes the resulting coordinate-max initial form a literal
single monomial.  The outside support witness shows that its contact coordinate
is positive.  Since the entire carrier is nonlinear and Hessian-singular, the
existing exposed-monomial theorem puts this far endpoint on the toric boundary.

Thus both ends of the honest first-contact line are now genuine boundary
points.  The far point is immediately classified as either rank three on a
facet or lying on an extreme ray; this is the finite split consumed next by
the rank-three/complementary polynomial obstructions.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual far endpoint of an honest contact-zero cross-facet line,
together with its boundary-stratum classification. -/
structure CrossFacetFarBoundaryData
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) where
  exponent : Fin 4 →₀ ℕ
  mem_face : exponent ∈ D.face.support
  contact_pos : 0 < exponent (0 : Fin 4)
  contact_max :
    ∀ d ∈ D.face.support, d (0 : Fin 4) ≤ exponent (0 : Fin 4)
  coeff_ne_zero : MvPolynomial.coeff exponent D.face ≠ 0
  boundary : MvExponentOnBoundary exponent
  stratum :
    (∃ F : ToricFacet, MvRankThreeOnFacet F exponent) ∨
      (∃ F H : ToricFacet,
        AdjacentFacets F H ∧
          OnRay a b F H (toToricExponent exponent))

/-- **Far endpoint extraction for the exact first-contact line.**

The only nontrivial bookkeeping is singleton exposure.  A coordinate-zero
maximum of `D.face` has all support points at the same contact coordinate;
the already-proved contact-coordinate injectivity therefore makes that
coordinate-max face a single monomial. -/
noncomputable def CrossFacetInitialData.farBoundaryData
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant G = 0)
    (hnonlinear : ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) :
    CrossFacetFarBoundaryData (a := a) (b := b) D := by
  have hface_ne : D.face ≠ 0 := by
    intro hz
    have hmem := D.facet_mem_face
    rw [hz] at hmem
    simpa using hmem

  let E := coordinateMaxInitialData D.face hface_ne (0 : Fin 4)
  let far : Fin 4 →₀ ℕ := E.witness
  let c : K := MvPolynomial.coeff far E.face

  have hfarE : far ∈ E.face.support := by
    simpa [far, E] using E.witness_mem
  have hfarD : far ∈ D.face.support :=
    E.support_subset hfarE

  have hfar_coord : far (0 : Fin 4) = E.level := by
    simpa [far, E] using E.witness_coordinate
  have hlevel_pos : 0 < E.level := by
    have hout_le :
        D.outsideExponent (0 : Fin 4) ≤ E.level :=
      E.maximal D.outsideExponent D.outside_mem_face
    exact lt_of_lt_of_le D.outside_coordinate_pos hout_le
  have hfar_pos : 0 < far (0 : Fin 4) := by
    rw [hfar_coord]
    exact hlevel_pos

  have hunique :
      ∀ q ∈ E.face.support, q = far := by
    intro q hq
    have hqD : q ∈ D.face.support :=
      E.support_subset hq
    have hq0 : q (0 : Fin 4) = far (0 : Fin 4) := by
      exact
        (E.coordinate_eq q hq).trans hfar_coord.symm
    exact D.support_eq_of_contactCoordinate_eq
      ha hb hcontactScale hBal hcontact hqD hfarD hq0

  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp hfarE

  have hmono : E.face = MvPolynomial.monomial far c := by
    apply MvPolynomial.ext
    intro q
    by_cases hq : q = far
    · subst q
      simp [c]
    · have hqzero : MvPolynomial.coeff q E.face = 0 := by
        by_contra hne
        have hqs : q ∈ E.face.support :=
          MvPolynomial.mem_support_iff.mpr hne
        exact hq (hunique q hqs)
      rw [hqzero]
      simp [hq]

  have hinit :
      initialForm (coordinateMaxWeight (0 : Fin 4))
          (E.level : ℤ) D.face =
        MvPolynomial.monomial far c := by
    rw [← E.face_eq]
    exact hmono

  have hfarG : far ∈ G.support :=
    D.support_subset hfarD
  have hfar_deg : 3 ≤ ordinaryDegree4 far :=
    hnonlinear far hfarG
  have hface_zero : hessianDeterminant D.face = 0 :=
    D.hessian_zero hzero
  have hboundary : MvExponentOnBoundary far :=
    exposed_monomial_on_boundary_of_zero_hessian
      E.weight_bound hface_zero hinit hc hfar_deg

  have hBalFace : HasBalancedMvSupport a b D.face :=
    D.balanced hBal
  have hfarBal : IsBalancedExponent a b far :=
    hBalFace far hfarD
  have hstratum :=
    mvBoundary_rankThree_or_extremeRay
      ha hb hcop hfarBal hboundary

  refine {
    exponent := far
    mem_face := hfarD
    contact_pos := hfar_pos
    contact_max := ?_
    coeff_ne_zero := ?_
    boundary := hboundary
    stratum := hstratum
  }
  · intro d hd
    have hle : d (0 : Fin 4) ≤ E.level :=
      E.maximal d hd
    simpa [hfar_coord] using hle
  · exact MvPolynomial.mem_support_iff.mp hfarD

end

end HC4.Newton
