import HC4.RationalRigidity.FirstContactCrossFacetFarRankThreeAffine
import HC4.Valuation.SingularWeightedKernelOpening
import Mathlib.Tactic

/-!
# First-contact cross-facet child kernel as a generic weighted opening

The affine RationalRigidity endgame now shows that the exact secondary
cross-facet child of a genuine positive first contact has a literal coordinate
kernel.  The secondary exposing weight is integer-valued and may have one
negative coefficient, whereas `SingularWeightedKernelOpeningData` uses a
bounded natural weight.

On the first-contact carrier this is only bookkeeping.  Every supported
exponent has the same positive first-contact weight, so adding any multiple of
that weight to the secondary weight does not change the selected secondary
face.  We add exactly enough to make every coordinate weight nonnegative and
then take the corresponding natural weight.

Thus, when the kernel is not already present on the first-contact carrier, the
literal child kernel is an honest `SingularWeightedKernelOpeningData` packet.
If it is already present on the carrier, that stronger parent-kernel event is
retained rather than being disguised as a first opening.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Amount of positive first-contact weight needed to absorb a possibly
negative secondary cross-facet bump. -/
def firstContactCrossFacetWeightShift
    {G : MvPolynomial (Fin 4) K}
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) : ℕ :=
  Int.toNat (-D.bump)

/-- Integer weight obtained by adding a constant-on-support multiple of the
first-contact weight to the secondary cross-facet exposing weight. -/
def shiftedFirstContactCrossFacetWeight
    {G : MvPolynomial (Fin 4) K}
    (contactScale contactBump : ℕ)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) :
    Fin 4 → ℤ :=
  fun i =>
    crossFacetWeight
        (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
        D.scale D.bump i +
      (firstContactCrossFacetWeightShift D : ℤ) *
        scaledContactWeight (0 : Fin 4) contactScale contactBump i

/-- The shifted secondary weight is coordinatewise nonnegative. -/
theorem shiftedFirstContactCrossFacetWeight_nonneg
    {G : MvPolynomial (Fin 4) K}
    {contactScale contactBump : ℕ}
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) :
    ∀ i : Fin 4,
      0 ≤ shiftedFirstContactCrossFacetWeight contactScale contactBump D i := by
  intro i
  fin_cases i
  · cases hb : D.bump with
    | ofNat n =>
        simp [shiftedFirstContactCrossFacetWeight,
          firstContactCrossFacetWeightShift, hb,
          crossFacetWeight, crossFacetOppositeCoordinate,
          scaledContactWeight]
    | negSucc n =>
        have hsumNat : 1 ≤ contactScale + contactBump := by omega
        have hsumZ : (1 : ℤ) ≤ (contactScale + contactBump : ℕ) := by
          exact_mod_cast hsumNat
        have hnZ : (0 : ℤ) ≤ (n + 1 : ℕ) := by positivity
        have hmul :=
          mul_le_mul_of_nonneg_left hsumZ hnZ
        simp [shiftedFirstContactCrossFacetWeight,
          firstContactCrossFacetWeightShift, hb,
          crossFacetWeight, crossFacetOppositeCoordinate,
          scaledContactWeight]
        nlinarith
  · simp [shiftedFirstContactCrossFacetWeight,
      firstContactCrossFacetWeightShift,
      crossFacetWeight, crossFacetOppositeCoordinate,
      scaledContactWeight]
    positivity
  · simp [shiftedFirstContactCrossFacetWeight,
      firstContactCrossFacetWeightShift,
      crossFacetWeight, crossFacetOppositeCoordinate,
      scaledContactWeight]
    positivity
  · simp [shiftedFirstContactCrossFacetWeight,
      firstContactCrossFacetWeightShift,
      crossFacetWeight, crossFacetOppositeCoordinate,
      scaledContactWeight]
    positivity

/-- Natural version of the shifted secondary weight. -/
def naturalFirstContactCrossFacetWeight
    {G : MvPolynomial (Fin 4) K}
    (contactScale contactBump : ℕ)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) :
    Fin 4 → ℕ :=
  fun i =>
    Int.toNat
      (shiftedFirstContactCrossFacetWeight contactScale contactBump D i)

/-- Casting the naturalized weight back to integers recovers the shifted
secondary weight literally. -/
theorem naturalFirstContactCrossFacetWeight_cast
    {G : MvPolynomial (Fin 4) K}
    {contactScale contactBump : ℕ}
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (i : Fin 4) :
    (naturalFirstContactCrossFacetWeight contactScale contactBump D i : ℤ) =
      shiftedFirstContactCrossFacetWeight contactScale contactBump D i := by
  unfold naturalFirstContactCrossFacetWeight
  exact Int.toNat_of_nonneg
    (shiftedFirstContactCrossFacetWeight_nonneg hcontactScale D i)

/-- Weight of an exponent under the naturalized secondary weight.  The only
change from the original secondary weight is the fixed multiple of the
first-contact weight. -/
theorem weight_naturalFirstContactCrossFacetWeight
    {G : MvPolynomial (Fin 4) K}
    {contactScale contactBump : ℕ}
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (d : Fin 4 →₀ ℕ) :
    (Finsupp.weight
        (naturalFirstContactCrossFacetWeight contactScale contactBump D) d : ℤ) =
      Finsupp.weight
          (crossFacetWeight
            (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
            D.scale D.bump) d +
        (firstContactCrossFacetWeightShift D : ℤ) *
          scaledContactExponentWeight
            (0 : Fin 4) contactScale contactBump d := by
  let w :=
    naturalFirstContactCrossFacetWeight contactScale contactBump D
  have hcast :
      (Finsupp.weight w d : ℤ) =
        Finsupp.weight (fun i => (w i : ℤ)) d := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply]
    push_cast
    rfl
  rw [hcast]
  have hw :
      (fun i => (w i : ℤ)) =
        shiftedFirstContactCrossFacetWeight contactScale contactBump D := by
    funext i
    exact naturalFirstContactCrossFacetWeight_cast
      hcontactScale D i
  rw [hw]
  rw [HC4.Newton.weight_crossFacetWeight,
    HC4.Newton.weight_scaledContactWeight]
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [shiftedFirstContactCrossFacetWeight,
      firstContactCrossFacetWeightShift,
      crossFacetWeight, crossFacetOppositeCoordinate,
      scaledContactWeight, scaledContactExponentWeight,
      ordinaryDegree4, Fin.sum_univ_four]
    ring
  · intro i
    simp

/-- **Secondary child kernel -> generic singular weighted opening.**

The parent is the genuine first-contact carrier.  Its support is already on one
exact first-contact level, so the shifted natural weight selects exactly the
same secondary child `D.face`. -/
theorem CrossFacetInitialData.exists_singularWeightedKernelOpeningData
    {G : MvPolynomial (Fin 4) K}
    {contactScale contactBump : ℕ}
    {contactLevel : ℤ}
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hcontact :
      ∀ d ∈ G.support,
        scaledContactExponentWeight
          (0 : Fin 4) contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant G = 0)
    (hnonlinear : ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d)
    (kernelCoordinate : Fin 4)
    (hchildKernel :
      MvPolynomial.pderiv kernelCoordinate D.face = 0)
    (hparentKernel :
      MvPolynomial.pderiv kernelCoordinate G ≠ 0) :
    Nonempty (SingularWeightedKernelOpeningData G) := by
  let w : Fin 4 → ℕ :=
    naturalFirstContactCrossFacetWeight contactScale contactBump D
  let level : ℕ := Finsupp.weight w D.facetExponent

  have hfacetSecondary :
      Finsupp.weight
          (crossFacetWeight
            (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
            D.scale D.bump)
          D.facetExponent = D.level :=
    D.face_weight_eq D.facet_mem_face

  have hfacetContact :
      scaledContactExponentWeight
          (0 : Fin 4) contactScale contactBump D.facetExponent =
        contactLevel :=
    hcontact D.facetExponent D.facet_mem

  have hweightValue :
      ∀ d : Fin 4 →₀ ℕ,
        (Finsupp.weight w d : ℤ) =
          Finsupp.weight
              (crossFacetWeight
                (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
                D.scale D.bump) d +
            (firstContactCrossFacetWeightShift D : ℤ) *
              scaledContactExponentWeight
                (0 : Fin 4) contactScale contactBump d := by
    intro d
    simpa [w] using
      weight_naturalFirstContactCrossFacetWeight
        hcontactScale D d

  have hlevelValue :
      (level : ℤ) =
        D.level +
          (firstContactCrossFacetWeightShift D : ℤ) * contactLevel := by
    dsimp [level]
    rw [hweightValue D.facetExponent,
      hfacetSecondary, hfacetContact]

  have hbound : HasReverseWeightBound w level G := by
    intro d hd
    have hsecondary :=
      D.weight_bound hd
    have hcontactD := hcontact d hd
    have hz :
        (Finsupp.weight w d : ℤ) ≤ (level : ℤ) := by
      rw [hweightValue d, hlevelValue, hcontactD]
      exact add_le_add_right hsecondary _
    exact_mod_cast hz

  have hinitial :
      initialForm (fun i => (w i : ℤ)) (level : ℤ) G = D.face := by
    rw [D.face_eq]
    apply MvPolynomial.ext
    intro d
    rw [coeff_initialForm, coeff_initialForm]
    by_cases hcoeff : MvPolynomial.coeff d G = 0
    · simp [hcoeff]
    · have hd : d ∈ G.support :=
        MvPolynomial.mem_support_iff.mpr hcoeff
      have hcontactD := hcontact d hd
      have hcast :
          Finsupp.weight (fun i => (w i : ℤ)) d =
            (Finsupp.weight w d : ℤ) := by
        rw [Finsupp.weight_apply, Finsupp.weight_apply]
        push_cast
        rfl
      have hiff :
          Finsupp.weight (fun i => (w i : ℤ)) d = (level : ℤ) ↔
            Finsupp.weight
                (crossFacetWeight
                  (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
                  D.scale D.bump) d = D.level := by
        rw [hcast, hweightValue d, hlevelValue, hcontactD]
        constructor <;> intro h <;> omega
      by_cases hs :
          Finsupp.weight
              (crossFacetWeight
                (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)
                D.scale D.bump) d = D.level
      · have hn := hiff.mpr hs
        simp [hs, hn]
      · have hn :
            Finsupp.weight (fun i => (w i : ℤ)) d ≠ (level : ℤ) := by
          intro h
          exact hs (hiff.mp h)
        simp [hs, hn]

  exact ⟨{
    child := D.face
    weight := w
    level := level
    kernelCoordinate := kernelCoordinate
    weight_bound := hbound
    initialForm_eq_child := hinitial
    parent_hessian_zero := hzero
    child_kernel := hchildKernel
    parent_kernel_ne := hparentKernel
    parent_support_degree_ge_three := hnonlinear
  }⟩

/-- **Rooted RR child-kernel bridge.**

The completed affine-RR theorem now feeds the generic weighted-kernel-opening
machinery without weakening its literal child kernel.  Either that coordinate
already annihilates the first-contact carrier `G`, or the exact secondary
child is a genuine first kernel opening of `G`. -/
theorem exists_qs_firstNonfacet_crossFacet_childKernelOpening
    {a b m : ℕ} {psi : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet .qs m psi)
    (hattained : ∃ v ∈ psi.support, ordinaryDegree4 v = m)
    (hout : HasNonlinearOutsideFacet .qs psi)
    (hlow : LowDegreeTameAtFacet .qs psi)
    (hBal : HasBalancedMvSupport a b psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    ∃ (scale bump : ℕ) (G : MvPolynomial (Fin 4) K)
      (D : CrossFacetInitialData G
        (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
      (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
      (kernelCoordinate : Fin 4),
      G = initialForm
          (scaledContactWeight (0 : Fin 4) scale bump)
          ((scale * m : ℕ) : ℤ) psi ∧
      0 < scale ∧
      0 < bump ∧
      hessianDeterminant G = 0 ∧
      HasBalancedMvSupport a b G ∧
      (∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) ∧
      MvPolynomial.pderiv kernelCoordinate D.face = 0 ∧
      (MvPolynomial.pderiv kernelCoordinate G = 0 ∨
        Nonempty (SingularWeightedKernelOpeningData G)) := by
  rcases HC4.RationalRigidity.exists_qs_firstNonfacet_crossFacet_childKernel
      ha hb hcop hm hdeg htop hattained hout hlow hBal hMA with
    ⟨scale, bump, G, D, R, kernelCoordinate,
      hG, hscale, hbump, hzero, hGBal, hnonlinear, hchildKernel⟩

  have hcontact :
      ∀ d ∈ G.support,
        scaledContactExponentWeight (0 : Fin 4) scale bump d =
          ((scale * m : ℕ) : ℤ) := by
    intro d hd
    have hd' :
        d ∈
          (initialForm
            (scaledContactWeight (0 : Fin 4) scale bump)
            ((scale * m : ℕ) : ℤ) psi).support := by
      simpa [hG] using hd
    exact scaledContactInitialForm_support_contact_eq hd'

  refine ⟨scale, bump, G, D, R, kernelCoordinate,
    hG, hscale, hbump, hzero, hGBal, hnonlinear, hchildKernel, ?_⟩
  by_cases hparent :
      MvPolynomial.pderiv kernelCoordinate G = 0
  · exact Or.inl hparent
  · exact Or.inr
      (D.exists_singularWeightedKernelOpeningData
        hscale hcontact hzero hnonlinear
        kernelCoordinate hchildKernel hparent)

end

end HC4.Valuation
