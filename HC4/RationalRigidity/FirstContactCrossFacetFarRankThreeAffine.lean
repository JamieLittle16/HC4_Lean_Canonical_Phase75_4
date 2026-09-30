import HC4.Newton.FirstContactCrossFacetFarBoundary
import HC4.Polynomial.RankThreeAffineSupportRealisation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
import HC4.RationalRigidity.RankThreeAffineHomogeneousTerminalSplit
import Mathlib.Tactic

/-!
# Far rank-three first-contact line as an honest affine terminal carrier

The genuine cross-facet first-contact line has two distinguished ends:

* the near endpoint is the positive extreme ray produced by first contact;
* the far endpoint is obtained by finite coordinate maximisation.

When the far endpoint is rank three on a facet and the near endpoint is
positive in that facet's omitted coordinate, swap the omitted coordinate into
slot zero and rebase the line at the far endpoint.  The far endpoint then has
shape `(0,A,B,C)` with `A,B,C>0`, while the swapped omitted coordinate is
injective on support.

The transverse slopes need not be integral.  This is exactly the purpose of
`RankThreeAffineSupportData`: the entire renamed child face is represented by
an honest affine line with unit longitudinal step and field-valued transverse
directions.  No gcd or Laurent-monomial reconstruction is introduced.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Source-honest affine support package obtained by reorienting a genuine
far rank-three first-contact endpoint. -/
structure CrossFacetFarRankThreeAffineSupportData
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D) where
  farFacet : ToricFacet
  rankThree : MvRankThreeOnFacet farFacet R.exponent
  rho : Equiv.Perm (Fin 4)
  rho_eq :
    rho = Equiv.swap (0 : Fin 4) (facetOmittedCoordinate farFacet)
  nearOmitted_pos :
    0 < D.facetExponent (facetOmittedCoordinate farFacet)
  A : ℕ
  B : ℕ
  C : ℕ
  q : K
  r : K
  s : K
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  support :
    RankThreeAffineSupportData
      (MvPolynomial.rename rho D.face) A B C q r s
  farIndex_zero :
    (Finsupp.mapDomain rho R.exponent) (0 : Fin 4) = 0
  nearIndex_pos :
    0 < (Finsupp.mapDomain rho D.facetExponent) (0 : Fin 4)
  nearIndex_max :
    ∀ e ∈ (MvPolynomial.rename rho D.face).support,
      e (0 : Fin 4) ≤
        (Finsupp.mapDomain rho D.facetExponent) (0 : Fin 4)

/-- **Far rank-three -> honest affine support.**

The only geometric input beyond far rank-three membership is positivity of the
near endpoint in the far facet's omitted coordinate.  The reorientation and
all affine identities are then forced by the already-green first-contact line
proportionality theorem. -/
theorem CrossFacetFarBoundaryData.exists_rankThreeAffineSupportData
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (F : ToricFacet)
    (hthree : MvRankThreeOnFacet F R.exponent)
    (hnear_pos :
      0 < D.facetExponent (facetOmittedCoordinate F)) :
    Nonempty (CrossFacetFarRankThreeAffineSupportData D R) := by
  classical
  let f : Fin 4 := facetOmittedCoordinate F
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) f
  let carrier : MvPolynomial (Fin 4) K :=
    MvPolynomial.rename rho D.face
  let A : ℕ := R.exponent (rho.symm (1 : Fin 4))
  let B : ℕ := R.exponent (rho.symm (2 : Fin 4))
  let C : ℕ := R.exponent (rho.symm (3 : Fin 4))

  have hfar_zero : R.exponent f = 0 := by
    cases F <;>
      simpa [f, facetOmittedCoordinate] using
        ((mvRankThreeOnFacet_iff _ R.exponent).1 hthree).1

  have hf_ne_zero : f ≠ (0 : Fin 4) := by
    intro hf
    have hz : D.facetExponent f = 0 := by
      rw [hf]
      exact D.facet_coordinate_zero
    rw [hz] at hnear_pos
    omega

  have hrho0 : rho.symm (0 : Fin 4) = f := by
    simp [rho, Equiv.symm_swap, hf_ne_zero]

  have hvfK : ((D.facetExponent f : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnear_pos)

  let q : K :=
    (((D.facetExponent (rho.symm (1 : Fin 4)) : ℕ) : K) -
      ((R.exponent (rho.symm (1 : Fin 4)) : ℕ) : K)) /
      ((D.facetExponent f : ℕ) : K)
  let r : K :=
    (((D.facetExponent (rho.symm (2 : Fin 4)) : ℕ) : K) -
      ((R.exponent (rho.symm (2 : Fin 4)) : ℕ) : K)) /
      ((D.facetExponent f : ℕ) : K)
  let s : K :=
    (((D.facetExponent (rho.symm (3 : Fin 4)) : ℕ) : K) -
      ((R.exponent (rho.symm (3 : Fin 4)) : ℕ) : K)) /
      ((D.facetExponent f : ℕ) : K)

  have hpreimage :
      ∀ {e : Fin 4 →₀ ℕ}, e ∈ carrier.support →
        ∃ d ∈ D.face.support, Finsupp.mapDomain rho d = e := by
    intro e he
    dsimp [carrier] at he
    rw [MvPolynomial.support_rename_of_injective rho.injective] at he
    rcases Finset.mem_image.mp he with ⟨d, hd, hde⟩
    exact ⟨d, hd, hde⟩

  have hABC : 0 < A ∧ 0 < B ∧ 0 < C := by
    cases F with
    | pr =>
        have h := (mvRankThreeOnFacet_iff .pr R.exponent).1 hthree
        simpa [A, B, C, rho, f, facetOmittedCoordinate,
          Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] using
          ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    | rq =>
        have h := (mvRankThreeOnFacet_iff .rq R.exponent).1 hthree
        simpa [A, B, C, rho, f, facetOmittedCoordinate,
          Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] using
          ⟨h.2.2.1, h.2.2.2, h.2.1⟩
    | qs =>
        have h0 := (mvRankThreeOnFacet_iff .qs R.exponent).1 hthree
        exact (Nat.ne_of_gt R.contact_pos h0.1).elim
    | sp =>
        have h := (mvRankThreeOnFacet_iff .sp R.exponent).1 hthree
        simpa [A, B, C, rho, f, facetOmittedCoordinate,
          Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] using
          ⟨h.2.2.1, h.2.1, h.2.2.2⟩

  let S :
      RankThreeAffineSupportData carrier A B C q r s := {
    eq_of_zeroCoordinate_eq := by
      intro e g he hg heg
      rcases hpreimage he with ⟨d, hd, hde⟩
      rcases hpreimage hg with ⟨p, hp, hpe⟩
      have he0 : e (0 : Fin 4) = d f := by
        rw [← hde, Finsupp.mapDomain_equiv_apply, hrho0]
      have hg0 : g (0 : Fin 4) = p f := by
        rw [← hpe, Finsupp.mapDomain_equiv_apply, hrho0]
      have hdf : d f = p f := by
        rw [← he0, ← hg0]
        exact heg
      have hdp :=
        D.support_eq_of_farOmittedCoordinate_eq
          ha hb hcontactScale hBal hcontact R f
          hnear_pos hfar_zero hd hp hdf
      calc
        e = Finsupp.mapDomain rho d := hde.symm
        _ = Finsupp.mapDomain rho p := by rw [hdp]
        _ = g := hpe

    affine := by
      intro e he
      rcases hpreimage he with ⟨d, hd, hde⟩

      have he_apply (i : Fin 4) :
          e i = d (rho.symm i) := by
        rw [← hde, Finsupp.mapDomain_equiv_apply]

      have he_zero : e (0 : Fin 4) = d f := by
        rw [he_apply, hrho0]

      have hcoord (i : Fin 4) :
          ((e i : ℕ) : K) =
            ((R.exponent (rho.symm i) : ℕ) : K) +
              ((e (0 : Fin 4) : ℕ) : K) *
                ((((D.facetExponent (rho.symm i) : ℕ) : K) -
                    ((R.exponent (rho.symm i) : ℕ) : K)) /
                  ((D.facetExponent f : ℕ) : K)) := by
        have hlineZ :=
          D.support_farOmitted_affine_proportional
            ha hb hcontactScale hBal hcontact R f
            hnear_pos hfar_zero d hd (rho.symm i)
        have hlineK :
            ((D.facetExponent f : ℕ) : K) *
                (((d (rho.symm i) : ℕ) : K) -
                  ((R.exponent (rho.symm i) : ℕ) : K)) =
              ((d f : ℕ) : K) *
                (((D.facetExponent (rho.symm i) : ℕ) : K) -
                  ((R.exponent (rho.symm i) : ℕ) : K)) := by
          exact_mod_cast hlineZ
        rw [he_apply, he_zero]
        field_simp [hvfK]
        linear_combination hlineK

      funext i
      fin_cases i
      · simp [rankThreeLogBaseExponent, rankThreeLogDirection]
      · simpa [A, q, rankThreeLogBaseExponent,
          rankThreeLogDirection] using hcoord (1 : Fin 4)
      · simpa [B, r, rankThreeLogBaseExponent,
          rankThreeLogDirection] using hcoord (2 : Fin 4)
      · simpa [C, s, rankThreeLogBaseExponent,
          rankThreeLogDirection] using hcoord (3 : Fin 4)
  }

  exact ⟨{
    farFacet := F
    rankThree := hthree
    rho := rho
    rho_eq := rfl
    nearOmitted_pos := hnear_pos
    A := A
    B := B
    C := C
    q := q
    r := r
    s := s
    A_pos := hABC.1
    B_pos := hABC.2.1
    C_pos := hABC.2.2
    support := by simpa [carrier] using S
    farIndex_zero := by
      rw [Finsupp.mapDomain_equiv_apply, hrho0, hfar_zero]
    nearIndex_pos := by
      rw [Finsupp.mapDomain_equiv_apply, hrho0]
      exact hnear_pos
    nearIndex_max := by
      intro e he
      have heCarrier : e ∈ carrier.support := by
        simpa [carrier] using he
      rcases hpreimage heCarrier with ⟨d, hd, hde⟩
      have he0 : e (0 : Fin 4) = d f := by
        rw [← hde, Finsupp.mapDomain_equiv_apply, hrho0]
      have hnear0 :
          (Finsupp.mapDomain rho D.facetExponent) (0 : Fin 4) =
            D.facetExponent f := by
        rw [Finsupp.mapDomain_equiv_apply, hrho0]
      rw [he0, hnear0]
      exact
        D.support_farOmittedCoordinate_le_near
          ha hb hcontactScale hBal hcontact R f
          hnear_pos hfar_zero d hd
  }⟩

namespace CrossFacetFarRankThreeAffineSupportData

variable {a b : ℕ}
variable {G : MvPolynomial (Fin 4) K}
variable {D : CrossFacetInitialData G
  (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)}
variable {R : CrossFacetFarBoundaryData (a := a) (b := b) D}

/-- Canonical codimension-two ray shape after moving the far facet's omitted
coordinate into slot zero.  Exactly one transverse coordinate remains positive. -/
def HasPositiveTwoZeroTransverseTop (e : Fin 4 →₀ ℕ) : Prop :=
  (0 < e (1 : Fin 4) ∧ e (2 : Fin 4) = 0 ∧ e (3 : Fin 4) = 0) ∨
    (e (1 : Fin 4) = 0 ∧ 0 < e (2 : Fin 4) ∧ e (3 : Fin 4) = 0) ∨
    (e (1 : Fin 4) = 0 ∧ e (2 : Fin 4) = 0 ∧ 0 < e (3 : Fin 4))

/-- The original positive q/s near ray becomes one of the three canonical
two-zero transverse top shapes in the affine terminal coordinates. -/
theorem nearExtreme_topShape
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (ha : 0 < a) (hb : 0 < b)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    HasPositiveTwoZeroTransverseTop
      (Finsupp.mapDomain P.rho D.facetExponent) := by
  cases hF : P.farFacet with
  | pr =>
      rw [P.rho_eq, hF]
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        right
        left
        refine ⟨?_, ?_, ?_⟩
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3] using hn
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        right
        right
        refine ⟨?_, ?_, ?_⟩
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · have hbn : 0 < b * n := Nat.mul_pos hb hn
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3] using hbn
  | rq =>
      rw [P.rho_eq, hF]
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        have hpos := P.nearOmitted_pos
        rw [hF] at hpos
        simp [facetOmittedCoordinate, h3] at hpos
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        left
        refine ⟨?_, ?_, ?_⟩
        · have han : 0 < a * n := Nat.mul_pos ha hn
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3] using han
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
  | qs =>
      have hpos := P.nearOmitted_pos
      rw [hF] at hpos
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        simp [facetOmittedCoordinate, h0] at hpos
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        simp [facetOmittedCoordinate, h0] at hpos
  | sp =>
      rw [P.rho_eq, hF]
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        left
        refine ⟨?_, ?_, ?_⟩
        · simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3] using hn
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        have hpos := P.nearOmitted_pos
        rw [hF] at hpos
        simp [facetOmittedCoordinate, h2] at hpos

/-- The affine support representation retains the actual far endpoint as
its literal coefficient-profile index zero. -/
theorem affineLineData_zeroExponent_eq_far
    (P : CrossFacetFarRankThreeAffineSupportData D R) :
    P.support.affineLineData.exponent 0 =
      Finsupp.mapDomain P.rho R.exponent := by
  let far := Finsupp.mapDomain P.rho R.exponent
  have hfarMem :
      far ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨R.exponent, R.mem_face, rfl⟩
  have hprofileMem :
      0 ∈ P.support.coefficientProfile.support := by
    have h :=
      P.support.coefficientProfile_mem_of_mem hfarMem
    simpa [far, P.farIndex_zero] using h
  have hspec := P.support.exponentAt_spec hprofileMem
  have hzero :
      P.support.affineLineData.exponent 0 (0 : Fin 4) =
        far (0 : Fin 4) := by
    change P.support.exponentAt 0 (0 : Fin 4) = far (0 : Fin 4)
    rw [hspec.2]
    simpa [far] using P.farIndex_zero.symm
  have heq :=
    P.support.eq_of_zeroCoordinate_eq hspec.1 hfarMem hzero
  simpa [far, RankThreeAffineSupportData.affineLineData] using heq

/-- Reindexing the four variables by the far-facet swap preserves ordinary
total degree. -/
theorem ordinaryDegree4_mapDomain_rho
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (e : Fin 4 →₀ ℕ) :
    ordinaryDegree4 (Finsupp.mapDomain P.rho e) = ordinaryDegree4 e := by
  rw [P.rho_eq]
  cases hF : P.farFacet <;>
    simp [ordinaryDegree4, facetOmittedCoordinate,
      Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne] <;> omega

/-- The far endpoint has strictly smaller ordinary degree than the near
endpoint on a genuine positive-bump contact face. -/
theorem far_ordinaryDegree_lt_near
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    {contactScale contactBump : ℕ} {contactLevel : ℤ}
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    ordinaryDegree4 R.exponent < ordinaryDegree4 D.facetExponent := by
  have hfarContact :=
    hcontact R.exponent (D.support_subset R.mem_face)
  have hnearContact :=
    hcontact D.facetExponent D.facet_mem
  have hs : (0 : ℤ) < (contactScale : ℤ) := by
    exact_mod_cast hcontactScale
  have hbump : (0 : ℤ) < (contactBump : ℤ) := by
    exact_mod_cast hcontactBump
  have hr0 : (0 : ℤ) < (R.exponent (0 : Fin 4) : ℤ) := by
    exact_mod_cast R.contact_pos
  unfold scaledContactExponentWeight at hfarContact hnearContact
  rw [D.facet_coordinate_zero] at hnearContact
  simp only [Nat.cast_zero, mul_zero, add_zero] at hnearContact
  have hltZ :
      (ordinaryDegree4 R.exponent : ℤ) <
        (ordinaryDegree4 D.facetExponent : ℤ) := by
    nlinarith
  exact_mod_cast hltZ

/-- **The far affine profile cannot have degree one.**

If the reoriented near q/s endpoint had profile index one, the possible far
facets are finite.  In the q-cases the near endpoint has ordinary degree two,
while a far rank-three point has degree at least three.  In the two surviving
s-cases, torus balance at the far rank-three point gives an even stronger
degree increase.  All possibilities contradict the positive-bump degree
drop. -/
theorem profile_natDegree_ne_one
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (ha : 0 < a) (hb : 0 < b)
    {contactScale contactBump : ℕ} {contactLevel : ℤ}
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    P.support.coefficientProfile.natDegree ≠ 1 := by
  intro hdeg
  have hnearMem :
      Finsupp.mapDomain P.rho D.facetExponent ∈
        (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨D.facetExponent, D.facet_mem_face, rfl⟩
  have hnearProfile :=
    P.support.coefficientProfile_mem_of_mem hnearMem
  have hidxLe :
      (Finsupp.mapDomain P.rho D.facetExponent) (0 : Fin 4) ≤
        P.support.coefficientProfile.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hnearProfile
  have hidx :
      (Finsupp.mapDomain P.rho D.facetExponent) (0 : Fin 4) = 1 := by
    have hpos := P.nearIndex_pos
    omega
  have hdrop :=
    P.far_ordinaryDegree_lt_near
      hcontactScale hcontactBump hcontact
  have hfarBal : IsBalancedExponent a b R.exponent :=
    hBal R.exponent (D.support_subset R.mem_face)

  cases hF : P.farFacet with
  | pr =>
      have hthree := (HC4.Newton.mvRankThreeOnFacet_iff .pr R.exponent).1
        (by simpa [hF] using P.rankThree)
      rcases hthree with ⟨hr1, hr0p, hr2p, hr3p⟩
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have hnOne : n = 1 := by
          have h := hidx
          rw [P.rho_eq, hF] at h
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            facetOmittedCoordinate, hn0, hn1, hn2, hn3] using h
        have hnearDeg : ordinaryDegree4 D.facetExponent = 2 := by
          simp [ordinaryDegree4, hn0, hn1, hn2, hn3, hnOne]
        have hfarDeg : 3 ≤ ordinaryDegree4 R.exponent := by
          unfold ordinaryDegree4
          rw [hr1]
          omega
        omega
      · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have han : a * n = 1 := by
          have h := hidx
          rw [P.rho_eq, hF] at h
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            facetOmittedCoordinate, hn0, hn1, hn2, hn3] using h
        have haLower : 1 ≤ a := by omega
        have hnLower : 1 ≤ n := by omega
        have haUpper : a ≤ 1 := by
          calc
            a = a * 1 := by simp
            _ ≤ a * n := Nat.mul_le_mul_left a hnLower
            _ ≤ 1 := by omega
        have hnUpper : n ≤ 1 := by
          calc
            n = 1 * n := by simp
            _ ≤ a * n := Nat.mul_le_mul_right n haLower
            _ ≤ 1 := by omega
        have haOne : a = 1 := Nat.le_antisymm haUpper haLower
        have hnOne : n = 1 := Nat.le_antisymm hnUpper hnLower
        have hnearDeg : ordinaryDegree4 D.facetExponent = b + 1 := by
          simp [ordinaryDegree4, hn0, hn1, hn2, hn3, haOne, hnOne]
          omega
        have hfarBal' :
            R.exponent 0 = b * R.exponent 2 + R.exponent 3 := by
          simpa [IsBalancedExponent, hr1, haOne] using hfarBal
        have hbR2 : b ≤ b * R.exponent 2 := by
          have h1 : 1 ≤ R.exponent 2 := by omega
          simpa using Nat.mul_le_mul_left b h1
        have hfarDeg : b + 3 ≤ ordinaryDegree4 R.exponent := by
          unfold ordinaryDegree4
          rw [hr1, hfarBal']
          omega
        omega
  | rq =>
      have hthree := (HC4.Newton.mvRankThreeOnFacet_iff .rq R.exponent).1
        (by simpa [hF] using P.rankThree)
      rcases hthree with ⟨hr3, hr0p, hr1p, hr2p⟩
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have h := hidx
        rw [P.rho_eq, hF] at h
        simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
          facetOmittedCoordinate, hn0, hn1, hn2, hn3] at h
      · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have hbn : b * n = 1 := by
          have h := hidx
          rw [P.rho_eq, hF] at h
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            facetOmittedCoordinate, hn0, hn1, hn2, hn3] using h
        have hbLower : 1 ≤ b := by omega
        have hnLower : 1 ≤ n := by omega
        have hbUpper : b ≤ 1 := by
          calc
            b = b * 1 := by simp
            _ ≤ b * n := Nat.mul_le_mul_left b hnLower
            _ ≤ 1 := by omega
        have hnUpper : n ≤ 1 := by
          calc
            n = 1 * n := by simp
            _ ≤ b * n := Nat.mul_le_mul_right n hbLower
            _ ≤ 1 := by omega
        have hbOne : b = 1 := Nat.le_antisymm hbUpper hbLower
        have hnOne : n = 1 := Nat.le_antisymm hnUpper hnLower
        have hnearDeg : ordinaryDegree4 D.facetExponent = a + 1 := by
          simp [ordinaryDegree4, hn0, hn1, hn2, hn3, hbOne, hnOne]
        have hfarBal' :
            a * R.exponent 0 + R.exponent 1 = R.exponent 2 := by
          simpa [IsBalancedExponent, hr3, hbOne] using hfarBal
        have haR0 : a ≤ a * R.exponent 0 := by
          have h1 : 1 ≤ R.exponent 0 := by omega
          simpa using Nat.mul_le_mul_left a h1
        have hfarDeg : a + 3 ≤ ordinaryDegree4 R.exponent := by
          unfold ordinaryDegree4
          rw [hr3, ← hfarBal']
          omega
        omega
  | qs =>
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have h := hidx
        rw [P.rho_eq, hF] at h
        simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
          facetOmittedCoordinate, hn0, hn1, hn2, hn3] at h
      · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have h := hidx
        rw [P.rho_eq, hF] at h
        simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
          facetOmittedCoordinate, hn0, hn1, hn2, hn3] at h
  | sp =>
      have hthree := (HC4.Newton.mvRankThreeOnFacet_iff .sp R.exponent).1
        (by simpa [hF] using P.rankThree)
      rcases hthree with ⟨hr2, hr0p, hr1p, hr3p⟩
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have hnOne : n = 1 := by
          have h := hidx
          rw [P.rho_eq, hF] at h
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            facetOmittedCoordinate, hn0, hn1, hn2, hn3] using h
        have hnearDeg : ordinaryDegree4 D.facetExponent = 2 := by
          simp [ordinaryDegree4, hn0, hn1, hn2, hn3, hnOne]
        have hfarDeg : 3 ≤ ordinaryDegree4 R.exponent := by
          unfold ordinaryDegree4
          rw [hr2]
          omega
        omega
      · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
        have h := hidx
        rw [P.rho_eq, hF] at h
        simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
          facetOmittedCoordinate, hn0, hn1, hn2, hn3] at h

/-- **Positive first-contact bump excludes an ordinary-degree-preserving
affine RR direction.**

The terminal affine line has literal far and near endpoints.  A zero sum of
its affine direction would give those endpoints the same ordinary degree.
But both lie on the same positive-bump contact face, with contact coordinate
zero at the near endpoint and strictly positive at the far endpoint; hence
the far endpoint has strictly smaller ordinary degree. -/
theorem affineDirection_sum_ne_zero
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    {contactScale contactBump : ℕ} {contactLevel : ℤ}
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    (1 : K) + P.q + P.r + P.s ≠ 0 := by
  intro hsum
  let far := Finsupp.mapDomain P.rho R.exponent
  let near := Finsupp.mapDomain P.rho D.facetExponent
  have hfarMem :
      far ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨R.exponent, R.mem_face, rfl⟩
  have hnearMem :
      near ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨D.facetExponent, D.facet_mem_face, rfl⟩

  have hdegree :
      ∀ e ∈ (MvPolynomial.rename P.rho D.face).support,
        ordinaryDegree4 e = P.A + P.B + P.C := by
    intro e he
    have haff := P.support.affine e he
    have h0 := congrFun haff (0 : Fin 4)
    have h1 := congrFun haff (1 : Fin 4)
    have h2 := congrFun haff (2 : Fin 4)
    have h3 := congrFun haff (3 : Fin 4)
    simp [rankThreeLogBaseExponent, rankThreeLogDirection] at h0 h1 h2 h3
    have hdegK :
        ((ordinaryDegree4 e : ℕ) : K) =
          ((P.A + P.B + P.C : ℕ) : K) := by
      unfold ordinaryDegree4
      push_cast
      linear_combination h1 + h2 + h3 +
        (e (0 : Fin 4) : K) * hsum
    exact_mod_cast hdegK

  have hfarDeg := hdegree far hfarMem
  have hnearDeg := hdegree near hnearMem
  have hpermFar := P.ordinaryDegree4_mapDomain_rho R.exponent
  have hpermNear := P.ordinaryDegree4_mapDomain_rho D.facetExponent
  have hdegEq :
      ordinaryDegree4 R.exponent = ordinaryDegree4 D.facetExponent := by
    dsimp [far] at hfarDeg
    dsimp [near] at hnearDeg
    rw [hpermFar] at hfarDeg
    rw [hpermNear] at hnearDeg
    omega

  have hlt :=
    P.far_ordinaryDegree_lt_near
      hcontactScale hcontactBump hcontact
  exact (Nat.ne_of_lt hlt) hdegEq

/-- The extracted affine coefficient profile has degree exactly the reoriented
near-end coordinate.  Thus the original near endpoint is the terminal top
index, not merely some positive coefficient layer. -/
theorem profile_natDegree_eq_nearIndex
    (P : CrossFacetFarRankThreeAffineSupportData D R) :
    P.support.coefficientProfile.natDegree =
      (Finsupp.mapDomain P.rho D.facetExponent) (0 : Fin 4) := by
  let near := Finsupp.mapDomain P.rho D.facetExponent
  have hnearMem :
      near ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨D.facetExponent, D.facet_mem_face, rfl⟩
  have hprofileMem :
      near (0 : Fin 4) ∈ P.support.coefficientProfile.support :=
    P.support.coefficientProfile_mem_of_mem hnearMem
  have hle :
      near (0 : Fin 4) ≤ P.support.coefficientProfile.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hprofileMem
  have hge :
      P.support.coefficientProfile.natDegree ≤ near (0 : Fin 4) := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_contra hcoeff
    have hnmem : n ∈ P.support.coefficientProfile.support :=
      Polynomial.mem_support_iff.mpr hcoeff
    rcases P.support.exists_exponent_of_coefficientProfile_mem hnmem with
      ⟨e, he, he0⟩
    have hmax :
        e (0 : Fin 4) ≤ near (0 : Fin 4) := by
      simpa [near] using P.nearIndex_max e he
    have hnearn :
        near (0 : Fin 4) < n := by
      simpa [near] using hn
    rw [he0] at hmax
    omega
  simpa [near] using Nat.le_antisymm hge hle

/-- The affine support representation retains the original near endpoint
as its literal top exponent. -/
theorem affineLineData_topExponent_eq_near
    (P : CrossFacetFarRankThreeAffineSupportData D R) :
    P.support.affineLineData.exponent
        P.support.coefficientProfile.natDegree =
      Finsupp.mapDomain P.rho D.facetExponent := by
  let near := Finsupp.mapDomain P.rho D.facetExponent
  have hnearMem :
      near ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨D.facetExponent, D.facet_mem_face, rfl⟩
  have hprofileMem :
      near (0 : Fin 4) ∈ P.support.coefficientProfile.support :=
    P.support.coefficientProfile_mem_of_mem hnearMem
  have hdeg :
      P.support.coefficientProfile.natDegree = near (0 : Fin 4) := by
    simpa [near] using P.profile_natDegree_eq_nearIndex
  have htopMem :
      P.support.coefficientProfile.natDegree ∈
        P.support.coefficientProfile.support := by
    simpa [hdeg] using hprofileMem
  have hspec := P.support.exponentAt_spec htopMem
  have hzero :
      P.support.affineLineData.exponent
          P.support.coefficientProfile.natDegree (0 : Fin 4) =
        near (0 : Fin 4) := by
    change
      P.support.exponentAt P.support.coefficientProfile.natDegree
          (0 : Fin 4) =
        near (0 : Fin 4)
    rw [hspec.2, hdeg]
  have heq :=
    P.support.eq_of_zeroCoordinate_eq hspec.1 hnearMem hzero
  simpa [near, RankThreeAffineSupportData.affineLineData] using heq

/-- The affine terminal top exponent is already codimension two in the
actual first-contact geometry.  The coefficient-profile top exponent is
literally the reoriented near q/s ray, and that ray has two zero transverse
coordinates. -/
theorem affineLineData_topExponent_codimensionTwo
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (ha : 0 < a) (hb : 0 < b)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    HC4.Newton.MvExponentOnCodimensionTwoBoundary
      (P.support.affineLineData.exponent
        P.support.coefficientProfile.natDegree) := by
  rw [P.affineLineData_topExponent_eq_near]
  rcases P.nearExtreme_topShape ha hb hnear with h23 | h13 | h12
  · exact ⟨(2 : Fin 4), (3 : Fin 4), by decide, h23.2.1, h23.2.2⟩
  · exact ⟨(1 : Fin 4), (3 : Fin 4), by decide, h13.1, h13.2.2⟩
  · exact ⟨(1 : Fin 4), (2 : Fin 4), by decide, h12.1, h12.2.1⟩

set_option maxHeartbeats 4000000 in
/-- A reoriented far-rank-three support package already reaches the mature
affine RationalRigidity terminal certificate as soon as the child face is
Hessian-singular. -/
theorem terminalCertificate
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (hzero : HC4.Polynomial.hessianDeterminant D.face = 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := P.support.coefficientProfile)
      (P.A : K) (P.B : K) (P.C : K) (1 : K)
      P.q P.r P.s := by
  let far := Finsupp.mapDomain P.rho R.exponent
  let near := Finsupp.mapDomain P.rho D.facetExponent

  have hfarMem :
      far ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨R.exponent, R.mem_face, rfl⟩
  have hnearMem :
      near ∈ (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨D.facetExponent, D.facet_mem_face, rfl⟩

  have hphi0 : P.support.coefficientProfile.coeff 0 ≠ 0 := by
    apply P.support.coeff_zero_ne_zero_of_mem_zero hfarMem
    simpa [far] using P.farIndex_zero

  have hphiDeg : 0 < P.support.coefficientProfile.natDegree := by
    rw [P.profile_natDegree_eq_nearIndex]
    simpa [near] using P.nearIndex_pos

  have hcarrierZero :
      HC4.Polynomial.hessianDeterminant
          (MvPolynomial.rename P.rho D.face) = 0 := by
    rw [HC4.Newton.hessianDeterminant_rename_perm, hzero]
    simp

  have hlineZero :
      HC4.Polynomial.hessianDeterminant
          P.support.affineLineData.polynomial = 0 := by
    rw [P.support.affineLineData_polynomial_eq]
    exact hcarrierZero

  exact hasRankThreePolynomialTerminalCertificate_of_affine_line
    P.support.affineLineData
    P.A_pos P.B_pos P.C_pos (by norm_num)
    hphiDeg hphi0 hlineZero

set_option maxHeartbeats 4000000 in
/-- The same data reaches the complete affine terminal binomial normal
form while retaining the source-honest exponent representation above. -/
noncomputable def binomialNormalForm
    (P : CrossFacetFarRankThreeAffineSupportData D R)
    (hzero : HC4.Polynomial.hessianDeterminant D.face = 0) :
    RankThreeTerminalBinomialNormalForm P.support.affineLineData := by
  have hfarMem :
      Finsupp.mapDomain P.rho R.exponent ∈
        (MvPolynomial.rename P.rho D.face).support := by
    rw [MvPolynomial.support_rename_of_injective P.rho.injective]
    exact Finset.mem_image.mpr ⟨R.exponent, R.mem_face, rfl⟩
  have hphi0 : P.support.coefficientProfile.coeff 0 ≠ 0 :=
    P.support.coeff_zero_ne_zero_of_mem_zero hfarMem P.farIndex_zero
  have hphiDeg : 0 < P.support.coefficientProfile.natDegree := by
    rw [P.profile_natDegree_eq_nearIndex]
    exact P.nearIndex_pos
  have hcarrierZero :
      HC4.Polynomial.hessianDeterminant
          (MvPolynomial.rename P.rho D.face) = 0 := by
    rw [HC4.Newton.hessianDeterminant_rename_perm, hzero]
    simp
  have hlineZero :
      HC4.Polynomial.hessianDeterminant
          P.support.affineLineData.polynomial = 0 := by
    rw [P.support.affineLineData_polynomial_eq]
    exact hcarrierZero
  exact rankThreeTerminal_binomialNormalForm
    P.support.affineLineData
    P.A_pos P.B_pos P.C_pos (by norm_num)
    hphiDeg hphi0 hlineZero

end CrossFacetFarRankThreeAffineSupportData

/-- **Terminal far first-contact = codimension-two affine RR terminal or
literal kernel.**

This strengthens the certificate/kernel splice by retaining the exact
geometric fact already proved above: in the genuine first-contact branch the
top exponent of the affine RR profile is literally the reoriented near q/s
ray, hence is codimension two.  Downstream consumers therefore receive the
terminal certificate and its actual codimension-two top endpoint together. -/
theorem CrossFacetFarBoundaryData.affineTerminalCodimensionTwo_or_kernel
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
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    (∃ P : CrossFacetFarRankThreeAffineSupportData D R,
        HasRankThreePolynomialTerminalCertificate
          (phi := P.support.coefficientProfile)
          (P.A : K) (P.B : K) (P.C : K) (1 : K)
          P.q P.r P.s ∧
        HC4.Newton.MvExponentOnCodimensionTwoBoundary
          (P.support.affineLineData.exponent
            P.support.coefficientProfile.natDegree)) ∨
      ∃ kernelCoordinate : Fin 4,
        MvPolynomial.pderiv kernelCoordinate D.face = 0 := by
  cases R.terminalRankThree_or_kernel
      ha hb hcop hcontactScale D hBal hcontact hzero hnear with
  | rankThree F hthree hnearPos =>
      rcases R.exists_rankThreeAffineSupportData
          ha hb hcontactScale D hBal hcontact R F hthree hnearPos with
        ⟨P⟩
      left
      refine ⟨P, ?_, ?_⟩
      · exact P.terminalCertificate (D.hessian_zero hzero)
      · exact P.affineLineData_topExponent_codimensionTwo ha hb hnear
  | kernel kernelCoordinate hkernel =>
      exact Or.inr ⟨kernelCoordinate, hkernel⟩

/-- **Positive-bump far first-contact has a literal coordinate kernel.**

The affine branch of `affineTerminalCodimensionTwo_or_kernel` is now
impossible.  Its terminal profile has positive degree, cannot have degree one,
cannot preserve ordinary degree because the contact bump is positive, and has
a literal codimension-two top exponent.  The carrier-independent affine RR
contradiction therefore eliminates it.  Hence only the exact child-face kernel
branch survives. -/
theorem CrossFacetFarBoundaryData.kernel_of_positiveFirstContact
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant G = 0)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    ∃ kernelCoordinate : Fin 4,
      MvPolynomial.pderiv kernelCoordinate D.face = 0 := by
  rcases R.affineTerminalCodimensionTwo_or_kernel
      ha hb hcop hcontactScale D hBal hcontact hzero hnear with
    hterminal | hkernel
  · rcases hterminal with ⟨P, hcert, hcodim⟩
    have hfarMem :
        Finsupp.mapDomain P.rho R.exponent ∈
          (MvPolynomial.rename P.rho D.face).support := by
      rw [MvPolynomial.support_rename_of_injective P.rho.injective]
      exact Finset.mem_image.mpr ⟨R.exponent, R.mem_face, rfl⟩
    have hphi0 : P.support.coefficientProfile.coeff 0 ≠ 0 :=
      P.support.coeff_zero_ne_zero_of_mem_zero hfarMem P.farIndex_zero
    have hphiDeg : 0 < P.support.coefficientProfile.natDegree := by
      rw [P.profile_natDegree_eq_nearIndex]
      exact P.nearIndex_pos
    have hdegOne :
        P.support.coefficientProfile.natDegree ≠ 1 :=
      P.profile_natDegree_ne_one
        ha hb hcontactScale hcontactBump hBal hcontact hnear
    have hsum_ne : (1 : K) + P.q + P.r + P.s ≠ 0 :=
      P.affineDirection_sum_ne_zero
        hcontactScale hcontactBump hcontact
    exact False.elim
      (rankThree_affineTerminal_codimensionTwoTop_impossible
        (K := K) P.support.affineLineData
        P.A_pos P.B_pos P.C_pos hphiDeg hphi0 hcert
        hdegOne hsum_ne hcodim)
  · exact hkernel

/-- **Rooted positive first-contact kernel theorem.**

Starting from the actual strict-low/non-facet `.qs` source contact, retain the
exact initial form, the exact secondary face, the actual far endpoint, and the
literal coordinate kernel forced by the completed affine RR elimination. -/
theorem exists_qs_firstNonfacet_crossFacet_childKernel
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
      MvPolynomial.pderiv kernelCoordinate D.face = 0 := by
  rcases exists_qs_firstNonfacet_crossFacet_extremeRay_nonlinear
      ha hb hcop hm hdeg htop hattained hout hlow hBal hMA with
    ⟨d₀, scale, bump, G, hG, hd₀G, hd₀deg, hscale, hbump,
      hzero, hnot, hGBal, hnonlinear, D, H, hAdj, hRay⟩
  have hsupports := firstContactCarrier_crossFacet_supports
    (F := .qs) (m := m) (scale := scale) (bump := bump)
    htop hattained hG hnot
  have hcontact :
      ∀ d ∈ G.support,
        scaledContactExponentWeight (0 : Fin 4) scale bump d =
          ((scale * m : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using hsupports.2.2
  have hfacetDeg : 3 ≤ ordinaryDegree4 D.facetExponent :=
    hnonlinear D.facetExponent (D.support_subset D.facet_mem_face)
  have hnear :=
    D.qs_extremeRay_facet_coordinates_pos hAdj hRay hfacetDeg
  let R : CrossFacetFarBoundaryData (a := a) (b := b) D :=
    D.farBoundaryData
      ha hb hcop hscale hGBal hcontact hzero hnonlinear
  rcases R.kernel_of_positiveFirstContact
      ha hb hcop hscale hbump D hGBal hcontact hzero hnear with
    ⟨kernelCoordinate, hkernel⟩
  exact ⟨scale, bump, G, D, R, kernelCoordinate,
    hG, hscale, hbump, hzero, hGBal, hnonlinear, hkernel⟩

/-- **Terminal far first-contact = affine RR certificate or literal kernel.**

This is the direct splice between the strengthened Newton far-boundary
classifier and the mature affine RationalRigidity stack.  A genuinely
transverse far rank-three point reconstructs an honest affine support line and
therefore carries the polynomial terminal certificate.  The only alternative
is that the exact child face already has a coordinate kernel. -/
theorem CrossFacetFarBoundaryData.affineTerminalCertificate_or_kernel
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
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    (∃ P : CrossFacetFarRankThreeAffineSupportData D R,
        HasRankThreePolynomialTerminalCertificate
          (phi := P.support.coefficientProfile)
          (P.A : K) (P.B : K) (P.C : K) (1 : K)
          P.q P.r P.s) ∨
      ∃ kernelCoordinate : Fin 4,
        MvPolynomial.pderiv kernelCoordinate D.face = 0 := by
  cases R.terminalRankThree_or_kernel
      ha hb hcop hcontactScale D hBal hcontact hzero hnear with
  | rankThree F hthree hnearPos =>
      rcases R.exists_rankThreeAffineSupportData
          ha hb hcontactScale D hBal hcontact R F hthree hnearPos with
        ⟨P⟩
      left
      refine ⟨P, ?_⟩
      exact P.terminalCertificate (D.hessian_zero hzero)
  | kernel kernelCoordinate hkernel =>
      exact Or.inr ⟨kernelCoordinate, hkernel⟩

end

end HC4.RationalRigidity
