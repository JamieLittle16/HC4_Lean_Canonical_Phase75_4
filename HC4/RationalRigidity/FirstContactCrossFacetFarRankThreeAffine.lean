import HC4.Newton.FirstContactCrossFacetFarBoundary
import HC4.Polynomial.RankThreeAffineSupportRealisation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
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
          ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    | qs =>
        have h0 := (mvRankThreeOnFacet_iff .qs R.exponent).1 hthree
        exact (Nat.ne_of_gt R.contact_pos h0.1).elim
    | sp =>
        have h := (mvRankThreeOnFacet_iff .sp R.exponent).1 hthree
        simpa [A, B, C, rho, f, facetOmittedCoordinate,
          Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne] using
          ⟨h.2.1, h.2.2.1, h.2.2.2⟩

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
  rw [P.rho_eq]
  cases hF : P.farFacet with
  | pr =>
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        exact Or.inr (Or.inl ⟨by
          simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate,
            h0, h1, h2, h3] using hn, by
          simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3],
          by simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]⟩)
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        right
        right
        refine ⟨?_, ?_, ?_⟩
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
          exact Nat.mul_pos (by
            have hpos := P.nearOmitted_pos
            rw [hF] at hpos
            simpa [facetOmittedCoordinate, h1] using hpos) hn
  | rq =>
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        have hpos := P.nearOmitted_pos
        rw [hF] at hpos
        simp [facetOmittedCoordinate, h3] at hpos
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        left
        refine ⟨?_, ?_, ?_⟩
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
          exact Nat.mul_pos (by
            have hpos := P.nearOmitted_pos
            rw [hF] at hpos
            simpa [facetOmittedCoordinate, h3] using hpos) hn
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
      rcases hnear with hq | hs
      · rcases hq with ⟨n, hn, h0, h1, h2, h3⟩
        left
        refine ⟨?_, ?_, ?_⟩
        · simpa [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate,
            h0, h1, h2, h3] using hn
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
        · simp [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne, facetOmittedCoordinate, h0, h1, h2, h3]
      · rcases hs with ⟨n, hn, h0, h1, h2, h3⟩
        have hpos := P.nearOmitted_pos
        rw [hF] at hpos
        simp [facetOmittedCoordinate, h2] at hpos

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
    have hmax := P.nearIndex_max e he
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
