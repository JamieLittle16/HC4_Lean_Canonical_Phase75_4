import HC4.Newton.FirstContactCrossFacetFarBoundary
import HC4.Polynomial.RankThreeAffineSupportRealisation
import HC4.RationalRigidity.RankThreeAffineLineTerminal
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
  rho : Equiv.Perm (Fin 4)
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
    rho := rho
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
  }⟩

end

end HC4.RationalRigidity
