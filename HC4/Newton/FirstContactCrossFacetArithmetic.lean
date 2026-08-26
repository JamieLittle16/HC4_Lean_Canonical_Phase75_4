import HC4.Newton.FirstContactCrossFacetAffineRRTransition
import Mathlib.Tactic

/-!
# A18.5.72: arithmetic collapse of the rank-three first-contact exit

A18.5.68c shows that the only surviving rank-three first-contact direction in
the canonical `qs` chart fixes transverse coordinates `2` and `3`.  The affine
RationalRigidity terminal also supplies a genuine first coefficient layer.

That first layer is an actual supported exponent with omitted coordinate one.
Toric balance at the initial `qs` exponent and at this first layer therefore
gives

    b * A = a + b * A₁.

Hence `b ∣ a`.  Under the primitive grading hypothesis `a.Coprime b`, this
forces `b = 1`.

This is a purely arithmetic consequence of already-certified support.  No
integral reparameterisation of the higher-degree affine line is used, so no
spurious divisibility assumption on the starting transverse exponents enters.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Rank-three first-contact arithmetic collapse.**

If the selected endpoint of the exact `qs` cross-facet face is rank three,
then the genuine first coefficient layer forced by the affine terminal makes
the lower grading weight divide the upper one.  Coprimality therefore forces
that lower weight to be one. -/
theorem CrossFacetInitialData.qs_rankThree_firstContact_forces_b_one
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs D.facetExponent) :
    b = 1 := by
  have htransition := D.qs_rankThree_terminal_transition_pr
    ha hb hcontactScale hcontactBump hBal hcontact hzero hthree
  have hslope2 : D.qsSlope (2 : Fin 4) = 0 := htransition.1
  have hslope3 : D.qsSlope (3 : Fin 4) = 0 := htransition.2.1

  have hphi1 : D.qsCoefficientPolynomial.coeff 1 ≠ 0 :=
    (D.qs_rankThree_binomialNormalForm
      ha hb hcontactScale hBal hcontact hzero hthree).first_coefficient_ne_zero
  have h1mem : 1 ∈ D.qsCoefficientPolynomial.support :=
    Polynomial.mem_support_iff.mpr hphi1
  rcases D.exists_faceExponent_of_qsCoefficientPolynomial_mem h1mem with
    ⟨e, heFace, he0⟩

  have he2 : e (2 : Fin 4) = D.facetExponent (2 : Fin 4) :=
    D.qs_support_coordinate_eq_facet_of_slope_zero
      ha hb hcontactScale hBal hcontact hslope2 heFace
  have he3 : e (3 : Fin 4) = D.facetExponent (3 : Fin 4) :=
    D.qs_support_coordinate_eq_facet_of_slope_zero
      ha hb hcontactScale hBal hcontact hslope3 heFace

  have hfacetBal : IsBalancedExponent a b D.facetExponent :=
    hBal D.facetExponent D.facet_mem
  have heBal : IsBalancedExponent a b e :=
    (D.balanced hBal) e heFace
  simp only [IsBalancedExponent] at hfacetBal heBal
  rw [D.facet_coordinate_zero] at hfacetBal
  simp only [mul_zero, zero_add] at hfacetBal
  rw [he0, he2, he3] at heBal
  simp only [mul_one] at heBal

  have hbalance :
      a + b * e (1 : Fin 4) =
        b * D.facetExponent (1 : Fin 4) := by
    calc
      a + b * e (1 : Fin 4) =
          b * D.facetExponent (2 : Fin 4) +
            a * D.facetExponent (3 : Fin 4) := heBal
      _ = b * D.facetExponent (1 : Fin 4) := hfacetBal.symm

  have he1le : e (1 : Fin 4) ≤ D.facetExponent (1 : Fin 4) := by
    have hmul :
        b * e (1 : Fin 4) ≤ b * D.facetExponent (1 : Fin 4) := by
      omega
    exact Nat.le_of_mul_le_mul_left hmul hb

  have hb_dvd_a : b ∣ a := by
    refine ⟨D.facetExponent (1 : Fin 4) - e (1 : Fin 4), ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega

  have hb_gcd : b ∣ Nat.gcd a b :=
    Nat.dvd_gcd hb_dvd_a (dvd_refl b)
  have hgcd : Nat.gcd a b = 1 := hcop
  rw [hgcd] at hb_gcd
  exact Nat.dvd_one.mp hb_gcd

end

end HC4.Newton