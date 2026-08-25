import HC4.Newton.FirstContactCrossFacetAffineRRFiniteSplit
import Mathlib.Tactic

/-!
# A18.5.68c: the rank-three cross-facet terminal exits through `pr`

The exact affine RR reduction leaves four possibilities after degree one is
removed.  The genuine first-contact construction supplies one extra piece of
provenance that is deliberately retained here: the bumped contact weight has
strictly positive bump.

That positivity makes the ordinary degree strictly decrease from the selected
facet exponent to the selected outside exponent.  Consequently the
ordinary-degree-preserving affine direction is impossible.  Two of the three
remaining double-zero slope patterns force the outside ordinary degree to
increase by toric balance, so they are impossible as well.  The unique
surviving pattern fixes coordinates `2` and `3`.

The mature terminal boundary theorem then forces the far supported exponent to
vanish in coordinate `1`; coordinates `0`, `2`, and `3` are positive.  Thus a
rank-three point on the `qs` facet does not terminate: it canonically crosses
to a rank-three point on the adjacent `pr` facet.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A genuine positive-bump first contact strictly lowers ordinary degree from
the chosen facet exponent to the chosen outside exponent. -/
theorem CrossFacetInitialData.qs_outside_ordinaryDegree_lt_facet
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    ordinaryDegree4 D.outsideExponent < ordinaryDegree4 D.facetExponent := by
  have hout := hcontact D.outsideExponent D.outside_mem
  have hfacet := hcontact D.facetExponent D.facet_mem
  have heq :
      scaledContactExponentWeight (0 : Fin 4)
          contactScale contactBump D.outsideExponent =
        scaledContactExponentWeight (0 : Fin 4)
          contactScale contactBump D.facetExponent :=
    hout.trans hfacet.symm
  unfold scaledContactExponentWeight at heq
  rw [D.facet_coordinate_zero] at heq
  simp only [Nat.cast_zero, Int.ofNat_eq_coe, mul_zero, add_zero] at heq
  have hs : (0 : ℤ) < (contactScale : ℤ) := by exact_mod_cast hcontactScale
  have hb : (0 : ℤ) < (contactBump : ℤ) := by exact_mod_cast hcontactBump
  have ho : (0 : ℤ) < (D.outsideExponent (0 : Fin 4) : ℤ) := by
    exact_mod_cast D.outside_coordinate_pos
  have hltZ :
      (ordinaryDegree4 D.outsideExponent : ℤ) <
        (ordinaryDegree4 D.facetExponent : ℤ) := by
    nlinarith
  exact_mod_cast hltZ

/-- A zero affine slope fixes that transverse coordinate on the whole exact
cross-facet face. -/
theorem CrossFacetInitialData.qs_support_coordinate_eq_facet_of_slope_zero
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    {k : Fin 4}
    (hslope : D.qsSlope k = 0)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    d k = D.facetExponent k := by
  have hdenK : (((D.outsideExponent (0 : Fin 4) : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.outside_coordinate_pos)
  have hnumK :
      ((((D.outsideExponent k : ℤ) - (D.facetExponent k : ℤ) : ℤ)) : K) = 0 := by
    have hs := hslope
    simp [CrossFacetInitialData.qsSlope, hdenK] at hs
    exact hs
  have hnumZ :
      (D.outsideExponent k : ℤ) - (D.facetExponent k : ℤ) = 0 := by
    exact_mod_cast hnumK
  have houtEqZ :
      (D.outsideExponent k : ℤ) = (D.facetExponent k : ℤ) :=
    sub_eq_zero.mp hnumZ
  have houtEq : D.outsideExponent k = D.facetExponent k := by
    exact_mod_cast houtEqZ
  have hline := D.support_crossFacet_affine_proportional
    ha hb hcontactScale hBal hcontact d hd k
  have hfacet0Z : (D.facetExponent (0 : Fin 4) : ℤ) = 0 := by
    exact_mod_cast D.facet_coordinate_zero
  have houtEqZ' : (D.outsideExponent k : ℤ) =
      (D.facetExponent k : ℤ) := by exact_mod_cast houtEq
  rw [hfacet0Z, houtEqZ'] at hline
  simp only [sub_zero, sub_self, mul_zero] at hline
  have hout0Z : (D.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.outside_coordinate_pos)
  have hdiff : (d k : ℤ) - (D.facetExponent k : ℤ) = 0 :=
    (mul_eq_zero.mp hline).resolve_left hout0Z
  have hdkZ : (d k : ℤ) = (D.facetExponent k : ℤ) := sub_eq_zero.mp hdiff
  exact_mod_cast hdkZ

/-- Ordinary-degree preservation of the affine RR direction would make the
selected outside exponent have the same ordinary degree as the facet exponent. -/
theorem CrossFacetInitialData.qs_outside_ordinaryDegree_eq_facet_of_direction_sum_zero
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hsum :
      1 + D.qsSlope (1 : Fin 4) + D.qsSlope (2 : Fin 4) +
        D.qsSlope (3 : Fin 4) = 0) :
    ordinaryDegree4 D.outsideExponent = ordinaryDegree4 D.facetExponent := by
  have haff := D.qs_support_affine
    ha hb hcontactScale hBal hcontact D.outside_mem_face
  have h1 := congrFun haff (1 : Fin 4)
  have h2 := congrFun haff (2 : Fin 4)
  have h3 := congrFun haff (3 : Fin 4)
  simp [rankThreeLogBaseExponent, rankThreeLogDirection] at h1 h2 h3
  have hdegK :
      ((ordinaryDegree4 D.outsideExponent : ℕ) : K) =
        ((ordinaryDegree4 D.facetExponent : ℕ) : K) := by
    simp only [ordinaryDegree4]
    push_cast
    rw [D.facet_coordinate_zero]
    norm_num
    linear_combination
      h1 + h2 + h3 +
        ((D.outsideExponent (0 : Fin 4) : ℕ) : K) * hsum
  exact_mod_cast hdegK

/-- **Canonical rank-three first-contact transition.**

With the genuine positive first-contact bump, the refined affine terminal split
collapses to the unique direction fixing coordinates `2` and `3`.  The far
supported exponent is therefore rank three on `pr`. -/
theorem CrossFacetInitialData.qs_rankThree_terminal_transition_pr
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
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
    let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
    D.qsSlope (2 : Fin 4) = 0 ∧
      D.qsSlope (3 : Fin 4) = 0 ∧
      MvRankThreeOnFacet .pr
        (L.exponent D.qsCoefficientPolynomial.natDegree) := by
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hdegLt := D.qs_outside_ordinaryDegree_lt_facet
    hcontactScale hcontactBump hcontact
  have hsplit := D.qs_rankThree_refinedTerminalSplit
    ha hb hcontactScale hBal hcontact hzero hthree

  have hRS :
      D.qsSlope (2 : Fin 4) = 0 ∧ D.qsSlope (3 : Fin 4) = 0 := by
    rcases hsplit with hQR | hQS | hRS | hhom
    · exfalso
      have h1fix := D.qs_support_coordinate_eq_facet_of_slope_zero
        ha hb hcontactScale hBal hcontact hQR.1 D.outside_mem_face
      have h2fix := D.qs_support_coordinate_eq_facet_of_slope_zero
        ha hb hcontactScale hBal hcontact hQR.2 D.outside_mem_face
      have hfacetBal := hBal D.facetExponent D.facet_mem
      have houtBal := hBal D.outsideExponent D.outside_mem
      simp only [IsBalancedExponent] at hfacetBal houtBal
      rw [D.facet_coordinate_zero, zero_mul, zero_add] at hfacetBal
      rw [h1fix, h2fix] at houtBal
      have hprod :
          (a * D.facetExponent (3 : Fin 4)) +
              a * D.outsideExponent (0 : Fin 4) =
            a * D.outsideExponent (3 : Fin 4) := by
        have htmp :
            b * D.facetExponent (2 : Fin 4) +
                (a * D.facetExponent (3 : Fin 4) +
                  a * D.outsideExponent (0 : Fin 4)) =
              b * D.facetExponent (2 : Fin 4) +
                a * D.outsideExponent (3 : Fin 4) := by
          calc
            _ = a * D.outsideExponent (0 : Fin 4) +
                (b * D.facetExponent (2 : Fin 4) +
                  a * D.facetExponent (3 : Fin 4)) := by ring
            _ = a * D.outsideExponent (0 : Fin 4) +
                b * D.facetExponent (1 : Fin 4) := by rw [← hfacetBal]
            _ = b * D.facetExponent (2 : Fin 4) +
                a * D.outsideExponent (3 : Fin 4) := by
              simpa [add_comm, add_left_comm, add_assoc] using houtBal
        exact Nat.add_left_cancel htmp
      have hpos : 0 < a * D.outsideExponent (0 : Fin 4) :=
        Nat.mul_pos ha D.outside_coordinate_pos
      have h3prodLt :
          a * D.facetExponent (3 : Fin 4) <
            a * D.outsideExponent (3 : Fin 4) := by omega
      have h3lt : D.facetExponent (3 : Fin 4) <
          D.outsideExponent (3 : Fin 4) :=
        (Nat.mul_lt_mul_left ha).mp h3prodLt
      have hdegGt : ordinaryDegree4 D.facetExponent <
          ordinaryDegree4 D.outsideExponent := by
        unfold ordinaryDegree4
        rw [D.facet_coordinate_zero, h1fix, h2fix]
        omega
      omega
    · exfalso
      have h1fix := D.qs_support_coordinate_eq_facet_of_slope_zero
        ha hb hcontactScale hBal hcontact hQS.1 D.outside_mem_face
      have h3fix := D.qs_support_coordinate_eq_facet_of_slope_zero
        ha hb hcontactScale hBal hcontact hQS.2 D.outside_mem_face
      have hfacetBal := hBal D.facetExponent D.facet_mem
      have houtBal := hBal D.outsideExponent D.outside_mem
      simp only [IsBalancedExponent] at hfacetBal houtBal
      rw [D.facet_coordinate_zero, zero_mul, zero_add] at hfacetBal
      rw [h1fix, h3fix] at houtBal
      have hprod :
          b * D.facetExponent (2 : Fin 4) +
              a * D.outsideExponent (0 : Fin 4) =
            b * D.outsideExponent (2 : Fin 4) := by
        have htmp :
            (b * D.facetExponent (2 : Fin 4) +
                a * D.outsideExponent (0 : Fin 4)) +
                a * D.facetExponent (3 : Fin 4) =
              b * D.outsideExponent (2 : Fin 4) +
                a * D.facetExponent (3 : Fin 4) := by
          calc
            _ = a * D.outsideExponent (0 : Fin 4) +
                (b * D.facetExponent (2 : Fin 4) +
                  a * D.facetExponent (3 : Fin 4)) := by ring
            _ = a * D.outsideExponent (0 : Fin 4) +
                b * D.facetExponent (1 : Fin 4) := by rw [← hfacetBal]
            _ = b * D.outsideExponent (2 : Fin 4) +
                a * D.facetExponent (3 : Fin 4) := by
              simpa [add_comm, add_left_comm, add_assoc] using houtBal
        exact Nat.add_right_cancel htmp
      have hpos : 0 < a * D.outsideExponent (0 : Fin 4) :=
        Nat.mul_pos ha D.outside_coordinate_pos
      have h2prodLt :
          b * D.facetExponent (2 : Fin 4) <
            b * D.outsideExponent (2 : Fin 4) := by omega
      have h2lt : D.facetExponent (2 : Fin 4) <
          D.outsideExponent (2 : Fin 4) :=
        (Nat.mul_lt_mul_left hb).mp h2prodLt
      have hdegGt : ordinaryDegree4 D.facetExponent <
          ordinaryDegree4 D.outsideExponent := by
        unfold ordinaryDegree4
        rw [D.facet_coordinate_zero, h1fix, h3fix]
        omega
      omega
    · exact hRS
    · exfalso
      have hdegEq :=
        D.qs_outside_ordinaryDegree_eq_facet_of_direction_sum_zero
          ha hb hcontactScale hBal hcontact hhom
      omega

  have htop := D.qs_rankThree_terminalTop_transverse_zero
    ha hb hcontactScale hBal hcontact hzero hthree
  have htopMem :
      L.exponent D.qsCoefficientPolynomial.natDegree ∈ D.face.support := by
    simpa [L] using
      (D.qsAffineLineData_top_mem_face_support
        ha hb hcontactScale hBal hcontact)
  have h2fix := D.qs_support_coordinate_eq_facet_of_slope_zero
    ha hb hcontactScale hBal hcontact hRS.1 htopMem
  have h3fix := D.qs_support_coordinate_eq_facet_of_slope_zero
    ha hb hcontactScale hBal hcontact hRS.2 htopMem
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hfacet0, _h1pos, h2pos, h3pos⟩
  have hdegPos : 0 < D.qsCoefficientPolynomial.natDegree :=
    D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
  have htop0pos :
      0 < L.exponent D.qsCoefficientPolynomial.natDegree (0 : Fin 4) := by
    rw [htop.1]
    exact hdegPos
  have htop2pos :
      0 < L.exponent D.qsCoefficientPolynomial.natDegree (2 : Fin 4) := by
    rw [h2fix]
    exact h2pos
  have htop3pos :
      0 < L.exponent D.qsCoefficientPolynomial.natDegree (3 : Fin 4) := by
    rw [h3fix]
    exact h3pos
  have htop1zero :
      L.exponent D.qsCoefficientPolynomial.natDegree (1 : Fin 4) = 0 := by
    rcases htop.2 with h1 | h2 | h3
    · exact h1
    · exact False.elim (Nat.ne_of_gt htop2pos h2)
    · exact False.elim (Nat.ne_of_gt htop3pos h3)
  refine ⟨hRS.1, hRS.2, ?_⟩
  exact (mvRankThreeOnFacet_iff .pr
    (L.exponent D.qsCoefficientPolynomial.natDegree)).2
      ⟨htop1zero, htop0pos, htop2pos, htop3pos⟩

end

end HC4.Newton
