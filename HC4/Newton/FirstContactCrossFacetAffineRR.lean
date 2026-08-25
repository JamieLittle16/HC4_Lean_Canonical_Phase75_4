import HC4.Newton.FirstContactCrossFacetEndpointStratum
import HC4.Polynomial.RankThreeAffineLineRealisation
import Mathlib.Tactic

/-!
# A18.5.67a: canonical cross-facet support as affine RR data

A18.5.65d proves that the exact cross-facet face is an honest affine line, and
A18.5.66 identifies the rank-three endpoint stratum.  The mature
RationalRigidity stack uses `RankThreeAffineLineData` in the canonical `qs`
chart, so this file performs the remaining support reindexing without imposing
the old finite-segment divisibility condition.

The key observation is that the omitted coordinate itself is already a
primitive parameter: index a supported exponent `d` by the literal natural
number `d 0` and take the RR omitted-coordinate step to be `1`.  A18.5.65d
proves that this coordinate is injective on support, so the coefficient
polynomial obtained by sending the monomial at `d` to degree `d 0` loses no
coefficient information.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The univariate coefficient polynomial obtained by indexing the canonical
`qs` cross-facet face by its omitted coordinate. -/
noncomputable def CrossFacetInitialData.qsCoefficientPolynomial
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4)) : Polynomial K :=
  ∑ d in D.face.support,
    Polynomial.monomial (d (0 : Fin 4)) (MvPolynomial.coeff d D.face)

/-- On the recognised cross-facet line, equal omitted coordinates force equal
actual support exponents. -/
theorem CrossFacetInitialData.qs_support_eq_of_zeroCoordinate_eq
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
    {p q : Fin 4 →₀ ℕ}
    (hp : p ∈ D.face.support) (hq : q ∈ D.face.support)
    (hpq : p (0 : Fin 4) = q (0 : Fin 4)) :
    p = q := by
  exact D.support_eq_of_contactCoordinate_eq
    ha hb hcontactScale hBal hcontact hp hq hpq

/-- A genuine multivariate support coefficient is retained literally at the
corresponding omitted-coordinate degree of the coefficient polynomial. -/
theorem CrossFacetInitialData.coeff_qsCoefficientPolynomial_of_mem
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
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    D.qsCoefficientPolynomial.coeff (d (0 : Fin 4)) =
      MvPolynomial.coeff d D.face := by
  classical
  unfold CrossFacetInitialData.qsCoefficientPolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single d]
  · simp [Polynomial.coeff_monomial]
  · intro q hq hqd
    have hq0 : q (0 : Fin 4) ≠ d (0 : Fin 4) := by
      intro h0
      apply hqd
      exact D.qs_support_eq_of_zeroCoordinate_eq
        ha hb hcontactScale hBal hcontact hq hd h0
    simp [Polynomial.coeff_monomial, hq0]
  · intro hnot
    exact (hnot hd).elim

/-- Every genuine face exponent gives a genuine coefficient-polynomial support
index. -/
theorem CrossFacetInitialData.qsCoefficientPolynomial_mem_of_face_mem
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
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    d (0 : Fin 4) ∈ D.qsCoefficientPolynomial.support := by
  rw [Polynomial.mem_support_iff]
  rw [D.coeff_qsCoefficientPolynomial_of_mem
    ha hb hcontactScale hBal hcontact hd]
  exact MvPolynomial.mem_support_iff.mp hd

/-- Conversely, every supported coefficient index is realised by an actual
face exponent with that omitted coordinate.  No injectivity is needed for this
direction; nonzero coefficient already forces at least one contributing
monomial. -/
theorem CrossFacetInitialData.exists_faceExponent_of_qsCoefficientPolynomial_mem
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4))
    {n : ℕ} (hn : n ∈ D.qsCoefficientPolynomial.support) :
    ∃ d ∈ D.face.support, d (0 : Fin 4) = n := by
  classical
  rw [Polynomial.mem_support_iff] at hn
  by_contra hnone
  push_neg at hnone
  unfold CrossFacetInitialData.qsCoefficientPolynomial at hn
  rw [Polynomial.finset_sum_coeff] at hn
  apply hn
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d (0 : Fin 4) ≠ n := hnone d hd
  simp [Polynomial.coeff_monomial, hdn, Ne.symm hdn]

/-- Canonical actual exponent attached to one univariate index.  Only indices
in the coefficient-polynomial support are used downstream; the fallback value
outside that support is irrelevant. -/
noncomputable def CrossFacetInitialData.qsExponentAt
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4))
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if h : ∃ d ∈ D.face.support, d (0 : Fin 4) = n then
    Classical.choose h
  else
    D.facetExponent

/-- The chosen exponent really is a face exponent with the requested omitted
coordinate whenever such an exponent exists. -/
theorem CrossFacetInitialData.qsExponentAt_spec
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4))
    {n : ℕ}
    (h : ∃ d ∈ D.face.support, d (0 : Fin 4) = n) :
    D.qsExponentAt n ∈ D.face.support ∧
      D.qsExponentAt n (0 : Fin 4) = n := by
  rw [CrossFacetInitialData.qsExponentAt]
  split
  · exact Classical.choose_spec h
  · rename_i hnone
    exact (hnone h).elim

/-- On a genuine support exponent, the canonical reindexing returns that very
exponent. -/
theorem CrossFacetInitialData.qsExponentAt_eq_of_face_mem
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
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    D.qsExponentAt (d (0 : Fin 4)) = d := by
  have hex : ∃ q ∈ D.face.support,
      q (0 : Fin 4) = d (0 : Fin 4) := ⟨d, hd, rfl⟩
  have hs := D.qsExponentAt_spec hex
  exact D.qs_support_eq_of_zeroCoordinate_eq
    ha hb hcontactScale hBal hcontact hs.1 hd hs.2

/-- Transverse affine slope of the recognised line in the canonical RR chart.
It is allowed to be negative in the coefficient field. -/
noncomputable def CrossFacetInitialData.qsSlope
    {F : MvPolynomial (Fin 4) K} {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4))
    (k : Fin 4) : K :=
  (((D.outsideExponent k : ℤ) - (D.facetExponent k : ℤ) : ℤ) : K) /
    ((D.outsideExponent (0 : Fin 4) : ℕ) : K)

/-- Every supported face exponent has exactly the affine RR exponent formula
when indexed by its literal omitted coordinate. -/
theorem CrossFacetInitialData.qs_support_affine
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
    {d : Fin 4 →₀ ℕ} (hd : d ∈ D.face.support) :
    (fun k : Fin 4 => ((d k : ℕ) : K)) =
      fun k =>
        rankThreeLogBaseExponent
            ((D.facetExponent 1 : ℕ) : K)
            ((D.facetExponent 2 : ℕ) : K)
            ((D.facetExponent 3 : ℕ) : K) k +
          ((d (0 : Fin 4) : ℕ) : K) *
            rankThreeLogDirection
              (1 : K)
              (D.qsSlope (1 : Fin 4))
              (D.qsSlope (2 : Fin 4))
              (D.qsSlope (3 : Fin 4)) k := by
  funext k
  have hline := D.support_crossFacet_affine_proportional
    ha hb hcontactScale hBal hcontact d hd k
  have hlineK := congrArg (fun z : ℤ => (z : K)) hline
  push_cast at hlineK
  have hden : ((D.outsideExponent (0 : Fin 4) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.outside_coordinate_pos)
  have hv0 : D.facetExponent (0 : Fin 4) = 0 := D.facet_coordinate_zero
  fin_cases k
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection, hv0]
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetInitialData.qsSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetInitialData.qsSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetInitialData.qsSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK

/-- **Canonical affine RR realisation of the exact cross-facet support.**

The omitted-coordinate step is literally one.  The endpoint exponents provide
the three positive base coordinates in the rank-three branch, while the
transverse direction is allowed to live in the coefficient field exactly as
required by `RankThreeAffineLineData`. -/
noncomputable def CrossFacetInitialData.qsAffineLineData
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    RankThreeAffineLineData
      (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3) 1
      (D.qsSlope (1 : Fin 4))
      (D.qsSlope (2 : Fin 4))
      (D.qsSlope (3 : Fin 4))
      D.qsCoefficientPolynomial where
  exponent := D.qsExponentAt
  affine := by
    intro n hn
    rcases D.exists_faceExponent_of_qsCoefficientPolynomial_mem hn with
      ⟨d, hd, hdn⟩
    subst n
    rw [D.qsExponentAt_eq_of_face_mem
      ha hb hcontactScale hBal hcontact hd]
    exact D.qs_support_affine
      ha hb hcontactScale hBal hcontact hd

/-- The facet coefficient becomes the literal constant coefficient of the RR
coefficient polynomial. -/
theorem CrossFacetInitialData.qsCoefficientPolynomial_coeff_zero_ne
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    D.qsCoefficientPolynomial.coeff 0 ≠ 0 := by
  have hcoeff := D.coeff_qsCoefficientPolynomial_of_mem
    ha hb hcontactScale hBal hcontact D.facet_mem_face
  rw [D.facet_coordinate_zero] at hcoeff
  rw [hcoeff]
  exact MvPolynomial.mem_support_iff.mp D.facet_mem_face

/-- The certified outside exponent gives a positive supported univariate index,
so the RR coefficient polynomial is genuinely nonconstant. -/
theorem CrossFacetInitialData.qsCoefficientPolynomial_natDegree_pos
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    0 < D.qsCoefficientPolynomial.natDegree := by
  have hout := D.qsCoefficientPolynomial_mem_of_face_mem
    ha hb hcontactScale hBal hcontact D.outside_mem_face
  have hle := Polynomial.le_natDegree_of_mem_supp
    (D.outsideExponent (0 : Fin 4)) hout
  exact lt_of_lt_of_le D.outside_coordinate_pos hle

end

end HC4.Newton
