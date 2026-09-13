import HC4.Newton.FiniteSupportCrossFacetRay
import HC4.Polynomial.RankThreeAffineLineRealisation
import Mathlib.Tactic

/-!
# A19.69: exact affine-RR realisation of a balance-free cross-facet ray

A19.67 produces an actual finite support ray without torus balance.  In the
canonical contact chart `j = 0`, the omitted coordinate itself is an honest
index: the affine proportionality relation makes coordinate `0` injective on
ray support.  Reindexing by that literal exponent therefore retains every
coefficient exactly.

The resulting `RankThreeAffineLineData` has omitted-coordinate step one and
arbitrary field-valued transverse slopes, exactly as required by the mature
affine RationalRigidity core.  No integrality of the transverse direction and
no torus grading are introduced.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficient polynomial obtained by indexing a balance-free ray by its
literal coordinate-`0` exponent. -/
noncomputable def CrossFacetRayData.zeroCoefficientPolynomial
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4)) : Polynomial K :=
  R.face.support.sum fun d =>
    Polynomial.monomial (d (0 : Fin 4)) (MvPolynomial.coeff d R.face)

/-- Coordinate `0` is injective on support of a genuine balance-free ray. -/
theorem CrossFacetRayData.support_eq_of_zeroCoordinate_eq
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {p q : Fin 4 →₀ ℕ}
    (hp : p ∈ R.face.support) (hq : q ∈ R.face.support)
    (hpq : p (0 : Fin 4) = q (0 : Fin 4)) :
    p = q := by
  apply Finsupp.ext
  intro k
  have hpLine := R.affine_proportional p hp k
  have hqLine := R.affine_proportional q hq k
  rw [hpq] at hpLine
  have hscaled :
      (R.outsideExponent (0 : Fin 4) : ℤ) *
        ((p k : ℤ) - (q k : ℤ)) = 0 := by
    linear_combination hpLine - hqLine
  have hout0 : (R.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt R.outside_coordinate_pos)
  have hdiff : (p k : ℤ) - (q k : ℤ) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hout0
  have heq : (p k : ℤ) = (q k : ℤ) := sub_eq_zero.mp hdiff
  exact_mod_cast heq

/-- A genuine ray coefficient is retained literally at its coordinate-`0`
index. -/
theorem CrossFacetRayData.coeff_zeroCoefficientPolynomial_of_mem
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ R.face.support) :
    R.zeroCoefficientPolynomial.coeff (d (0 : Fin 4)) =
      MvPolynomial.coeff d R.face := by
  classical
  unfold CrossFacetRayData.zeroCoefficientPolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single d]
  · simp [Polynomial.coeff_monomial]
  · intro q hq hqd
    have hq0 : q (0 : Fin 4) ≠ d (0 : Fin 4) := by
      intro h0
      apply hqd
      exact R.support_eq_of_zeroCoordinate_eq hq hd h0
    simp [Polynomial.coeff_monomial, hq0]
  · intro hnot
    exact (hnot hd).elim

/-- Every genuine ray exponent yields a supported univariate index. -/
theorem CrossFacetRayData.zeroCoefficientPolynomial_mem_of_face_mem
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ R.face.support) :
    d (0 : Fin 4) ∈ R.zeroCoefficientPolynomial.support := by
  rw [Polynomial.mem_support_iff]
  rw [R.coeff_zeroCoefficientPolynomial_of_mem hd]
  exact MvPolynomial.mem_support_iff.mp hd

/-- Conversely, every supported coefficient index comes from an actual ray
exponent with that coordinate-`0` value. -/
theorem CrossFacetRayData.exists_faceExponent_of_zeroCoefficientPolynomial_mem
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {n : ℕ} (hn : n ∈ R.zeroCoefficientPolynomial.support) :
    ∃ d ∈ R.face.support, d (0 : Fin 4) = n := by
  classical
  rw [Polynomial.mem_support_iff] at hn
  by_contra hnone
  push_neg at hnone
  unfold CrossFacetRayData.zeroCoefficientPolynomial at hn
  rw [Polynomial.finset_sum_coeff] at hn
  apply hn
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d (0 : Fin 4) ≠ n := hnone d hd
  simp [Polynomial.coeff_monomial, hdn, Ne.symm hdn]

/-- Canonical actual ray exponent attached to one univariate index. -/
noncomputable def CrossFacetRayData.zeroExponentAt
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (n : ℕ) : Fin 4 →₀ ℕ :=
  if h : ∃ d ∈ R.face.support, d (0 : Fin 4) = n then
    Classical.choose h
  else
    R.facetExponent

/-- The chosen index exponent is genuine support whenever such support exists. -/
theorem CrossFacetRayData.zeroExponentAt_spec
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {n : ℕ}
    (h : ∃ d ∈ R.face.support, d (0 : Fin 4) = n) :
    R.zeroExponentAt n ∈ R.face.support ∧
      R.zeroExponentAt n (0 : Fin 4) = n := by
  unfold CrossFacetRayData.zeroExponentAt
  split
  · rename_i h'
    exact Classical.choose_spec h'
  · rename_i h'
    exact (h' h).elim

/-- Reindexing a genuine support exponent returns that exponent itself. -/
theorem CrossFacetRayData.zeroExponentAt_eq_of_face_mem
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ R.face.support) :
    R.zeroExponentAt (d (0 : Fin 4)) = d := by
  have hex : ∃ q ∈ R.face.support,
      q (0 : Fin 4) = d (0 : Fin 4) := ⟨d, hd, rfl⟩
  have hs := R.zeroExponentAt_spec hex
  exact R.support_eq_of_zeroCoordinate_eq hs.1 hd hs.2

/-- Transverse affine slope of the ray. -/
noncomputable def CrossFacetRayData.zeroSlope
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (k : Fin 4) : K :=
  (((R.outsideExponent k : ℤ) - (R.facetExponent k : ℤ) : ℤ) : K) /
    ((R.outsideExponent (0 : Fin 4) : ℕ) : K)

/-- Every supported ray exponent has the affine rank-three exponent formula
when indexed by its literal coordinate-`0` exponent. -/
theorem CrossFacetRayData.zero_support_affine
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ R.face.support) :
    (fun k : Fin 4 => ((d k : ℕ) : K)) =
      fun k =>
        rankThreeLogBaseExponent
            ((R.facetExponent 1 : ℕ) : K)
            ((R.facetExponent 2 : ℕ) : K)
            ((R.facetExponent 3 : ℕ) : K) k +
          ((d (0 : Fin 4) : ℕ) : K) *
            rankThreeLogDirection
              (1 : K)
              (R.zeroSlope (1 : Fin 4))
              (R.zeroSlope (2 : Fin 4))
              (R.zeroSlope (3 : Fin 4)) k := by
  funext k
  have hline := R.affine_proportional d hd k
  have hlineK := congrArg (fun z : ℤ => (z : K)) hline
  push_cast at hlineK
  have hden : ((R.outsideExponent (0 : Fin 4) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt R.outside_coordinate_pos)
  have hv0 : R.facetExponent (0 : Fin 4) = 0 := R.facet_coordinate_zero
  fin_cases k
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection, hv0]
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetRayData.zeroSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetRayData.zeroSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK
  · simp [rankThreeLogBaseExponent, rankThreeLogDirection,
      CrossFacetRayData.zeroSlope, hv0] at hlineK ⊢
    field_simp [hden]
    linear_combination hlineK

/-- Canonical affine-RR realisation of the balance-free ray. -/
noncomputable def CrossFacetRayData.zeroAffineLineData
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4)) :
    RankThreeAffineLineData
      (R.facetExponent 1) (R.facetExponent 2) (R.facetExponent 3) 1
      (R.zeroSlope (1 : Fin 4))
      (R.zeroSlope (2 : Fin 4))
      (R.zeroSlope (3 : Fin 4))
      R.zeroCoefficientPolynomial where
  exponent := R.zeroExponentAt
  affine := by
    intro n hn
    rcases R.exists_faceExponent_of_zeroCoefficientPolynomial_mem hn with
      ⟨d, hd, hdn⟩
    subst n
    rw [R.zeroExponentAt_eq_of_face_mem hd]
    simpa only [Nat.cast_one] using R.zero_support_affine hd

/-- The ray facet coefficient is the nonzero constant coefficient. -/
theorem CrossFacetRayData.zeroCoefficientPolynomial_coeff_zero_ne
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4)) :
    R.zeroCoefficientPolynomial.coeff 0 ≠ 0 := by
  have hcoeff := R.coeff_zeroCoefficientPolynomial_of_mem R.facet_mem_face
  rw [R.facet_coordinate_zero] at hcoeff
  rw [hcoeff]
  exact MvPolynomial.mem_support_iff.mp R.facet_mem_face

/-- The genuine outside ray exponent makes the coefficient polynomial
nonconstant. -/
theorem CrossFacetRayData.zeroCoefficientPolynomial_natDegree_pos
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4)) :
    0 < R.zeroCoefficientPolynomial.natDegree := by
  have hout := R.zeroCoefficientPolynomial_mem_of_face_mem R.outside_mem_face
  have hle := Polynomial.le_natDegree_of_mem_supp
    (R.outsideExponent (0 : Fin 4)) hout
  exact lt_of_lt_of_le R.outside_coordinate_pos hle

@[simp] theorem CrossFacetRayData.zeroAffineLineData_exponent
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (n : ℕ) :
    R.zeroAffineLineData.exponent n = R.zeroExponentAt n := by
  rfl

/-- **Exact affine-RR reconstruction.**  The multivariate polynomial attached
to the ray line data is literally the extracted ray face. -/
theorem CrossFacetRayData.zeroAffineLineData_polynomial_eq_face
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4)) :
    R.zeroAffineLineData.polynomial = R.face := by
  classical
  let L := R.zeroAffineLineData
  change L.polynomial = R.face
  apply MvPolynomial.ext
  intro d
  simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ R.face.support
  · have hidx : d (0 : Fin 4) ∈ R.zeroCoefficientPolynomial.support :=
      R.zeroCoefficientPolynomial_mem_of_face_mem hd
    have hexp : L.exponent (d (0 : Fin 4)) = d := by
      rw [show L.exponent (d (0 : Fin 4)) =
        R.zeroExponentAt (d (0 : Fin 4)) by simp [L]]
      exact R.zeroExponentAt_eq_of_face_mem hd
    have hcoeff :
        R.zeroCoefficientPolynomial.coeff (d (0 : Fin 4)) =
          MvPolynomial.coeff d R.face :=
      R.coeff_zeroCoefficientPolynomial_of_mem hd
    rw [Finset.sum_eq_single (d (0 : Fin 4))]
    · rw [L.term_eq_monomial]
      simp [hexp, hcoeff]
    · intro n hn hnd
      have hne : L.exponent n ≠ d := by
        intro heq
        have h0 := congrArg
          (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) heq
        change L.exponent n (0 : Fin 4) = d (0 : Fin 4) at h0
        have hn0 : L.exponent n (0 : Fin 4) = n := by
          have hz := L.exponent_zero_eq hn
          simpa using hz
        rw [hn0] at h0
        exact hnd h0
      rw [L.term_eq_monomial]
      simp [hne]
    · intro hnot
      exact (hnot hidx).elim
  · have hd0 : MvPolynomial.coeff d R.face = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hd0]
    apply Finset.sum_eq_zero
    intro n hn
    have hex := R.exists_faceExponent_of_zeroCoefficientPolynomial_mem hn
    have hspec := R.zeroExponentAt_spec hex
    have hLmem : L.exponent n ∈ R.face.support := by
      rw [show L.exponent n = R.zeroExponentAt n by simp [L]]
      exact hspec.1
    have hne : L.exponent n ≠ d := by
      intro heq
      apply hd
      simpa [heq] using hLmem
    rw [L.term_eq_monomial]
    simp [hne]

/-- Hessian singularity transfers exactly to the affine RR realisation. -/
theorem CrossFacetRayData.zeroAffineLineData_hessian_zero
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (hzero : hessianDeterminant F = 0) :
    hessianDeterminant R.zeroAffineLineData.polynomial = 0 := by
  rw [R.zeroAffineLineData_polynomial_eq_face]
  exact R.hessian_zero_of_source hzero

end

end HC4.Newton
