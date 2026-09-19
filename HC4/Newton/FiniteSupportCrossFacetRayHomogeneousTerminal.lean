import HC4.Newton.FiniteSupportCrossFacetRayCoordinatePermutation
import HC4.RationalRigidity.RankThreeAffineHomogeneousTerminalSplit
import Mathlib.Tactic

/-!
# Homogeneous balance-free rays after contact normalization

A cross-facet ray may start at any coordinate facet.  After the source-honest
contact normalization of
`FiniteSupportCrossFacetRayCoordinatePermutation`, the mature affine RR
terminal is available in the canonical contact-`0` chart.

If the source ray carrier is ordinary homogeneous, every exponent of the
re-extracted canonical ray still has the same ordinary degree: coordinate
permutation preserves `Finsupp.degree`, and the ray face is literal support
of the renamed source.

Combining that fact with the balance-free homogeneous affine terminal split
gives the reusable outcome needed by the final top-face assembly.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem finsuppDegree_eq_ordinaryDegree4_local
    (d : Fin 4 →₀ ℕ) :
    d.degree = ordinaryDegree4 d := by
  rw [Finsupp.degree_eq_weight_one]
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · simp [ordinaryDegree4, Fin.sum_univ_four]
  · intro i
    simp

private theorem ordinaryDegree4_mapDomain_perm
    (rho : Equiv.Perm (Fin 4))
    (d : Fin 4 →₀ ℕ) :
    ordinaryDegree4 (Finsupp.mapDomain rho d) = ordinaryDegree4 d := by
  rw [← finsuppDegree_eq_ordinaryDegree4_local,
    ← finsuppDegree_eq_ordinaryDegree4_local]
  exact Finsupp.degree_mapDomain rho d

/-- Any support exponent of the contact-normalized ray has the same ordinary
degree as its preimage in the original homogeneous source. -/
theorem CrossFacetRayData.renameContactToZero_support_degree
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    {D : ℕ}
    (hhom : ∀ d ∈ F.support, ordinaryDegree4 d = D)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ R.renameContactToZero.face.support) :
    ordinaryDegree4 d = D := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap j (0 : Fin 4)
  let R0 := R.renameContactToZero
  have hdRenamed :
      d ∈ (MvPolynomial.rename rho F).support := by
    simpa [R0, rho, CrossFacetRayData.renameContactToZero] using
      R0.support_subset hd
  have hdCoeff :
      MvPolynomial.coeff d (MvPolynomial.rename rho F) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdRenamed
  rcases MvPolynomial.coeff_rename_ne_zero rho F d hdCoeff with
    ⟨e, heMap, heCoeff⟩
  have heMem : e ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr heCoeff
  rw [← heMap]
  exact (ordinaryDegree4_mapDomain_perm rho e).trans (hhom e heMem)

/-- **Homogeneous arbitrary-contact ray terminal split.**

After source-renaming and honest re-extraction at contact coordinate `0`,
either the canonical ray facet endpoint is already codimension two, or it is
rank three on `.qs`, carries the full affine RR certificate, and the
homogeneous scalar relation forces a fixed transverse slope or a
codimension-two far endpoint. -/
theorem CrossFacetRayData.renamedZero_homogeneousTerminalSplit
    [IsAlgClosed K]
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    {D : ℕ}
    (hzero : hessianDeterminant F = 0)
    (hhom : ∀ d ∈ F.support, ordinaryDegree4 d = D) :
    let R0 := R.renameContactToZero
    (MvRankThreeOnFacet .qs R0.facetExponent ∧
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := R0.zeroCoefficientPolynomial)
        ((R0.facetExponent 1 : ℕ) : K)
        ((R0.facetExponent 2 : ℕ) : K)
        ((R0.facetExponent 3 : ℕ) : K)
        (1 : K)
        (R0.zeroSlope (1 : Fin 4))
        (R0.zeroSlope (2 : Fin 4))
        (R0.zeroSlope (3 : Fin 4)) ∧
      (R0.zeroSlope (1 : Fin 4) = 0 ∨
        R0.zeroSlope (2 : Fin 4) = 0 ∨
        R0.zeroSlope (3 : Fin 4) = 0 ∨
        MvExponentOnCodimensionTwoBoundary
          (R0.zeroAffineLineData.exponent
            R0.zeroCoefficientPolynomial.natDegree))) ∨
      MvExponentOnCodimensionTwoBoundary R0.facetExponent := by
  let R0 := R.renameContactToZero
  rcases R.renamedZero_terminalCertificate_or_codimensionTwo hzero with
    hterminal | hcodim
  · rcases hterminal with ⟨hthree, hcert⟩
    have hcoords := mvRankThreeOnFacet_qs hthree
    have hA : 0 < R0.facetExponent 1 := hcoords.2.1
    have hB : 0 < R0.facetExponent 2 := hcoords.2.2.1
    have hC : 0 < R0.facetExponent 3 := hcoords.2.2.2
    have hphiDeg : 0 < R0.zeroCoefficientPolynomial.natDegree :=
      R0.zeroCoefficientPolynomial_natDegree_pos
    have hphi0 : R0.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
      R0.zeroCoefficientPolynomial_coeff_zero_ne

    have hstep :=
      HC4.RationalRigidity.rankThree_unit_longitudinal_step_of_certificate
        hA hB hC (by norm_num) hphiDeg hphi0 hcert
    have hphi1 : R0.zeroCoefficientPolynomial.coeff 1 ≠ 0 := hstep.2
    have h1mem : 1 ∈ R0.zeroCoefficientPolynomial.support :=
      Polynomial.mem_support_iff.mpr hphi1
    have h1exists :=
      R0.exists_faceExponent_of_zeroCoefficientPolynomial_mem h1mem
    have h1spec := R0.zeroExponentAt_spec h1exists
    have h1face :
        R0.zeroAffineLineData.exponent 1 ∈ R0.face.support := by
      simpa using h1spec.1
    have hdegreeOne :
        ordinaryDegree4 (R0.zeroAffineLineData.exponent 1) = D := by
      simpa [R0] using R.renameContactToZero_support_degree hhom h1face

    have hphi : R0.zeroCoefficientPolynomial ≠ 0 := by
      intro hz
      rw [hz] at hphi0
      simp at hphi0
    have htopMem :
        R0.zeroCoefficientPolynomial.natDegree ∈
          R0.zeroCoefficientPolynomial.support := by
      rw [Polynomial.mem_support_iff]
      change R0.zeroCoefficientPolynomial.leadingCoeff ≠ 0
      exact (Polynomial.leadingCoeff_ne_zero).2 hphi
    have htopExists :=
      R0.exists_faceExponent_of_zeroCoefficientPolynomial_mem htopMem
    have htopSpec := R0.zeroExponentAt_spec htopExists
    have htopFace :
        R0.zeroAffineLineData.exponent
            R0.zeroCoefficientPolynomial.natDegree ∈ R0.face.support := by
      simpa using htopSpec.1
    have hdegreeTop :
        ordinaryDegree4
            (R0.zeroAffineLineData.exponent
              R0.zeroCoefficientPolynomial.natDegree) = D := by
      simpa [R0] using R.renameContactToZero_support_degree hhom htopFace

    have hbaseDegree :
        ordinaryDegree4 R0.facetExponent = D := by
      exact R.renameContactToZero_support_degree hhom R0.facet_mem_face
    have hbaseOrd :
        ordinaryDegree4 R0.facetExponent =
          R0.facetExponent 1 + R0.facetExponent 2 + R0.facetExponent 3 := by
      rw [ordinaryDegree4]
      rw [R0.facet_coordinate_zero]
      omega
    have hD :
        R0.facetExponent 1 + R0.facetExponent 2 +
            R0.facetExponent 3 = D := by
      omega
    have hdegreeOne' :
        ordinaryDegree4 (R0.zeroAffineLineData.exponent 1) =
          R0.facetExponent 1 + R0.facetExponent 2 +
            R0.facetExponent 3 := by
      omega
    have hdegreeTop' :
        ordinaryDegree4
            (R0.zeroAffineLineData.exponent
              R0.zeroCoefficientPolynomial.natDegree) =
          R0.facetExponent 1 + R0.facetExponent 2 +
            R0.facetExponent 3 := by
      omega

    have hsplit :=
      HC4.RationalRigidity.rankThree_affineTerminal_homogeneous_fixed_or_codimensionTwo
        R0.zeroAffineLineData hA hB hC hphiDeg hphi0 hcert
        hdegreeOne' hdegreeTop'
    exact Or.inl ⟨hthree, hcert, hsplit⟩
  · exact Or.inr hcodim

end

end HC4.Newton
