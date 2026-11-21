import HC4.Newton.FiniteSupportCrossFacetRayHomogeneousTerminal
import HC4.Valuation.FiniteSupportPositiveCoordinatesHessianMinor
import HC4.Valuation.FiniteSupportCrossFacetRayHessianMinorLift
import Mathlib.Tactic

/-!
# Balance-free homogeneous ray to codimension two or rank-two Hessian geometry

After contact normalization, the homogeneous affine RR terminal has only four
possibilities: a codimension-two far endpoint, or one of three extreme binary
directions. In each binary direction two transverse coordinates are literally
fixed at their positive rank-three base exponents on every supported ray
monomial. Hence the corresponding principal Hessian minor of the ray face is
nonzero.

This is a local geometry theorem only. It does not identify ray geometry with
source geometry and does not turn finite repair metadata into a contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.RationalRigidity
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A homogeneous singular cross-facet ray, after canonical contact
normalization, is either already codimension two (at its near or far endpoint)
or carries an honest nonzero principal Hessian minor on the exact ray face. -/
theorem balanceFreeHomogeneousRay_codimensionTwo_or_rankTwoFace
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    {D : ℕ}
    (hzero : hessianDeterminant F = 0)
    (hhom : ∀ d ∈ F.support, ordinaryDegree4 d = D) :
    let R0 := R.renameContactToZero
    MvExponentOnCodimensionTwoBoundary R0.facetExponent ∨
      MvExponentOnCodimensionTwoBoundary
        (R0.zeroAffineLineData.exponent
          R0.zeroCoefficientPolynomial.natDegree) ∨
      ∃ i k : Fin 4,
        i ≠ k ∧
          hessianPrincipalMinor R0.face i k ≠ 0 := by
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

    have hcertNat :
        HasRankThreePolynomialTerminalCertificate
          (phi := R0.zeroCoefficientPolynomial)
          ((R0.facetExponent 1 : ℕ) : K)
          ((R0.facetExponent 2 : ℕ) : K)
          ((R0.facetExponent 3 : ℕ) : K)
          ((1 : ℕ) : K)
          (R0.zeroSlope (1 : Fin 4))
          (R0.zeroSlope (2 : Fin 4))
          (R0.zeroSlope (3 : Fin 4)) := by
      simpa using hcert
    have hstep :=
      rankThree_unit_longitudinal_step_of_certificate
        (K := K)
        (A := R0.facetExponent 1)
        (B := R0.facetExponent 2)
        (C := R0.facetExponent 3)
        (P := 1)
        (Q := R0.zeroSlope (1 : Fin 4))
        (R := R0.zeroSlope (2 : Fin 4))
        (S := R0.zeroSlope (3 : Fin 4))
        (phi := R0.zeroCoefficientPolynomial)
        hA hB hC (by norm_num) hphiDeg hphi0 hcertNat
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
        ordinaryDegree4 R0.facetExponent = D :=
      R.renameContactToZero_support_degree hhom R0.facet_mem_face
    have hbaseOrd :
        ordinaryDegree4 R0.facetExponent =
          R0.facetExponent 1 + R0.facetExponent 2 +
            R0.facetExponent 3 := by
      rw [ordinaryDegree4, R0.facet_coordinate_zero]
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

    rcases
        rankThree_affineTerminal_homogeneous_extreme_or_codimensionTwo
          (K := K)
          (A := R0.facetExponent 1)
          (B := R0.facetExponent 2)
          (C := R0.facetExponent 3)
          (Q := R0.zeroSlope (1 : Fin 4))
          (R := R0.zeroSlope (2 : Fin 4))
          (S := R0.zeroSlope (3 : Fin 4))
          (phi := R0.zeroCoefficientPolynomial)
          R0.zeroAffineLineData hA hB hC hphiDeg hphi0 hcert
          hdegreeOne' hdegreeTop' with
      htopCodim | hQR | hQS | hRS
    · exact Or.inr (Or.inl htopCodim)
    · rcases hQR with ⟨hQ, hR, _hS⟩
      have hface : R0.face ≠ 0 := by
        intro hz
        have hm := R0.facet_mem_face
        rw [hz] at hm
        simp at hm
      have hpos1 : ∀ d ∈ R0.face.support, 0 < d (1 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (1 : Fin 4)
        have heq : d (1 : Fin 4) = R0.facetExponent (1 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hQ] at haff
          exact_mod_cast haff
        rw [heq]
        exact hA
      have hpos2 : ∀ d ∈ R0.face.support, 0 < d (2 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (2 : Fin 4)
        have heq : d (2 : Fin 4) = R0.facetExponent (2 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hR] at haff
          exact_mod_cast haff
        rw [heq]
        exact hB
      exact Or.inr (Or.inr
        ⟨(1 : Fin 4), (2 : Fin 4), by decide,
          hessianPrincipalMinor_ne_zero_of_support_two_positive
            hface (by decide) hpos1 hpos2⟩)
    · rcases hQS with ⟨hQ, hS, _hR⟩
      have hface : R0.face ≠ 0 := by
        intro hz
        have hm := R0.facet_mem_face
        rw [hz] at hm
        simp at hm
      have hpos1 : ∀ d ∈ R0.face.support, 0 < d (1 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (1 : Fin 4)
        have heq : d (1 : Fin 4) = R0.facetExponent (1 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hQ] at haff
          exact_mod_cast haff
        rw [heq]
        exact hA
      have hpos3 : ∀ d ∈ R0.face.support, 0 < d (3 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (3 : Fin 4)
        have heq : d (3 : Fin 4) = R0.facetExponent (3 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hS] at haff
          exact_mod_cast haff
        rw [heq]
        exact hC
      exact Or.inr (Or.inr
        ⟨(1 : Fin 4), (3 : Fin 4), by decide,
          hessianPrincipalMinor_ne_zero_of_support_two_positive
            hface (by decide) hpos1 hpos3⟩)
    · rcases hRS with ⟨hR, hS, _hQ⟩
      have hface : R0.face ≠ 0 := by
        intro hz
        have hm := R0.facet_mem_face
        rw [hz] at hm
        simp at hm
      have hpos2 : ∀ d ∈ R0.face.support, 0 < d (2 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (2 : Fin 4)
        have heq : d (2 : Fin 4) = R0.facetExponent (2 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hR] at haff
          exact_mod_cast haff
        rw [heq]
        exact hB
      have hpos3 : ∀ d ∈ R0.face.support, 0 < d (3 : Fin 4) := by
        intro d hd
        have haff := congrFun (R0.zero_support_affine hd) (3 : Fin 4)
        have heq : d (3 : Fin 4) = R0.facetExponent (3 : Fin 4) := by
          simp [rankThreeLogBaseExponent, rankThreeLogDirection, hS] at haff
          exact_mod_cast haff
        rw [heq]
        exact hC
      exact Or.inr (Or.inr
        ⟨(2 : Fin 4), (3 : Fin 4), by decide,
          hessianPrincipalMinor_ne_zero_of_support_two_positive
            hface (by decide) hpos2 hpos3⟩)
  · exact Or.inl hcodim


/-- **Source-facing balance-free ray dichotomy.**

The local contact-zero RR analysis either reaches codimension two, or its
nonzero ray Hessian pivot lifts through the canonical ray extractor and the
coordinate normalization to a genuine nonzero principal Hessian minor of the
original source polynomial. -/
theorem balanceFreeHomogeneousRay_codimensionTwo_or_sourceRankTwo
    {F : MvPolynomial (Fin 4) K}
    {j : Fin 4}
    (R : CrossFacetRayData F j)
    {D : ℕ}
    (hzero : hessianDeterminant F = 0)
    (hhom : ∀ d ∈ F.support, ordinaryDegree4 d = D) :
    MvExponentOnCodimensionTwoBoundary R.renameContactToZero.facetExponent ∨
      MvExponentOnCodimensionTwoBoundary
        (R.renameContactToZero.zeroAffineLineData.exponent
          R.renameContactToZero.zeroCoefficientPolynomial.natDegree) ∨
      ∃ i k : Fin 4,
        i ≠ k ∧ hessianPrincipalMinor F i k ≠ 0 := by
  rcases balanceFreeHomogeneousRay_codimensionTwo_or_rankTwoFace
      R hzero hhom with hnear | hfar | hminor
  · exact Or.inl hnear
  · exact Or.inr (Or.inl hfar)
  · rcases hminor with ⟨i, k, hik, hminor⟩
    let rho : Equiv.Perm (Fin 4) := Equiv.swap j (0 : Fin 4)
    have hsource :=
      CrossFacetRayData.source_hessianPrincipalMinor_ne_zero_of_renamedZero
        R hminor
    have hne : rho.symm i ≠ rho.symm k := by
      intro h
      apply hik
      exact rho.symm.injective h
    exact Or.inr (Or.inr ⟨rho.symm i, rho.symm k, hne, hsource⟩)

end

end HC4.Valuation
