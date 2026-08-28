import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirection
import HC4.RationalRigidity.RankThreeSingleDirectionRefinement
import HC4.RationalRigidity.RankThreeAffineTwoFixedEqualitiesImpossible
import HC4.RationalRigidity.RankThreeAffineTwoFixedCyclicImpossible
import Mathlib.Tactic

/-!
# A19.75: the genuine lower `qs` affine terminal is degree one

A19.74 removes the homogeneous direction from the general affine
RationalRigidity split.  Every remaining fixed transverse direction is refined
by the mature cyclic single-direction lemmas to a second fixed direction or a
reduced homogeneous equation.  The latter is exactly the full homogeneous
equation after the first slope is zero, hence is excluded by A19.74.

The three possible pairs of fixed transverse directions are then eliminated by
the affine two-fixed coefficient-three contradiction, including its two cyclic
companions.  The completely fixed direction is impossible already from the
first-contact geometry: the outside exponent has positive coordinate `0`, so
with all transverse coordinates fixed its ordinary degree is larger than the
facet endpoint, while the positive contact bump forces it to have strictly
smaller ordinary degree.

Consequently a rank-three `.qs` endpoint on the retained lower first-contact
ray has coefficient polynomial of degree exactly one.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.RationalRigidity
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The lower first-contact ray cannot fix all three transverse coordinates. -/
theorem qs_ray_all_transverse_fixed_impossible
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hQ : C.ray.zeroSlope (1 : Fin 4) = 0)
    (hR : C.ray.zeroSlope (2 : Fin 4) = 0)
    (hS : C.ray.zeroSlope (3 : Fin 4) = 0) : False := by
  have haff := C.ray.zero_support_affine C.ray.outside_mem_face
  have h1K := congrFun haff (1 : Fin 4)
  have h2K := congrFun haff (2 : Fin 4)
  have h3K := congrFun haff (3 : Fin 4)
  simp [HC4.Polynomial.rankThreeLogBaseExponent,
    HC4.Polynomial.rankThreeLogDirection, hQ, hR, hS] at h1K h2K h3K
  have h1 : C.ray.outsideExponent (1 : Fin 4) =
      C.ray.facetExponent (1 : Fin 4) := by
    exact_mod_cast h1K
  have h2 : C.ray.outsideExponent (2 : Fin 4) =
      C.ray.facetExponent (2 : Fin 4) := by
    exact_mod_cast h2K
  have h3 : C.ray.outsideExponent (3 : Fin 4) =
      C.ray.facetExponent (3 : Fin 4) := by
    exact_mod_cast h3K
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  have hdegGt :
      HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent <
        HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent := by
    simp only [HC4.Polynomial.ordinaryDegree4]
    rw [hfacet0, h1, h2, h3]
    omega
  have houtContact :
      HC4.Newton.scaledContactExponentWeight (0 : Fin 4) C.scale C.bump
          C.ray.outsideExponent =
        ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray_contact_eq C.ray.outsideExponent C.ray.outside_mem_face
  have houtLtTop :
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent <
        T.topFace.degree :=
    HC4.Newton.contact_degree_lt
      C.scale_pos C.bump_pos C.ray.outside_coordinate_pos houtContact
  have hfacetContact :
      HC4.Newton.scaledContactExponentWeight (0 : Fin 4) C.scale C.bump
          C.ray.facetExponent =
        ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray_contact_eq C.ray.facetExponent C.ray.facet_mem_face
  unfold HC4.Newton.scaledContactExponentWeight at hfacetContact
  rw [hfacet0] at hfacetContact
  have hscaleZ : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  have hfacetTopZ :
      (HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent : ℤ) =
        (T.topFace.degree : ℤ) := by
    push_cast at hfacetContact
    nlinarith
  have hfacetTop :
      HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent =
        T.topFace.degree := by
    exact_mod_cast hfacetTopZ
  omega

/-- **A19.75 lower affine terminal closure.**  A genuine lower first-contact
ray with rank-three `.qs` facet endpoint has coefficient degree exactly one. -/
theorem qs_ray_terminal_degreeOne
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.ray.zeroCoefficientPolynomial.natDegree = 1 := by
  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hcoords.2.1
  have hB : 0 < C.ray.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < C.ray.facetExponent 3 := hcoords.2.2.2
  have hphiDeg : 0 < C.ray.zeroCoefficientPolynomial.natDegree :=
    C.ray.zeroCoefficientPolynomial_natDegree_pos
  have hphi0 : C.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    C.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert0 := C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
  have hcert :
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := C.ray.zeroCoefficientPolynomial)
        ((C.ray.facetExponent 1 : ℕ) : K)
        ((C.ray.facetExponent 2 : ℕ) : K)
        ((C.ray.facetExponent 3 : ℕ) : K)
        (((1 : ℕ) : K))
        (C.ray.zeroSlope (1 : Fin 4))
        (C.ray.zeroSlope (2 : Fin 4))
        (C.ray.zeroSlope (3 : Fin 4)) := by
    simpa only [Nat.cast_one] using hcert0
  have hsum :
      1 + C.ray.zeroSlope (1 : Fin 4) + C.ray.zeroSlope (2 : Fin 4) +
          C.ray.zeroSlope (3 : Fin 4) ≠ 0 :=
    C.qs_ray_directionSum_ne_zero

  have hQR :
      C.ray.zeroSlope (1 : Fin 4) = 0 →
      C.ray.zeroSlope (2 : Fin 4) = 0 → False := by
    intro hQ hR
    by_cases hS : C.ray.zeroSlope (3 : Fin 4) = 0
    · exact C.qs_ray_all_transverse_fixed_impossible hQ hR hS
    · have hSone : C.ray.zeroSlope (3 : Fin 4) + 1 ≠ 0 := by
        intro hone
        apply hsum
        rw [hQ, hR]
        linear_combination hone
      exact HC4.RationalRigidity.rankThree_terminal_first_two_fixed_impossible_of_eq
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hQ hR hS hSone

  have hQS :
      C.ray.zeroSlope (1 : Fin 4) = 0 →
      C.ray.zeroSlope (3 : Fin 4) = 0 → False := by
    intro hQ hS
    by_cases hR : C.ray.zeroSlope (2 : Fin 4) = 0
    · exact C.qs_ray_all_transverse_fixed_impossible hQ hR hS
    · have hRone : C.ray.zeroSlope (2 : Fin 4) + 1 ≠ 0 := by
        intro hone
        apply hsum
        rw [hQ, hS]
        linear_combination hone
      exact HC4.RationalRigidity.rankThree_terminal_outer_two_fixed_impossible_of_eq
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hQ hS hR hRone

  have hRS :
      C.ray.zeroSlope (2 : Fin 4) = 0 →
      C.ray.zeroSlope (3 : Fin 4) = 0 → False := by
    intro hR hS
    by_cases hQ : C.ray.zeroSlope (1 : Fin 4) = 0
    · exact C.qs_ray_all_transverse_fixed_impossible hQ hR hS
    · have hQone : C.ray.zeroSlope (1 : Fin 4) + 1 ≠ 0 := by
        intro hone
        apply hsum
        rw [hR, hS]
        linear_combination hone
      exact HC4.RationalRigidity.rankThree_terminal_two_fixed_impossible_of_eq
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hR hS hQ hQone

  rcases C.qs_ray_terminal_degreeOne_or_fixedDirection hthree with
    hdeg | hQ | hR | hS
  · exact hdeg
  · rcases HC4.RationalRigidity.rankThree_terminal_Q_zero_refines
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hQ with
      hR | hS | hhom
    · exact (hQR hQ hR).elim
    · exact (hQS hQ hS).elim
    · exfalso
      apply hsum
      simpa [hQ] using hhom
  · rcases HC4.RationalRigidity.rankThree_terminal_R_zero_refines
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hR with
      hQ | hS | hhom
    · exact (hQR hQ hR).elim
    · exact (hRS hR hS).elim
    · exfalso
      apply hsum
      simpa [hR] using hhom
  · rcases HC4.RationalRigidity.rankThree_terminal_S_zero_refines
        hA hB hC (by norm_num) hphiDeg hphi0 hcert hS with
      hQ | hR | hhom
    · exact (hQS hQ hS).elim
    · exact (hRS hR hS).elim
    · exfalso
      apply hsum
      simpa [hS] using hhom

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
