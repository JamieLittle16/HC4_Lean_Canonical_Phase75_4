import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Newton.FiniteSupportCrossFacetRayAffineRRTerminal
import HC4.RationalRigidity.RankThreeTerminalDirectionSplit
import Mathlib.Tactic

/-!
# A19.74: a genuine lower first-contact ray has nonzero ordinary-degree direction

The balance-free affine ray extracted in A19.67 from an A19.66 lower
first-nonfacet carrier still lies on the exact denominator-cleared first-contact
hyperplane.  In the canonical `.qs` chart the affine parameter is literally
coordinate `0`.

If the affine direction had ordinary-degree sum

    1 + Q + R + S = 0,

then the affine support identity would give equal ordinary degrees for the
retained facet and outside exponents.  Subtracting their two exact first-contact
equations would then force

    bump * outsideExponent₀ = 0,

contradicting both the positive first-contact bump and the genuine positive
outside coordinate.

Thus the homogeneous-direction branch of the mature RationalRigidity terminal
split is unavailable on a genuine lower first-contact ray.  A rank-three `.qs`
endpoint leaves only degree one or one fixed transverse direction.  No torus
balance, integrality of the transverse slopes, or new termination measure is
used.  The final theorem below is the kernel-facing finite split consumed by
the next local assembly layer.
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

/-- The affine direction of a genuine `.qs` lower first-contact ray cannot
preserve ordinary degree. -/
theorem qs_ray_directionSum_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    1 + C.ray.zeroSlope (1 : Fin 4) + C.ray.zeroSlope (2 : Fin 4) +
        C.ray.zeroSlope (3 : Fin 4) ≠ 0 := by
  intro hsum

  have haff := C.ray.zero_support_affine C.ray.outside_mem_face
  have h1 := congrFun haff (1 : Fin 4)
  have h2 := congrFun haff (2 : Fin 4)
  have h3 := congrFun haff (3 : Fin 4)
  simp [rankThreeLogBaseExponent, rankThreeLogDirection] at h1 h2 h3

  have hsumMul :
      ((C.ray.outsideExponent (0 : Fin 4) : ℕ) : K) *
          (1 + C.ray.zeroSlope (1 : Fin 4) +
            C.ray.zeroSlope (2 : Fin 4) +
            C.ray.zeroSlope (3 : Fin 4)) = 0 := by
    rw [hsum]
    simp

  have hdegK :
      ((ordinaryDegree4 C.ray.outsideExponent : ℕ) : K) =
        ((ordinaryDegree4 C.ray.facetExponent : ℕ) : K) := by
    simp only [ordinaryDegree4]
    push_cast
    rw [C.ray.facet_coordinate_zero]
    simp only [Nat.cast_zero]
    linear_combination h1 + h2 + h3 + hsumMul

  have hdeg :
      ordinaryDegree4 C.ray.outsideExponent =
        ordinaryDegree4 C.ray.facetExponent := by
    exact_mod_cast hdegK

  have hfacetContact :
      scaledContactExponentWeight (0 : Fin 4) C.scale C.bump
          C.ray.facetExponent =
        ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using
      C.ray_contact_eq C.ray.facetExponent C.ray.facet_mem_face
  have houtContact :
      scaledContactExponentWeight (0 : Fin 4) C.scale C.bump
          C.ray.outsideExponent =
        ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using
      C.ray_contact_eq C.ray.outsideExponent C.ray.outside_mem_face

  unfold scaledContactExponentWeight at hfacetContact houtContact
  rw [C.ray.facet_coordinate_zero] at hfacetContact
  rw [hdeg] at houtContact
  have hprod :
      (C.bump : ℤ) * (C.ray.outsideExponent (0 : Fin 4) : ℤ) = 0 := by
    linear_combination houtContact - hfacetContact
  have hbump : (C.bump : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.bump_pos)
  have hout : (C.ray.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.ray.outside_coordinate_pos)
  exact (mul_ne_zero hbump hout) hprod

/-- A rank-three `.qs` endpoint on the genuine lower first-contact ray reaches
only the four non-homogeneous branches of the mature affine RR direction
split. -/
theorem qs_ray_terminal_degreeOne_or_fixedDirection
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.ray.zeroCoefficientPolynomial.natDegree = 1 ∨
      C.ray.zeroSlope (1 : Fin 4) = 0 ∨
      C.ray.zeroSlope (2 : Fin 4) = 0 ∨
      C.ray.zeroSlope (3 : Fin 4) = 0 := by
  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hcoords.2.1
  have hB : 0 < C.ray.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < C.ray.facetExponent 3 := hcoords.2.2.2
  have hcert := C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
  have hsplit :=
    HC4.RationalRigidity.rankThree_terminal_degreeOne_or_directionDegenerate
      (K := K)
      (A := C.ray.facetExponent 1)
      (B := C.ray.facetExponent 2)
      (C := C.ray.facetExponent 3)
      (P := 1)
      (Q := C.ray.zeroSlope (1 : Fin 4))
      (R := C.ray.zeroSlope (2 : Fin 4))
      (S := C.ray.zeroSlope (3 : Fin 4))
      (phi := C.ray.zeroCoefficientPolynomial)
      hA hB hC (by norm_num)
      C.ray.zeroCoefficientPolynomial_natDegree_pos
      C.ray.zeroCoefficientPolynomial_coeff_zero_ne
      hcert
  rcases hsplit with hdeg | hq | hr | hs | hsum
  · exact Or.inl hdeg
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr (Or.inl hr))
  · exact Or.inr (Or.inr (Or.inr hs))
  · exact (C.qs_ray_directionSum_ne_zero hsum).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
