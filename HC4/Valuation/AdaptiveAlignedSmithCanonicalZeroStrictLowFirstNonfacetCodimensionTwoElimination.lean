import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetResidualDegreeGap
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoAlgebra
import Mathlib.Tactic

/-!
# A19.91: the lower degree-one `qs` ray cannot end in codimension two

A19.75/A19.79 identify the genuine lower `qs` ray with a primitive
coordinate-zero step and coefficient degree one.  A19.90 upgrades its
rank-three terminal equation to the exact autonomous normal form

    T = X - X^2.

The expensive pure algebra is isolated in
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoAlgebra`.
This file only extracts the small scalar data needed from the large
restart-state records and assembles the contradiction.
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

-- Keep the public elimination theorem thin so command-local heartbeat budgets reset.

/-- Cast-normalised rank-three terminal certificate.  Keeping this conversion
in its own declaration prevents the final proof from repeatedly normalising
the full dependent terminal record. -/
private theorem qs_ray_degreeOne_terminalCertificate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := C.ray.zeroCoefficientPolynomial)
      ((C.ray.facetExponent 1 : ℕ) : K)
      ((C.ray.facetExponent 2 : ℕ) : K)
      ((C.ray.facetExponent 3 : ℕ) : K)
      (1 : K)
      (C.ray.zeroSlope (1 : Fin 4))
      (C.ray.zeroSlope (2 : Fin 4))
      (C.ray.zeroSlope (3 : Fin 4)) := by
  have hcert0 := C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
  simpa only [Nat.cast_one] using hcert0

/-- Extract coordinate zero and the three transverse affine endpoint equations
as a compact tuple.  This is the only place where the support-affine record is
normalised. -/
private theorem qs_ray_outside_affine_data
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.ray.outsideExponent (0 : Fin 4) = 1 ∧
      ((C.ray.outsideExponent (1 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (1 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (1 : Fin 4) ∧
      ((C.ray.outsideExponent (2 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (2 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (2 : Fin 4) ∧
      ((C.ray.outsideExponent (3 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (3 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (3 : Fin 4) := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have haff := C.ray.zero_support_affine C.ray.outside_mem_face
  refine ⟨hout0, ?_, ?_, ?_⟩
  · have h := congrFun haff (1 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  · have h := congrFun haff (2 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  · have h := congrFun haff (3 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h

set_option maxHeartbeats 1000000 in
/-- The valuation layer now performs only geometric extraction.  A19.90 and
the degree-one codimension-two algebra are consumed together by the state-free
adapter in the algebra module, so no raw polynomial identity is elaborated
against the dependent restart-state record here. -/
private theorem qs_ray_outside_transverse_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtTwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary
      C.ray.outsideExponent) :
    C.ray.outsideExponent (1 : Fin 4) = 0 ∧
      C.ray.outsideExponent (2 : Fin 4) = 0 ∧
      C.ray.outsideExponent (3 : Fin 4) = 0 := by
  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hcoords.2.1
  have hB : 0 < C.ray.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < C.ray.facetExponent 3 := hcoords.2.2.2
  have hphiDeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hphi0 : C.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    C.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert := qs_ray_degreeOne_terminalCertificate C hthree
  rcases qs_ray_outside_affine_data C hthree with
    ⟨hout0, h1aff, h2aff, h3aff⟩
  have hpairs :=
    HC4.Valuation.transversePair_zero_of_codimensionTwoBoundary
      C.ray.outsideExponent hout0 houtTwo
  exact
    HC4.Valuation.degreeOneTerminal_codimensionTwoPair_forcesAll
      hA hB hC hphiDeg hphi0 hcert h1aff h2aff h3aff hpairs

/-- Once transverse vanishing is known, the primitive coordinate-zero step
makes the outside endpoint have ordinary degree exactly one. -/
private theorem qs_ray_outside_degree_eq_one
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtTwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary
      C.ray.outsideExponent) :
    HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent = 1 := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  rcases qs_ray_outside_transverse_zero C hthree houtTwo with ⟨h1, h2, h3⟩
  simp [HC4.Polynomial.ordinaryDegree4, hout0, h1, h2, h3]

/-- **A19.91 lower codimension-two elimination.**  Under the surviving
rank-three `.qs` hypothesis, the actual degree-one outside endpoint cannot be
codimension two. -/
theorem qs_ray_outside_codimensionTwo_impossible
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtTwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary
      C.ray.outsideExponent) : False := by
  have houtDeg := qs_ray_outside_degree_eq_one C hthree houtTwo
  rcases C.qs_ray_strictLow_sourceCodimensionTwo_degree_lt_outside hthree with
    ⟨d, _hd, hdeg3, _hd0, _htwo, hlt⟩
  rw [houtDeg] at hlt
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
