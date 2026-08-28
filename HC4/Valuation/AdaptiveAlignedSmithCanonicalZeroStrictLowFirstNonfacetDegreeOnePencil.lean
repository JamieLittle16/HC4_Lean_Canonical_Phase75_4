import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayBoundary
import HC4.Polynomial.RankThreeDegreeOnePencilRealisation
import Mathlib.Tactic

/-!
# A19.79: the lower `qs` terminal is an honest degree-one endpoint pencil

A19.75 forces the coefficient polynomial of a rank-three lower `.qs` ray to
have degree exactly one.  Since the balance-free ray is indexed by its literal
coordinate `0`, every supported ray exponent therefore has coordinate `0`
equal to `0` or `1`.  Coordinate-zero injectivity on the ray identifies those
two fibres with the retained facet and outside exponents themselves.

Thus the complete ray face is literally supported on the honest length-one
rank-three segment

    (0,A,B,C)  --  (1,U2,U3,U4).

The generic degree-one moment realisation can then be applied directly to the
actual ray face.  Its Hessian singularity yields a zero coefficient-weighted
endpoint-pencil determinant, while both endpoint coefficients remain nonzero.
This is the small scalar interface used by the remaining balance-free endpoint
arithmetic; no torus grading is introduced.
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

/-- In the degree-one lower terminal, the retained outside exponent is exactly
index `1` of the coordinate-zero affine parametrisation. -/
theorem qs_ray_outside_zeroCoordinate_eq_one
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.ray.outsideExponent (0 : Fin 4) = 1 := by
  have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have houtMem :
      C.ray.outsideExponent (0 : Fin 4) ∈
        C.ray.zeroCoefficientPolynomial.support :=
    C.ray.zeroCoefficientPolynomial_mem_of_face_mem C.ray.outside_mem_face
  have houtLe :
      C.ray.outsideExponent (0 : Fin 4) ≤
        C.ray.zeroCoefficientPolynomial.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ houtMem
  have houtPos : 0 < C.ray.outsideExponent (0 : Fin 4) :=
    C.ray.outside_coordinate_pos
  omega

/-- The lower degree-one ray face is supported on the literal two-endpoint
integral rank-three line from its retained facet exponent to its retained
outside exponent. -/
theorem qs_ray_degreeOne_supportedLine
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    HC4.Polynomial.IsSupportedOnRankThreeLine
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1 C.ray.face := by
  intro d hd
  have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hidx : d (0 : Fin 4) ∈ C.ray.zeroCoefficientPolynomial.support :=
    C.ray.zeroCoefficientPolynomial_mem_of_face_mem hd
  have hle : d (0 : Fin 4) ≤ C.ray.zeroCoefficientPolynomial.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hidx
  have hle1 : d (0 : Fin 4) ≤ 1 := by simpa [hdeg] using hle
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  rcases Nat.eq_zero_or_pos (d (0 : Fin 4)) with hd0 | hdpos
  · refine ⟨0, by decide, ?_⟩
    have hdfacet : d = C.ray.facetExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq hd C.ray.facet_mem_face
        (by simpa [hd0, C.ray.facet_coordinate_zero])
    rw [hdfacet]
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply,
        C.ray.facet_coordinate_zero]
  · have hd1 : d (0 : Fin 4) = 1 := by omega
    refine ⟨1, by decide, ?_⟩
    have hdout : d = C.ray.outsideExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq hd C.ray.outside_mem_face
        (by simpa [hd1, hout0])
    rw [hdout]
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply, hout0]

/-- Both literal endpoints of the lower degree-one line occur with nonzero
coefficients in the actual ray face. -/
theorem qs_ray_degreeOne_endpoint_coefficients_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1 C.ray.face
    phi.coeff 0 ≠ 0 ∧ phi.coeff 1 ≠ 0 := by
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    (C.ray.facetExponent 1)
    (C.ray.facetExponent 2)
    (C.ray.facetExponent 3)
    1
    (C.ray.outsideExponent 1)
    (C.ray.outsideExponent 2)
    (C.ray.outsideExponent 3)
    1 C.ray.face
  have hstartExp :
      HC4.Polynomial.rankThreeLineExponentFinsupp
        (C.ray.facetExponent 1)
        (C.ray.facetExponent 2)
        (C.ray.facetExponent 3)
        1
        (C.ray.outsideExponent 1)
        (C.ray.outsideExponent 2)
        (C.ray.outsideExponent 3)
        1 0 = C.ray.facetExponent := by
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply,
        C.ray.facet_coordinate_zero]
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hendExp :
      HC4.Polynomial.rankThreeLineExponentFinsupp
        (C.ray.facetExponent 1)
        (C.ray.facetExponent 2)
        (C.ray.facetExponent 3)
        1
        (C.ray.outsideExponent 1)
        (C.ray.outsideExponent 2)
        (C.ray.outsideExponent 3)
        1 1 = C.ray.outsideExponent := by
    ext k
    fin_cases k <;>
      simp [HC4.Polynomial.rankThreeLineExponentFinsupp_apply, hout0]
  constructor
  · dsimp [phi]
    rw [HC4.Polynomial.coeff_zero_rankThreeLineCoefficientPolynomial,
      hstartExp]
    exact MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face
  · dsimp [phi]
    rw [HC4.Polynomial.coeff_M_rankThreeLineCoefficientPolynomial,
      hendExp]
    exact MvPolynomial.mem_support_iff.mp C.ray.outside_mem_face

/-- **A19.79 weighted-pencil interface.**  The actual two-endpoint lower ray
has singular coefficient-weighted endpoint pencil. -/
theorem qs_ray_degreeOne_endpointPencil_det_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
      (C.ray.facetExponent 1)
      (C.ray.facetExponent 2)
      (C.ray.facetExponent 3)
      1
      (C.ray.outsideExponent 1)
      (C.ray.outsideExponent 2)
      (C.ray.outsideExponent 3)
      1 C.ray.face
    (HC4.Polynomial.weightedRankThreeEndpointPencil
      ((C.ray.facetExponent 1 : ℕ) : K)
      ((C.ray.facetExponent 2 : ℕ) : K)
      ((C.ray.facetExponent 3 : ℕ) : K)
      (1 : K)
      ((C.ray.outsideExponent 1 : ℕ) : K)
      ((C.ray.outsideExponent 2 : ℕ) : K)
      ((C.ray.outsideExponent 3 : ℕ) : K)
      (phi.coeff 0) (phi.coeff 1)).det = 0 := by
  simpa only [Nat.cast_one] using
    (HC4.Polynomial.supported_rankThree_degreeOne_endpointPencil_det_zero
      (K := K)
      (v2 := C.ray.facetExponent 1)
      (v3 := C.ray.facetExponent 2)
      (v4 := C.ray.facetExponent 3)
      (u1 := 1)
      (u2 := C.ray.outsideExponent 1)
      (u3 := C.ray.outsideExponent 2)
      (u4 := C.ray.outsideExponent 3)
      (F := C.ray.face)
      (by decide)
      (C.qs_ray_degreeOne_supportedLine hthree)
      C.ray_hessian_zero)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
