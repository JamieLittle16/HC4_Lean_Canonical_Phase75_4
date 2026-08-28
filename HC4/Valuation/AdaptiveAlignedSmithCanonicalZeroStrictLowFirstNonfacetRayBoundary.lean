import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayTerminal
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.76: the degree-one lower RR endpoint is an actual boundary transition

A19.75 proves that a genuine lower first-contact `.qs` ray with rank-three
facet endpoint has coefficient polynomial of degree exactly one.  The retained
outside exponent gives a supported coefficient index equal to its literal
coordinate `0`.  Positivity of that coordinate and the degree-one conclusion
therefore force the outside index itself to be `1`.

Hence the top exponent in the exact affine RationalRigidity realisation is not
an abstract endpoint: it is literally the retained outside exponent.  The
mature affine RR boundary theorem then puts that exponent on the toric
coordinate boundary.  Since its old omitted coordinate `0` is positive, it
cannot return to `.qs`; the balance-free boundary rank split therefore gives a
different rank-three facet or a genuine codimension-two boundary point.

No balance relation, integral transverse direction, or new termination measure
is introduced.
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

/-- **A19.76 lower affine boundary closure.**  The actual outside exponent of a
rank-three `.qs` lower first-contact ray lies either on a different rank-three
coordinate facet or on a codimension-two coordinate boundary. -/
theorem qs_ray_outside_boundaryTransition
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    (∃ next : ToricFacet,
        next ≠ .qs ∧
          HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.outsideExponent := by
  have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have houtMem :
      C.ray.outsideExponent (0 : Fin 4) ∈
        C.ray.zeroCoefficientPolynomial.support :=
    C.ray.zeroCoefficientPolynomial_mem_of_face_mem C.ray.outside_mem_face
  have houtLe :
      C.ray.outsideExponent (0 : Fin 4) ≤
        C.ray.zeroCoefficientPolynomial.natDegree :=
    Polynomial.le_natDegree_of_mem_supp
      (C.ray.outsideExponent (0 : Fin 4)) houtMem
  have houtPos : 0 < C.ray.outsideExponent (0 : Fin 4) :=
    C.ray.outside_coordinate_pos
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 := by
    omega

  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hcoords.2.1
  have hB : 0 < C.ray.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < C.ray.facetExponent 3 := hcoords.2.2.2
  have hphiDeg : 0 < C.ray.zeroCoefficientPolynomial.natDegree :=
    C.ray.zeroCoefficientPolynomial_natDegree_pos
  have hphi0 : C.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    C.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert0 :=
    C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
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

  have hboundaryTop :=
    HC4.RationalRigidity.rankThreeAffineLine_topExponent_on_boundary_of_certificate
      C.ray.zeroAffineLineData hA hB hC (by norm_num)
      hphiDeg hphi0 hcert
  have htopEq :
      C.ray.zeroAffineLineData.exponent
          C.ray.zeroCoefficientPolynomial.natDegree =
        C.ray.outsideExponent := by
    rw [C.ray.zeroAffineLineData_exponent, hdeg, ← hout0]
    exact C.ray.zeroExponentAt_eq_of_face_mem C.ray.outside_mem_face
  have hboundary :
      HC4.Polynomial.MvExponentOnBoundary C.ray.outsideExponent := by
    rw [htopEq] at hboundaryTop
    exact hboundaryTop

  rcases HC4.Newton.mvBoundary_rankThreeFacet_or_codimensionTwo hboundary with
    hnext | htwo
  · rcases hnext with ⟨next, hnextThree⟩
    left
    refine ⟨next, ?_, hnextThree⟩
    intro heq
    subst next
    have hz : C.ray.outsideExponent (0 : Fin 4) = 0 :=
      (HC4.Newton.mvRankThreeOnFacet_qs hnextThree).1
    omega
  · exact Or.inr htwo

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
