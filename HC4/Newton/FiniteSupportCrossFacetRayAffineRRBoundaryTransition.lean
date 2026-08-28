import HC4.Newton.FiniteSupportCrossFacetRayAffineRRTerminal
import HC4.Newton.SingularBoundaryRankSplit
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import Mathlib.Tactic

/-!
# A19.77: the balance-free affine RR top endpoint is genuine support

A19.72 supplies the complete affine RationalRigidity terminal certificate for
any contact-coordinate `0` ray whose facet endpoint is rank three on `.qs`.
The mature RR top-boundary theorem places the exponent at the degree of the
coefficient polynomial on the toric boundary.

The affine realisation in A19.69 is lossless: that degree is a genuinely
supported univariate index and `zeroExponentAt` is therefore a genuinely
supported exponent of the extracted ray face.  Its coordinate `0` is exactly
the positive polynomial degree.  Consequently the new boundary point cannot
lie back on `.qs`; it is rank three on a different coordinate facet or is
already codimension two.

The returned exponent stays on the exact extracted ray carrier throughout.
No torus balance or integral transverse direction is used.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.RationalRigidity
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Supported balance-free RR boundary transition.**  The RR top exponent is
an actual ray monomial and leaves the starting `.qs` facet. -/
theorem CrossFacetRayData.zero_rankThree_topSupportedBoundaryTransition
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs R.facetExponent) :
    ∃ d ∈ R.face.support,
      0 < d (0 : Fin 4) ∧
      ((∃ next : ToricFacet,
          next ≠ .qs ∧ MvRankThreeOnFacet next d) ∨
        MvExponentOnCodimensionTwoBoundary d) := by
  have hcoords := mvRankThreeOnFacet_qs hthree
  have hA : 0 < R.facetExponent 1 := hcoords.2.1
  have hB : 0 < R.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < R.facetExponent 3 := hcoords.2.2.2
  have hphiDeg : 0 < R.zeroCoefficientPolynomial.natDegree :=
    R.zeroCoefficientPolynomial_natDegree_pos
  have hphi0 : R.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    R.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert0 := R.zero_rankThree_terminalCertificate hzero hthree
  have hcert :
      HasRankThreePolynomialTerminalCertificate
        (phi := R.zeroCoefficientPolynomial)
        ((R.facetExponent 1 : ℕ) : K)
        ((R.facetExponent 2 : ℕ) : K)
        ((R.facetExponent 3 : ℕ) : K)
        (((1 : ℕ) : K))
        (R.zeroSlope (1 : Fin 4))
        (R.zeroSlope (2 : Fin 4))
        (R.zeroSlope (3 : Fin 4)) := by
    simpa only [Nat.cast_one] using hcert0
  have hboundaryTop :=
    rankThreeAffineLine_topExponent_on_boundary_of_certificate
      R.zeroAffineLineData hA hB hC (by norm_num)
      hphiDeg hphi0 hcert

  have hphi : R.zeroCoefficientPolynomial ≠ 0 := by
    intro hz
    rw [hz] at hphi0
    simp at hphi0
  have hDmem :
      R.zeroCoefficientPolynomial.natDegree ∈
        R.zeroCoefficientPolynomial.support := by
    rw [Polynomial.mem_support_iff]
    change R.zeroCoefficientPolynomial.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  rcases R.exists_faceExponent_of_zeroCoefficientPolynomial_mem hDmem with
    ⟨q, hqmem, hq0⟩
  have hspec := R.zeroExponentAt_spec
    (show ∃ q ∈ R.face.support,
        q (0 : Fin 4) = R.zeroCoefficientPolynomial.natDegree from
      ⟨q, hqmem, hq0⟩)
  let d : Fin 4 →₀ ℕ :=
    R.zeroExponentAt R.zeroCoefficientPolynomial.natDegree
  have hdmem : d ∈ R.face.support := by
    simpa [d] using hspec.1
  have hd0 : d (0 : Fin 4) = R.zeroCoefficientPolynomial.natDegree := by
    simpa [d] using hspec.2
  have hdpos : 0 < d (0 : Fin 4) := by
    rw [hd0]
    exact hphiDeg
  have hboundary : HC4.Polynomial.MvExponentOnBoundary d := by
    simpa [d] using hboundaryTop

  refine ⟨d, hdmem, hdpos, ?_⟩
  rcases mvBoundary_rankThreeFacet_or_codimensionTwo hboundary with
    hnext | htwo
  · rcases hnext with ⟨next, hnextThree⟩
    left
    refine ⟨next, ?_, hnextThree⟩
    intro heq
    subst next
    have hz : d (0 : Fin 4) = 0 :=
      (mvRankThreeOnFacet_qs hnextThree).1
    omega
  · exact Or.inr htwo

end

end HC4.Newton
