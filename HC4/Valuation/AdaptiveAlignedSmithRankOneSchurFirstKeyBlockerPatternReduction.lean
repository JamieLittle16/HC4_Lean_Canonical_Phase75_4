import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyRadialNormalForm
import HC4.Valuation.AdaptiveAlignedSmithBlockerResidual
import Mathlib.Tactic

/-!
# Blocker-pattern reduction of the first transverse key

Stage 4B15 leaves the exact transverse frontier

    degree one | strict radial | nonradial Hessian kernel.

The canonical blocker exponent itself already removes almost all of the
strict-radial branch.  The three non-pure blocker patterns are genuinely
transverse-linear.  Their concrete residual normal forms retain a nonzero
longitudinal coefficient polynomial over one of the three transverse
exponents `e_j`.  Honest right recentering acts on that fibre by Taylor
translation at `1`, hence preserves nonzeroness.  Therefore the recentered
special fibre contains an actual source monomial of total transverse degree
one.  Since B8/B14 use the *least* positive transverse source degree, that
least degree is exactly one.

Thus a strict radial branch can occur only over the pure-longitudinal blocker.
The next patch can use the already-green nonzero longitudinal Hessian pivot
for precisely that one remaining pattern.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero fixed transverse-linear longitudinal coefficient in the honest
special fibre forces the least positive transverse source degree to be one. -/
theorem firstPositiveTransverseSourceDegree_eq_one_of_linearCoefficient_ne_zero
    (F : MvPolynomial (Fin 4) K)
    (hpos : (positiveTransverseSourceSupport F).Nonempty)
    (j : Fin 3)
    (hlinear :
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F ≠ 0) :
    firstPositiveTransverseSourceDegree F hpos = 1 := by
  let a := (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F).natDegree
  have hcoeff :
      (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F).coeff a ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mpr hlinear
  have hsource :
      MvPolynomial.coeff ((Finsupp.single j 1).cons a) F ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff]
    exact hcoeff
  have hsupp : ((Finsupp.single j 1).cons a) ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hsource
  have hdeg :
      pureLongitudinalTransverseDegree ((Finsupp.single j 1).cons a) = 1 := by
    unfold pureLongitudinalTransverseDegree
    rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
      show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
      show (3 : Fin 4) = (2 : Fin 3).succ by rfl]
    rw [Finsupp.cons_succ, Finsupp.cons_succ, Finsupp.cons_succ]
    fin_cases j <;> simp
  have hle : firstPositiveTransverseSourceDegree F hpos ≤ 1 := by
    rw [← hdeg]
    exact firstPositiveTransverseSourceDegree_le F hpos hsupp (by omega)
  have hpositive : 0 < firstPositiveTransverseSourceDegree F hpos := by
    rcases exists_source_firstPositiveTransverseSourceDegree F hpos with
      ⟨d, hd, hdpos, hdeq⟩
    rw [← hdeq]
    exact hdpos
  omega

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Any nonzero transverse-linear fibre retained by the raw blocker remains
nonzero on the honest right-recentered special fibre. -/
theorem recentered_linearCoefficient_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (j : Fin 3)
    (hraw :
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1)
        B.aligned.endpoint.rawSpecialFiber ≠ 0) :
    longitudinalCoefficientPolynomialAt (Finsupp.single j 1)
        (polynomialFamilySpecialFiber C.family) ≠ 0 := by
  rw [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family,
    B.aligned.endpoint.rightRecenteredFamily_specialFiber,
    longitudinalCoefficientPolynomialAt_longitudinalRightRecenterHom]
  exact polynomial_taylor_one_ne_zero _ hraw

/-- Carrier form of the generic degree-one criterion. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree_eq_one_of_linearCoefficient_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (j : Fin 3)
    (hlinear :
      longitudinalCoefficientPolynomialAt (Finsupp.single j 1)
        (polynomialFamilySpecialFiber C.family) ≠ 0) :
    D.transverseDegree = 1 := by
  unfold FirstKeyCanonicalMaximalHomogeneousKernelData.transverseDegree
  exact
    firstPositiveTransverseSourceDegree_eq_one_of_linearCoefficient_ne_zero
      (polynomialFamilySpecialFiber C.family) L.hpos j hlinear

/-- The three non-pure blocker constructors are already transverse-linear on
the honest recentered source.  Therefore every first-key homogeneous packet
is either transverse degree one or lies over the pure-longitudinal blocker. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_pureLongitudinalBlocker
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L) :
    D.transverseDegree = 1 ∨ IsPureLongitudinalSmithPattern B.exponent := by
  rcases B.concreteResidualNormalForm with ⟨R⟩
  cases R with
  | pureLongitudinal A C0 hpattern hA hAeq hC hfactor hdegree normal =>
      exact Or.inr hpattern

  | lowNegativeFirst A R0 hpattern hA hAeq hR hfactor hdegree normal =>
      left
      have htrans :=
        smithTransverseExponent_eq_single_one_of_lowNegativeFirst
          B.exponent hpattern
      have hraw :
          longitudinalCoefficientPolynomialAt (Finsupp.single (1 : Fin 3) 1)
              B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
        have hA' :
            longitudinalCoefficientPolynomialAt
                (smithTransverseExponent
                  B.exponent.b B.exponent.c B.exponent.d)
                B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
          change longitudinalCoefficientPolynomial
              B.exponent.b B.exponent.c B.exponent.d
              B.aligned.endpoint.rawSpecialFiber ≠ 0
          rw [← hAeq]
          exact hA
        rw [htrans] at hA'
        exact hA'
      exact D.transverseDegree_eq_one_of_linearCoefficient_ne_zero 1
        (C.recentered_linearCoefficient_ne_zero 1 hraw)

  | lowNegativeSecond A R0 hpattern hA hAeq hR hfactor hdegree normal =>
      left
      have htrans :=
        smithTransverseExponent_eq_single_zero_of_lowNegativeSecond
          B.exponent hpattern
      have hraw :
          longitudinalCoefficientPolynomialAt (Finsupp.single (0 : Fin 3) 1)
              B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
        have hA' :
            longitudinalCoefficientPolynomialAt
                (smithTransverseExponent
                  B.exponent.b B.exponent.c B.exponent.d)
                B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
          change longitudinalCoefficientPolynomial
              B.exponent.b B.exponent.c B.exponent.d
              B.aligned.endpoint.rawSpecialFiber ≠ 0
          rw [← hAeq]
          exact hA
        rw [htrans] at hA'
        exact hA'
      exact D.transverseDegree_eq_one_of_linearCoefficient_ne_zero 0
        (C.recentered_linearCoefficient_ne_zero 0 hraw)

  | wLinear A R0 hpattern hA hAeq hR hfactor hdegree normal =>
      left
      have htrans :=
        smithTransverseExponent_eq_single_two_of_wLinear
          B.exponent hpattern
      have hraw :
          longitudinalCoefficientPolynomialAt (Finsupp.single (2 : Fin 3) 1)
              B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
        have hA' :
            longitudinalCoefficientPolynomialAt
                (smithTransverseExponent
                  B.exponent.b B.exponent.c B.exponent.d)
                B.aligned.endpoint.rawSpecialFiber ≠ 0 := by
          change longitudinalCoefficientPolynomial
              B.exponent.b B.exponent.c B.exponent.d
              B.aligned.endpoint.rawSpecialFiber ≠ 0
          rw [← hAeq]
          exact hA
        rw [htrans] at hA'
        exact hA'
      exact D.transverseDegree_eq_one_of_linearCoefficient_ne_zero 2
        (C.recentered_linearCoefficient_ne_zero 2 hraw)

/-- **Stage 4B16 blocker-pattern collapse.**

The strict Euler-radial branch from B15 cannot occur on any of the three
transverse-linear blocker patterns.  If it occurs at all, the endpoint is
necessarily the pure-longitudinal blocker. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.strictRadial_implies_pureLongitudinalBlocker
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (S : C.FirstKeyStrictRadialProfileData D F) :
    IsPureLongitudinalSmithPattern B.exponent := by
  rcases D.degreeOne_or_pureLongitudinalBlocker with hdegree | hpure
  · have hm2 := S.transverseDegree_two_le
    omega
  · exact hpure

/-- After using the blocker pattern, the B15 three-way frontier sharpens to:

* transverse degree one;
* strict radial over the pure-longitudinal blocker only;
* genuine nonradial transverse Hessian kernel.
-/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_pureStrictRadial_or_nonradialKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) :
    D.transverseDegree = 1 ∨
      (IsPureLongitudinalSmithPattern B.exponent ∧
        Nonempty (C.FirstKeyStrictRadialProfileData D F)) ∨
      Nonempty (C.FirstKeyNonradialTransverseKernelData D F) := by
  rcases D.degreeOne_or_strictRadial_or_nonradialKernel F with
    hdegree | hrest
  · exact Or.inl hdegree
  · rcases hrest with hstrict | hnon
    · right
      left
      rcases hstrict with ⟨S⟩
      exact ⟨D.strictRadial_implies_pureLongitudinalBlocker F S, ⟨S⟩⟩
    · exact Or.inr (Or.inr hnon)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
