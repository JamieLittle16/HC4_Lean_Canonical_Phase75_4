import HC4.RationalRigidity.ClearedInfinityEvaluation
import HC4.RationalRigidity.RankThreeReducedTarget
import Mathlib.Tactic
import HC4.Newton.LexicographicRefinement
import HC4.Newton.LexicographicInitialForm
import HC4.Newton.IteratedRefinement
import HC4.Newton.BinarySchurPivot
import HC4.Newton.FirstSchurEntry
import HC4.Newton.FirstSchurDeterminantOrder
import HC4.Newton.RankTwoFourBlockSchur
import HC4.Newton.RankTwoReesSchurEntry
import HC4.Newton.BinaryPivotGeometry
import HC4.Newton.FixedKernelHessian
import HC4.Newton.TransverseSupportRigidity
import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Newton.AxisHomogeneousNormalForm
import HC4.Newton.DirectionalCoefficientRecurrence
import HC4.Newton.FiniteDirectionalRecurrence
import HC4.Newton.LinearPowerRecurrence
import HC4.Newton.LinearPowerRecurrenceClassification
import HC4.Newton.TransverseSliceClassification
import HC4.Newton.LinearPowerPacketNormalForm
import HC4.Newton.RankTwoHomogeneousPacketClassification
import HC4.Newton.RankOnePersistentPacket
import HC4.Newton.RankOnePacketQuadratic
import HC4.Newton.RankOnePacketReentry
import HC4.Newton.FiniteRepairTermination
import HC4.Newton.RankOneRepairProgress
import HC4.Newton.RankTwoRepairTerminal
import HC4.Newton.SmithCollisionQuadraticRankOne
import HC4.Newton.SmithGradeArithmetic
import HC4.Newton.SmithExtremeBalance
import HC4.Newton.FiniteValuationTilt
import HC4.Newton.SmithValuationTiltAdapter
import HC4.Newton.SmithPoleMinimality
import HC4.Newton.SmithFiniteBalanceClosure
import HC4.Newton.ExactCollisionFirstWall
import HC4.Newton.SmithFirstWallTransverse
import HC4.Newton.SmithFirstWallLongitudinal
import HC4.Newton.SmithFirstWallGradeClassification
import HC4.Newton.SmithSymmetricBalanceRefinement
import HC4.Newton.SmithRefinedFaceRankOnePacket
import HC4.Newton.SmithRefinedFacePolynomial
import HC4.Newton.RankOnePacketExactCollision
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import HC4.Newton.PreterminalFirstDeparture
import HC4.Newton.MixedDepartureAdapter
import HC4.Newton.TerminalConformalWeight
import HC4.Newton.TerminalQuadraticHessian
import HC4.Newton.TerminalActualHessian
import HC4.Newton.TerminalConformalFace
import HC4.Newton.TerminalCollision
import HC4.Newton.TerminalScalarGradient
import HC4.Newton.TerminalCenteredWeights
import HC4.Newton.TerminalDirectRankJumpReduction
import HC4.Newton.TerminalWeightPermutation
import HC4.Newton.TerminalNonnegativeWeights
import HC4.PlanarJC2Interface
import HC4.PlanarDoublingInjectivity
import HC4.Newton.TerminalTwoZeroPattern
import HC4.Newton.TerminalTwoZeroSupport
import HC4.Newton.TerminalTwoZeroDoublingForm
import HC4.Newton.TerminalTwoZeroEndpointInterface
import HC4.Newton.TerminalTwoZeroPlanarisation
import HC4.Newton.TwoZeroBlockDeterminant
import HC4.Newton.TerminalTwoZeroHessianSquare
import HC4.Newton.TerminalTwoZeroKellerReduction
import HC4.PlanarJacobianEvaluation
import HC4.Newton.TerminalTwoZeroGradientConjugacy
import HC4.Newton.TerminalTwoZeroJC2Endpoint
import HC4.Newton.TerminalPermutedGradient
import HC4.Newton.PositiveWeightTriangularSupport
import HC4.Newton.TerminalPositiveWeightTriangularReduction
import HC4.Newton.TerminalPositiveWeightLinearBlocks
import HC4.Newton.TerminalPositiveWeightRecursiveCertificate
import HC4.Newton.PositiveWeightTriangularEvaluation
import HC4.Newton.TerminalPositiveWeightEndpoint
import HC4.Newton.TerminalOneZeroPattern
import HC4.Newton.TerminalOneZeroSupport
import HC4.Newton.OneZeroBlockDeterminant
import HC4.Newton.TerminalOneZeroHessianFactor
import HC4.Newton.TerminalOneZeroAffineRecovery
import HC4.Newton.TerminalOneZeroTransverseConstant
import HC4.Newton.TerminalOneZeroPlanarFibre
import HC4.Newton.TerminalOneZeroAmbientDecoupling
import HC4.Newton.TerminalOneZeroEndpoint
import HC4.Newton.TerminalCoordinatePermutation

/-!
# Automatic infinity assembly for the rank-three autonomous equation

Phases 86 and 87 deliberately separated the finite pole-removal argument from
the single source-infinity certificate.  This file closes that seam.

The source infinity value is computed from the canonical reduced logarithmic
source.  The reduced logarithmic eta numerator has degree strictly below the
square of the source denominator.  The cleared-homogeneous substitution
lemma from `ClearedInfinityEvaluation` therefore forces the canonical target
numerator to vanish at the source infinity value.

Consequently the Phase 82/86 denominator-removal theorem applies with
`etaInfinity = 0`, and the rank-three autonomous target is an honest
polynomial.  Positive source-denominator degree also supplies the
transcendence hypothesis required for target reduction.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Positive degree of the canonical logarithmic-source denominator forces
`phi` itself to have positive degree. -/
theorem phi_natDegree_pos_of_logarithmicSourceDenominator_pos
    (phi : Polynomial K)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    0 < phi.natDegree := by
  have hdvd : logarithmicSourceDenominator phi ∣ phi :=
    logarithmicSource_denominator_dvd phi
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp [logarithmicSourceDenominator, canonicalReducedDenominator,
      polynomialPairRatFunc, HC4.Polynomial.eulerDerivative] at hSourceDegree
  by_contra hnot
  have hphi0 : phi.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hDle : (logarithmicSourceDenominator phi).natDegree ≤ phi.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hphi
  rw [hphi0] at hDle
  exact (Nat.not_lt_of_ge hDle) hSourceDegree

/-- The reduced rank-three target numerator vanishes automatically at the
exceptional source-infinity value.  This is the exact algebraic form of the
manuscript's `eta(infinity)=0`, hence `R(deg phi)=0`, after target reduction. -/
theorem rankThreeTargetNumerator_eval_infinity_eq_zero
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4).eval
        (rationalInfinityValue
          (logarithmicSourceNumerator phi)
          (logarithmicSourceDenominator phi)) = 0 := by
  let rho := logarithmicSourceRatFunc phi
  let eta := logarithmicSourceEtaRatFunc phi
  let A := rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4
  let B := rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4
  let N := logarithmicSourceNumerator phi
  let D := logarithmicSourceDenominator phi
  let H := logarithmicSourceEtaNumerator phi

  have hRhoDegree : 0 < rho.denom.natDegree := by
    simpa [rho, logarithmicSourceRatFunc, logarithmicSourceDenominator,
      canonicalReducedDenominator] using hSourceDegree
  have hTrans : Transcendental K rho :=
    ratFunc_transcendental_of_denom_natDegree_pos rho hRhoDegree
  have hCross : Polynomial.aeval rho A = eta * Polynomial.aeval rho B := by
    simpa [rho, eta, A, B] using
      rankThree_reduced_target_equation hEq hRawD hTrans

  have hPhiDeg : 0 < phi.natDegree :=
    phi_natDegree_pos_of_logarithmicSourceDenominator_pos phi hSourceDegree
  have hDegEq : N.natDegree = D.natDegree := by
    simpa [N, D] using logarithmicSource_num_natDegree_eq_denom phi hPhiDeg
  have hD : D ≠ 0 := by
    simpa [D] using logarithmicSource_denominator_ne_zero phi
  have hDmonic : D.Monic := by
    simpa [D] using logarithmicSource_denominator_monic phi
  have hHdeg : H.natDegree < D.natDegree + D.natDegree := by
    simpa [H, D] using
      logarithmicSourceEtaNumerator_natDegree_lt_two_denom phi hSourceDegree
  have hRho : rho =
      algebraMap (Polynomial K) (RatFunc K) N /
        algebraMap (Polynomial K) (RatFunc K) D := by
    simpa [rho, N, D] using (logarithmicSource_fraction_eq phi).symm
  have hEta : eta =
      algebraMap (Polynomial K) (RatFunc K) H /
        (algebraMap (Polynomial K) (RatFunc K) D) ^ 2 := by
    simp [eta, H, D, logarithmicSourceEtaRatFunc, polynomialPairRatFunc]

  have hAinf : A.eval N.leadingCoeff = 0 :=
    eval_at_infinity_eq_zero_of_autonomous_ratFunc_identity
      hD hDmonic hDegEq hHdeg hRho hEta hCross
  have hNlc : N.leadingCoeff = (phi.natDegree : K) := by
    simpa [N] using
      logarithmicSource_numerator_leadingCoeff_eq_natDegree phi hPhiDeg
  have hInf : rationalInfinityValue N D = (phi.natDegree : K) := by
    simpa [N, D] using
      logarithmicSource_rationalInfinityValue_eq_natDegree phi hPhiDeg
  change A.eval (rationalInfinityValue N D) = 0
  rw [hInf, ← hNlc]
  exact hAinf

/-- The concrete rank-three target denominator is automatically constant:
finite poles are excluded by Phase 86 and the infinity chart is discharged by
the exact Phase 87 degree certificate. -/
theorem rankThreeTargetDenominator_constant_auto
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  have hRhoDegree : 0 < (logarithmicSourceRatFunc phi).denom.natDegree := by
    simpa [logarithmicSourceRatFunc, logarithmicSourceDenominator,
      canonicalReducedDenominator] using hSourceDegree
  have hTrans : Transcendental K (logarithmicSourceRatFunc phi) :=
    ratFunc_transcendental_of_denom_natDegree_pos
      (logarithmicSourceRatFunc phi) hRhoDegree
  have hInf :
      (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4).eval
          (rationalInfinityValue
            (logarithmicSourceRatFunc phi).num
            (logarithmicSourceRatFunc phi).denom) = 0 := by
    simpa [logarithmicSourceNumerator, logarithmicSourceDenominator,
      canonicalReducedNumerator, canonicalReducedDenominator,
      logarithmicSourceRatFunc] using
      rankThreeTargetNumerator_eval_infinity_eq_zero hEq hRawD hSourceDegree
  apply rankThreeTargetDenominator_constant_of_ratFunc_equation
    hEq hRawD hTrans hRhoDegree 0
  simpa using hInf

/-- Automatic denominator removal starting from the Phase 83 fraction-field
rank-three equation. -/
theorem rankThreeTargetDenominator_constant_of_fraction_equation_auto
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : HC4.Polynomial.RankThreeFractionEquation
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  have hPhiDeg :=
    phi_natDegree_pos_of_logarithmicSourceDenominator_pos phi hSourceDegree
  have hphi : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hPhiDeg
    simp at hPhiDeg
  exact rankThreeTargetDenominator_constant_auto
    (rankThree_ratFunc_equation_of_fraction_equation hphi hEq)
    hRawD hSourceDegree

/-- Automatic denominator removal starting directly from singularity of the
substituted rank-three logarithmic core. -/
theorem rankThreeTargetDenominator_constant_of_core_det_zero_auto
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hdet : HC4.Polynomial.RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b := by
  exact rankThreeTargetDenominator_constant_of_fraction_equation_auto
    (HC4.Polynomial.rankThree_fraction_equation_of_core_det_zero hdet)
    hRawD hSourceDegree

/-- Once the reduced target denominator is the nonzero constant `b`, the
canonical target rational function is represented by an honest polynomial. -/
def rankThreeAutonomousPolynomial
    (v2 v3 v4 w1 w2 w3 w4 b : K) : Polynomial K :=
  Polynomial.C b⁻¹ *
    rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4

/-- The reduced rank-three autonomous equation becomes an honest polynomial
autonomous equation after constant-denominator removal. -/
theorem rankThree_polynomial_autonomous_equation_of_constant_denominator
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 b : K}
    (hb : b ≠ 0)
    (hB : rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b)
    (hCross :
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeTargetNumerator v2 v3 v4 w1 w2 w3 w4) =
        logarithmicSourceEtaRatFunc phi *
          Polynomial.aeval (logarithmicSourceRatFunc phi)
            (rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4)) :
    Polynomial.aeval (logarithmicSourceRatFunc phi)
        (rankThreeAutonomousPolynomial v2 v3 v4 w1 w2 w3 w4 b) =
      logarithmicSourceEtaRatFunc phi := by
  unfold rankThreeAutonomousPolynomial
  simp only [map_mul, Polynomial.aeval_C]
  rw [hCross, hB]
  simp only [Polynomial.aeval_C]
  calc
    algebraMap K (RatFunc K) b⁻¹ *
          (logarithmicSourceEtaRatFunc phi * algebraMap K (RatFunc K) b) =
        (algebraMap K (RatFunc K) b⁻¹ * algebraMap K (RatFunc K) b) *
          logarithmicSourceEtaRatFunc phi := by
      ac_rfl
    _ = algebraMap K (RatFunc K) (b⁻¹ * b) *
          logarithmicSourceEtaRatFunc phi := by
      rw [map_mul]
    _ = logarithmicSourceEtaRatFunc phi := by
      simp [hb]

/-- End product of the rational-to-polynomial bridge: from the concrete
rank-three RatFunc equation and positive source degree, obtain an explicit
polynomial autonomous right-hand side whose evaluation is `eta`. -/
theorem exists_rankThree_polynomial_autonomous_equation
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b ∧
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeAutonomousPolynomial v2 v3 v4 w1 w2 w3 w4 b) =
        logarithmicSourceEtaRatFunc phi := by
  obtain ⟨b, hb, hB⟩ := rankThreeTargetDenominator_constant_auto
    hEq hRawD hSourceDegree
  have hRhoDegree : 0 < (logarithmicSourceRatFunc phi).denom.natDegree := by
    simpa [logarithmicSourceRatFunc, logarithmicSourceDenominator,
      canonicalReducedDenominator] using hSourceDegree
  have hTrans : Transcendental K (logarithmicSourceRatFunc phi) :=
    ratFunc_transcendental_of_denom_natDegree_pos
      (logarithmicSourceRatFunc phi) hRhoDegree
  have hCross := rankThree_reduced_target_equation hEq hRawD hTrans
  refine ⟨b, hb, hB, ?_⟩
  exact rankThree_polynomial_autonomous_equation_of_constant_denominator
    hb hB hCross


/-- The rational-to-polynomial bridge starting from the Phase 83 fraction-field
equation. -/
theorem exists_rankThree_polynomial_autonomous_equation_of_fraction_equation
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : HC4.Polynomial.RankThreeFractionEquation
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b ∧
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeAutonomousPolynomial v2 v3 v4 w1 w2 w3 w4 b) =
        logarithmicSourceEtaRatFunc phi := by
  have hPhiDeg :=
    phi_natDegree_pos_of_logarithmicSourceDenominator_pos phi hSourceDegree
  have hphi : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hPhiDeg
    simp at hPhiDeg
  exact exists_rankThree_polynomial_autonomous_equation
    (rankThree_ratFunc_equation_of_fraction_equation hphi hEq)
    hRawD hSourceDegree

/-- The rational-to-polynomial bridge starting directly from singularity of
the substituted rank-three logarithmic core. -/
theorem exists_rankThree_polynomial_autonomous_equation_of_core_det_zero
    [IsAlgClosed K]
    {phi : Polynomial K} {v2 v3 v4 w1 w2 w3 w4 : K}
    (hdet : HC4.Polynomial.RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b ∧
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeAutonomousPolynomial v2 v3 v4 w1 w2 w3 w4 b) =
        logarithmicSourceEtaRatFunc phi := by
  exact exists_rankThree_polynomial_autonomous_equation_of_fraction_equation
    (HC4.Polynomial.rankThree_fraction_equation_of_core_det_zero hdet)
    hRawD hSourceDegree


/-- Terminal certificate for the rank-three local branch: the rational
autonomous target has a nonzero constant denominator and therefore becomes
an honest polynomial autonomous equation. -/
def HasRankThreePolynomialTerminalCertificate
    {phi : Polynomial K}
    (v2 v3 v4 w1 w2 w3 w4 : K) : Prop :=
  ∃ b : K, b ≠ 0 ∧
    rankThreeTargetDenominator v2 v3 v4 w1 w2 w3 w4 = Polynomial.C b ∧
    Polynomial.aeval (logarithmicSourceRatFunc phi)
        (rankThreeAutonomousPolynomial v2 v3 v4 w1 w2 w3 w4 b) =
      logarithmicSourceEtaRatFunc phi

/-- The green Phase 88 rank-three theorem is exactly the polynomial terminal
certificate needed by the local corank classification. -/
theorem hasRankThreePolynomialTerminalCertificate
    [IsAlgClosed K]
    {phi : Polynomial K}
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hEq : RankThreeRatFuncEquation phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    HasRankThreePolynomialTerminalCertificate
      (phi := phi) v2 v3 v4 w1 w2 w3 w4 := by
  exact
    exists_rankThree_polynomial_autonomous_equation
      hEq hRawD hSourceDegree

/-- Core-determinant-zero form of the rank-three terminal certificate. -/
theorem hasRankThreePolynomialTerminalCertificate_of_core_det_zero
    [IsAlgClosed K]
    {phi : Polynomial K}
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hdet : HC4.Polynomial.RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4)
    (hRawD :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        v2 v3 v4 w1 w2 w3 w4 ≠ 0)
    (hSourceDegree : 0 < (logarithmicSourceDenominator phi).natDegree) :
    HasRankThreePolynomialTerminalCertificate
      (phi := phi) v2 v3 v4 w1 w2 w3 w4 := by
  exact
    exists_rankThree_polynomial_autonomous_equation_of_core_det_zero
      hdet hRawD hSourceDegree

end

end HC4.RationalRigidity
