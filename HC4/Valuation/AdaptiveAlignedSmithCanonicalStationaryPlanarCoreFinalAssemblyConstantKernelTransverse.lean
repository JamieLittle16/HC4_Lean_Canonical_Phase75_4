import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyLosslessAxis
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurSourceCoordinateKernel
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLinearCornerElimination
import HC4.Newton.TerminalOneZeroAffineRecovery
import Mathlib.Tactic

/-!
# Final assembly A16: constant RS2 kernel back to the literal source

A15 leaves one early-Schur residue in a constant kernel direction of the
auxiliary special four-block.  Before the final saturated-kernel restart can
use that direction, two source-honesty issues have to be removed:

* the auxiliary swap/shear/permutation Hessian chart must be undone; and
* the resulting constant kernel cannot be purely longitudinal, because the
  common A11 source packet still contains a genuine later longitudinal layer
  at the same transverse Smith exponent.

This file proves both facts.  The residual constant-RS2 branch therefore
carries a nonzero *transverse* constant kernel direction of the literal
right-recentered special-fibre Hessian.  This is the exact input for the final
marked-axis-preserving source straightening / saturated-kernel spend.

No residual is declared progress here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Constant-vector analogue of the B6 swap/shear chart removal. -/
def constantCoordinateDirectionForChartKind
    (kind : AdaptiveAlignedRightRecenteredHessianChartKind)
    (v : Fin 4 → K) : Fin 4 → K :=
  match kind with
  | .coordinate => v
  | .swap02 => swap02KernelVector v
  | .shear02 => shear02KernelVector v

/-- Remove both the auxiliary swap/shear and the retained coordinate
permutation from a constant kernel direction. -/
def literalConstantSourceDirection
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (v : Fin 4 → K) : Fin 4 → K :=
  sourceCoordinateKernelVector C.chartData.chart.rho
    (constantCoordinateDirectionForChartKind C.chartData.chart.kind v)

/-- A constant nonzero kernel direction of the Hessian of the *literal honest
right-recentered special fibre*.  Unlike `ConstantSpecialSourceKernelData`,
there is no remaining chart bookkeeping in this structure. -/
structure LiteralConstantSpecialSourceKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  direction : Fin 4 → K
  direction_ne_zero : direction ≠ 0
  kernel :
    (HC4.Polynomial.hessian
      (polynomialFamilySpecialFiber C.family)).mulVec
        (fun i => MvPolynomial.C (direction i)) = 0

private theorem constantCoordinateDirectionForChartKind_ne_zero
    (kind : AdaptiveAlignedRightRecenteredHessianChartKind)
    {v : Fin 4 → K}
    (hv : v ≠ 0) :
    constantCoordinateDirectionForChartKind kind v ≠ 0 := by
  cases kind with
  | coordinate => simpa [constantCoordinateDirectionForChartKind] using hv
  | swap02 =>
      intro hzero
      apply hv
      apply swap02KernelVector_injective (R := K)
      simpa [constantCoordinateDirectionForChartKind] using hzero
  | shear02 =>
      intro hzero
      apply hv
      apply shear02KernelVector_injective (R := K)
      simpa [constantCoordinateDirectionForChartKind] using hzero

/-- Undo the complete retained Hessian chart on a constant projective-kernel
residue.  Since swap, shear and permutation are all literal source-coordinate
changes, constancy of the direction is preserved exactly. -/
noncomputable def ConstantSpecialSourceKernelData.toLiteralConstantSpecialSourceKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : ConstantSpecialSourceKernelData C) :
    LiteralConstantSpecialSourceKernelData C := by
  let kind := C.chartData.chart.kind
  let rho := C.chartData.chart.rho
  let vcoord := constantCoordinateDirectionForChartKind kind D.direction
  let wcoord : Fin 4 → MvPolynomial (Fin 4) K :=
    fun i => MvPolynomial.C (vcoord i)

  have hvcoord : vcoord ≠ 0 := by
    dsimp [vcoord, kind]
    exact constantCoordinateDirectionForChartKind_ne_zero
      C.chartData.chart.kind D.direction_ne_zero

  have hwcoord : wcoord ≠ 0 := by
    intro hzero
    apply hvcoord
    funext i
    have hi := congrFun hzero i
    simpa [wcoord] using hi

  have hcoordKernel : C.coordinateSpecialFourBlock.matrix.mulVec wcoord = 0 := by
    generalize hkind : C.chartData.chart.kind = chartKind
    cases chartKind with
    | coordinate =>
        have hker := D.kernel
        rw [C.specialFourBlock_eq_coordinateSpecialFourBlock_of_coordinate hkind] at hker
        simpa [wcoord, vcoord, kind, constantCoordinateDirectionForChartKind, hkind]
          using hker
    | swap02 =>
        have hker := D.kernel
        rw [C.specialFourBlock_eq_swap02_coordinateSpecialFourBlock_of_swap02 hkind] at hker
        have hback :=
          C.coordinateSpecialFourBlock.mulVec_swap02KernelVector_eq_zero
            (fun i => MvPolynomial.C (D.direction i)) hker
        simpa [wcoord, vcoord, kind, constantCoordinateDirectionForChartKind,
          hkind, swap02KernelVector] using hback
    | shear02 =>
        have hker := D.kernel
        rw [C.specialFourBlock_eq_shear02_coordinateSpecialFourBlock_of_shear02 hkind] at hker
        have hback :=
          C.coordinateSpecialFourBlock.mulVec_shear02KernelVector_eq_zero
            (fun i => MvPolynomial.C (D.direction i)) hker
        have hwcoord_shear :
            wcoord =
              shear02KernelVector
                (fun i => MvPolynomial.C (D.direction i)) := by
          funext i
          fin_cases i <;>
            simp [wcoord, vcoord, kind, constantCoordinateDirectionForChartKind,
              hkind, shear02KernelVector]
        rw [hwcoord_shear]
        exact hback

  let Q : C.CoordinateSpecialKernelData := {
    vector := wcoord
    vector_ne_zero := hwcoord
    kernel := hcoordKernel
  }
  let S := Q.toSourceCoordinateSpecialKernelData
  let vsource := sourceCoordinateKernelVector rho vcoord

  have hvsource : vsource ≠ 0 := by
    intro hzero
    apply hvcoord
    apply sourceCoordinateKernelVector_injective (R := K) rho
    simpa [vsource] using hzero

  have hvector :
      S.vector = fun i => MvPolynomial.C (vsource i) := by
    change sourceCoordinateKernelVector rho wcoord =
      fun i => MvPolynomial.C (vsource i)
    funext i
    simp [sourceCoordinateKernelVector, wcoord, vsource]

  refine {
    direction := vsource
    direction_ne_zero := hvsource
    kernel := ?_
  }
  have hker := S.kernel
  rw [hvector] at hker
  exact hker

/-- Directional derivative along a constant source vector. -/
noncomputable def constantSourceDirectionalDerivative
    (F : MvPolynomial (Fin 4) K)
    (v : Fin 4 → K) : MvPolynomial (Fin 4) K :=
  ∑ i : Fin 4, MvPolynomial.C (v i) * MvPolynomial.pderiv i F

/-- Differentiating the constant directional derivative is exactly one row of
`Hess(F) * v`. -/
theorem pderiv_constantSourceDirectionalDerivative
    (F : MvPolynomial (Fin 4) K)
    (v : Fin 4 → K)
    (r : Fin 4) :
    MvPolynomial.pderiv r (constantSourceDirectionalDerivative F v) =
      (HC4.Polynomial.hessian F).mulVec
        (fun i => MvPolynomial.C (v i)) r := by
  classical
  simp only [constantSourceDirectionalDerivative, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    Matrix.mulVec, dotProduct, HC4.Polynomial.hessian_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pderiv_comm_commRing]
  ac_rfl

namespace LiteralConstantSpecialSourceKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- The literal constant Hessian kernel integrates once: the honest special
fibre has zero directional derivative along that vector.  The integration
constant vanishes because the right-recentered source has zero linear jet. -/
theorem directionalDerivative_eq_zero
    (D : LiteralConstantSpecialSourceKernelData C) :
    constantSourceDirectionalDerivative
        (polynomialFamilySpecialFiber C.family) D.direction = 0 := by
  let F := polynomialFamilySpecialFiber C.family
  let G := constantSourceDirectionalDerivative F D.direction

  have hp (r : Fin 4) : MvPolynomial.pderiv r G = 0 := by
    rw [show G = constantSourceDirectionalDerivative F D.direction by rfl]
    rw [pderiv_constantSourceDirectionalDerivative]
    exact congrFun D.kernel r

  have hconstant : G = MvPolynomial.C (MvPolynomial.coeff 0 G) := by
    exact finFour_eq_C_of_all_pderiv_eq_zero G
      (hp 0) (hp 1) (hp 2) (hp 3)

  have hlinear (i : Fin 4) :
      MvPolynomial.coeff 0 (MvPolynomial.pderiv i F) = 0 := by
    rw [coeff_pderiv_mixedDegree]
    simpa [F] using C.specialFiber_linearCoeff_zero i

  have hA : MvPolynomial.coeff 0 (standardTwoZeroA F) = 0 := by
    change MvPolynomial.coeff 0 (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    exact hlinear (2 : Fin 4)
  have hC : MvPolynomial.coeff 0 (standardTwoZeroC F) = 0 := by
    change MvPolynomial.coeff 0 (MvPolynomial.pderiv (3 : Fin 4) F) = 0
    exact hlinear (3 : Fin 4)

  have hcoeff : MvPolynomial.coeff 0 G = 0 := by
    classical
    simp [G, constantSourceDirectionalDerivative, Fin.sum_univ_four,
      MvPolynomial.coeff_C_mul, hlinear, hA, hC]

  have hGzero : G = 0 := by
    rw [hconstant, hcoeff]
    simp
  simpa [G, F] using hGzero

end LiteralConstantSpecialSourceKernelData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Constant RS2 kernel cannot point only along the marked axis -/

/-- Once the A11 first positive longitudinal departure is retained, a literal
constant source-kernel direction cannot be purely longitudinal.  If it were,
the zero directional derivative would force `∂₀F = 0`; but the later occupied
same-Smith-exponent monomial has positive longitudinal exponent. -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.exists_transverse_of_literalConstantKernel
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker}
    (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.LiteralConstantSpecialSourceKernelData C) :
    ∃ j : Fin 4, j ≠ (0 : Fin 4) ∧ D.direction j ≠ 0 := by
  by_cases h1 : D.direction (1 : Fin 4) ≠ 0
  · exact ⟨1, by decide, h1⟩
  by_cases h2 : D.direction (2 : Fin 4) ≠ 0
  · exact ⟨2, by decide, h2⟩
  by_cases h3 : D.direction (3 : Fin 4) ≠ 0
  · exact ⟨3, by decide, h3⟩

  have hv1 : D.direction (1 : Fin 4) = 0 := not_ne_iff.mp h1
  have hv2 : D.direction (2 : Fin 4) = 0 := not_ne_iff.mp h2
  have hv3 : D.direction (3 : Fin 4) = 0 := not_ne_iff.mp h3
  have hv0 : D.direction (0 : Fin 4) ≠ 0 := by
    intro hv0
    apply D.direction_ne_zero
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2, hv3]

  let F := polynomialFamilySpecialFiber C.family
  have hdir := D.directionalDerivative_eq_zero
  have hp0 : MvPolynomial.pderiv (0 : Fin 4) F = 0 := by
    change
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.constantSourceDirectionalDerivative
        F D.direction = 0 at hdir
    simp [AdaptiveAlignedSmithRankOneClosingSourceCarrier.constantSourceDirectionalDerivative,
      Fin.sum_univ_four, hv1, hv2, hv3] at hdir
    exact hdir.resolve_left hv0

  rcases P.support_pair with ⟨n, q, hq, hn, hnq⟩
  have hexp :=
    exponent_eq_zero_of_pderiv_eq_zero
      (0 : Fin 4) F hp0
      ((smithTransverseExponent
        S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q))
      (by simpa [F, AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using hnq)
  have hnqzero : n + q = 0 := by
    simpa using hexp
  omega

/-! ## A16 frontier -/

/-- Constant-RS2 residue after all chart bookkeeping has been removed and the
surviving source direction is known to have a genuine transverse component. -/
structure AdaptiveAlignedSmithConstantRS2TransverseKernelData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) where
  carrier : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker
  firstActual_lt :
    carrier.firstActualLayerOrder < S.blocker.aligned.endpoint.defect
  tangential :
    carrier.IsClosingClockSchurTangentialOrder carrier.firstActualLayerOrder
  rs2 : carrier.ConstantSpecialSchurKernelLineRS2PreassemblyData
  kernel : carrier.LiteralConstantSpecialSourceKernelData
  transverse : ∃ j : Fin 4, j ≠ (0 : Fin 4) ∧ kernel.direction j ≠ 0

/-- A15 geometry with the only remaining RS2 constructor strengthened to a
literal transverse source-kernel packet. -/
inductive AdaptiveAlignedSmithCanonicalConstantKernelTransverseTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | rs2TransverseConstantKernel
      (data : AdaptiveAlignedSmithConstantRS2TransverseKernelData S)
  | canonicalLosslessAxis
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : C.DirectClosingCanonicalSquareLosslessAxisTerminalCoreData heq)
  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)
  | planarRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket (0 : Fin 4) 1 2 P.degree P.packet)
  | wSquareRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket (0 : Fin 4) 3 2 P.degree P.packet)
  | sectionGaugeKilled
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : C.DirectClosingPositiveSectionGaugeStep)
      (hkilled : G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)
  | sectionGaugeOrderRaised
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : C.DirectClosingPositiveSectionGaugeStep)
      (hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index) hnew)

structure AdaptiveAlignedSmithCanonicalConstantKernelTransverseTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalConstantKernelTransverseTerminalGeometry stationary

inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreConstantKernelTransverseOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | local (P : AdaptiveAlignedSmithCanonicalConstantKernelTransverseTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A16 constant-kernel source refinement.**

The A15 constant-RS2 branch is transported all the way back to the literal
right-recentered source.  Its constant Hessian kernel integrates to a zero
source directional derivative; the common first longitudinal departure then
forces that direction to have a transverse component.  Every other A15
terminal geometry is retained unchanged. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreConstantKernelTransverseFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreConstantKernelTransverseOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreLosslessAxisFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      cases P.geometry with
      | rs2ConstantSourceKernel C hlt htangential R kernel =>
          let literal := kernel.toLiteralConstantSpecialSourceKernelData
          have htrans := P.source.exists_transverse_of_literalConstantKernel literal
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rs2TransverseConstantKernel {
              carrier := C
              firstActual_lt := hlt
              tangential := htangential
              rs2 := R
              kernel := literal
              transverse := htrans
            }
          }
      | canonicalLosslessAxis C heq data =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .canonicalLosslessAxis C heq data
          }
      | zeroSchurSourceReady C source =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .zeroSchurSourceReady C source
          }
      | planarRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .planarRigid hall Q hrigid
          }
      | wSquareRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .wSquareRigid hall Q hrigid
          }
      | sectionGaugeKilled C heq G hkilled =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeKilled C heq G hkilled
          }
      | sectionGaugeOrderRaised C heq G hnew hstrict =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeOrderRaised C heq G hnew hstrict
          }

end

end HC4.Valuation
