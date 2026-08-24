import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostTransverseKernel
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyCoherentZeroJetAxis
import HC4.Valuation.AdaptiveRigidMatrixExposure
import Mathlib.Tactic

/-!
# Final assembly A17.2A: lossless canonical wall -> exact staircase input

A17.1 removes the transverse constant-kernel RS2 residue.  Its surviving
canonical wall is deliberately lossless: A15 retained the literal zero-order
wall face, while A11 retained the first later source monomial over the same
Smith exponent.  The final staircase argument must use those facts on one and
the same right-recentered polynomial family.

This file performs only that provenance assembly.  It does not call the
canonical wall progress and it does not declare a one-axis face contradictory.
Instead it packages the exact input needed by the finite staircase theorem:

* the coherent source -> zero-jet -> axis packet recomputed from the retained
  low-dimensional wall face;
* the exact positive polynomial-family Hessian clock;
* hence vanishing Hessian determinant on the literal special fibre;
* the canonical first later longitudinal departure on that very special fibre.

The next A17.2 file can therefore be a pure finite polynomial argument, with no
remaining chart/source identification hidden inside it.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The exact data on which the final canonical finite-staircase argument is
allowed to depend.  Every field refers to the literal `C.family`; no auxiliary
Schur chart or reconstructed polynomial is present. -/
structure DirectClosingCanonicalSquareStaircaseReadyData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
    (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect) : Prop where
  coherent : DirectClosingCanonicalSquareCoherentZeroJetAxisTerminalCoreData C heq
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K) C.family
      S.blocker.aligned.endpoint.defect
  clock_pos : 0 < S.blocker.aligned.endpoint.defect
  special_hessianDeterminant_zero :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber C.family) = 0
  firstDeparture :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber C.family)
      S.blocker.exponent

/-- A positive pure parameter Hessian clock vanishes after specialization to
`τ = 0`.  This is the family-to-special-fibre determinant fact used by the
staircase and is independent of the canonical wall geometry. -/
theorem specialFiber_hessianDeterminant_eq_zero_of_familyDefect_pos
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpos : 0 < B.aligned.endpoint.defect) :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber C.family) = 0 := by
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := C.family_hessianDefect
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  have hne : B.aligned.endpoint.defect ≠ 0 := Nat.ne_of_gt hpos
  simp [hne]

/-- The A11 first-departure certificate is definitionally on the same literal
right-recentered family carried by a rank-one closing source carrier. -/
theorem terminalSource_firstDeparture_on_carrierFamily
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber C.family)
      S.blocker.exponent := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using
    source.firstDeparture

/-- A lossless A15 canonical packet plus the common A11 source packet produces
one fully coherent staircase-ready object.  The separately stored A15 `axis`
field is intentionally ignored: the zero-jet and axis data are recomputed from
the retained low-dimensional face. -/
theorem DirectClosingCanonicalSquareLosslessAxisTerminalCoreData.toStaircaseReady
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker}
    {heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect}
    (data : DirectClosingCanonicalSquareLosslessAxisTerminalCoreData C heq)
    (source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (hpos : 0 < S.blocker.aligned.endpoint.defect) :
    Nonempty (DirectClosingCanonicalSquareStaircaseReadyData S source C heq) := by
  rcases data.toCoherentZeroJetAxisTerminalCore with ⟨coherent⟩
  exact ⟨{
    coherent := coherent
    hessianDefect := C.family_hessianDefect
    clock_pos := hpos
    special_hessianDeterminant_zero :=
      specialFiber_hessianDeterminant_eq_zero_of_familyDefect_pos C hpos
    firstDeparture := terminalSource_firstDeparture_on_carrierFamily source C
  }⟩

namespace DirectClosingCanonicalSquareStaircaseReadyData

/-- The staircase-ready packet exposes two actual monomials on its literal
special fibre at one common transverse Smith exponent and distinct
longitudinal levels. -/
theorem support_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S}
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker}
    {heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareStaircaseReadyData S source C heq) :
    ∃ n q : ℕ,
      0 < q ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) ∈
        (polynomialFamilySpecialFiber C.family).support ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) ∈
        (polynomialFamilySpecialFiber C.family).support :=
  D.firstDeparture.support_pair

/-- The same two-layer certificate also records the strict ordinary-degree
increase which orients the finite staircase. -/
theorem ordinaryDegree_strict
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S}
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker}
    {heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareStaircaseReadyData S source C heq) :
    ∃ n q : ℕ,
      0 < q ∧
      HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) <
        HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent
            S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) :=
  D.firstDeparture.ordinaryDegree_strict

end DirectClosingCanonicalSquareStaircaseReadyData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
