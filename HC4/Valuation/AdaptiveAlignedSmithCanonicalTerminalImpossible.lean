import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalRankThreeFirstContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalRigidityData
import Mathlib.Tactic

/-!
# A18.5.74: terminal singular carrier to rigidity contradiction

A18.5.13 gives every terminal node of the well-founded rank-one trace an
honest singular polynomial carrier.  At positive raw defect this is the actual
terminal special fibre; at raw defect zero it is the genuine nonzero maximal
ordinary face selected in A18.5.12.

A18.5.64 packages exactly the algebraic data consumed by the closed A18.5.63
RationalRigidity contradiction.  This file is the trace-facing assembly layer
between those two interfaces.

Crucially, this adapter does not identify the general affine first-contact
line of A18.5.65--73 with the older integral finite-segment model.  That would
silently reintroduce the divisibility condition which the affine line was
introduced to remove.  Instead the carrier polynomial and its Hessian
singularity are discharged here once and for all; the remaining hypotheses are
precisely the genuine balanced integral-line support and endpoint certificates.
When those certificates are available, terminality is contradictory by one
invocation of A18.5.63.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalTerminalSingularCarrier

/-- The actual singular polynomial carried by a terminal node.

At zero raw defect this is the selected maximal ordinary top face; at positive
raw defect it is the represented terminal special fibre itself. -/
noncomputable def polynomial
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity}
    (C : AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T) :
    MvPolynomial (Fin 4) K :=
  match C with
  | .zeroDefect data => data.face
  | .positiveDefect _ _ => T.specialFiber

/-- The carrier polynomial is Hessian-singular in both determinant-clock
regimes. -/
theorem polynomial_hessian_zero
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity}
    (C : AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T) :
    HC4.Polynomial.hessianDeterminant C.polynomial = 0 := by
  cases C with
  | zeroDefect data =>
      exact data.hessian_zero
  | positiveDefect rawDefect_pos hzero =>
      exact hzero

/-- Package the genuine balanced rank-three line geometry of a terminal
singular carrier into the exact A18.5.64 RationalRigidity interface.

All determinant-clock bookkeeping is internal to the carrier.  Callers supply
only the actual line geometry and endpoint survival. -/
noncomputable def toSupportedBalancedRankThreeData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity}
    (C : AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T)
    (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b C.polynomial)
    (hsupported : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M C.polynomial)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) C.polynomial ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) C.polynomial ≠ 0) :
    AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData (K := K) where
  a := a
  b := b
  a_pos := ha
  b_pos := hb
  v2 := v2
  v3 := v3
  v4 := v4
  u1 := u1
  u2 := u2
  u3 := u3
  u4 := u4
  M := M
  v2_pos := hv2
  v3_pos := hv3
  v4_pos := hv4
  M_pos := hM
  u1_pos := hu1
  polynomial := C.polynomial
  balanced := hbalanced
  supported := hsupported
  start_ne := hstart
  end_ne := hend
  hessian_zero := C.polynomial_hessian_zero

/-- Once the genuine terminal line certificates have been exposed, the
terminal singular carrier is impossible by the already-closed A18.5.63
RationalRigidity theorem. -/
theorem impossible_of_supportedBalancedRankThree
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity}
    (C : AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T)
    (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b C.polynomial)
    (hsupported : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M C.polynomial)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) C.polynomial ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) C.polynomial ≠ 0) :
    False := by
  exact (C.toSupportedBalancedRankThreeData
    a b ha hb
    v2 v3 v4 u1 u2 u3 u4 M
    hv2 hv3 hv4 hM hu1
    hbalanced hsupported hstart hend).impossible

end AdaptiveAlignedSmithCanonicalTerminalSingularCarrier

/-- **A18.5.74 — trace-facing terminal impossibility.**

A finite rank-one termination trace cannot end in a terminal whose canonical
singular carrier has been exposed as a genuine balanced supported rank-three
line.  The proof is now exactly the terminal-carrier constructor followed by
A18.5.63. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.terminal_impossible_of_supportedBalancedRankThree
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b trace.reachedSingularCarrier.polynomial)
    (hsupported : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M trace.reachedSingularCarrier.polynomial)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0)
        trace.reachedSingularCarrier.polynomial ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M)
        trace.reachedSingularCarrier.polynomial ≠ 0) :
    False := by
  exact trace.reachedSingularCarrier.impossible_of_supportedBalancedRankThree
    a b ha hb
    v2 v3 v4 u1 u2 u3 u4 M
    hv2 hv3 hv4 hM hu1
    hbalanced hsupported hstart hend

end

end HC4.Valuation
