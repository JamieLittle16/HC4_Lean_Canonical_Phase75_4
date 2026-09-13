import HC4.RationalRigidity.RankThreeBalancedHomogeneousImpossible
import Mathlib.Tactic

/-!
# A18.5.64: exact terminal interface for balanced rank-three rigidity

The terminal splice should have one explicit algebraic target.  Rather than
repeating the long input list of the final RationalRigidity theorem in every
Smith/Newton adapter, this file packages exactly those inputs and no more.

No new geometric assertion is made here.  In particular, support on a genuine
rank-three line, endpoint survival, balance, and Hessian singularity remain
proof obligations for the terminal geometry adapters that construct this
record.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The exact data consumed by
`HC4.RationalRigidity.supported_balanced_rankThree_edge_impossible`.

Keeping the carrier polynomial explicit lets the positive-defect terminal use
its actual special fibre, while the zero-defect terminal may use the singular
maximal ordinary face selected by A18.5.12. -/
structure AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b

  v2 : ℕ
  v3 : ℕ
  v4 : ℕ
  u1 : ℕ
  u2 : ℕ
  u3 : ℕ
  u4 : ℕ
  M : ℕ

  v2_pos : 0 < v2
  v3_pos : 0 < v3
  v4_pos : 0 < v4
  M_pos : 0 < M
  u1_pos : 0 < u1

  polynomial : MvPolynomial (Fin 4) K

  balanced : HasBalancedMvSupport a b polynomial
  supported : IsSupportedOnRankThreeLine
    v2 v3 v4 u1 u2 u3 u4 M polynomial
  start_ne :
    MvPolynomial.coeff
      (rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M 0) polynomial ≠ 0
  end_ne :
    MvPolynomial.coeff
      (rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M M) polynomial ≠ 0
  hessian_zero : hessianDeterminant polynomial = 0

/-- Any completed terminal rigidity package is contradictory by the already
closed A18.5.63 RationalRigidity endgame. -/
theorem AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData.impossible
    (D : AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData (K := K)) :
    False := by
  exact
    HC4.RationalRigidity.supported_balanced_rankThree_edge_impossible
      D.a_pos D.b_pos
      D.v2_pos D.v3_pos D.v4_pos D.M_pos D.u1_pos
      D.balanced D.supported D.start_ne D.end_ne D.hessian_zero

end

end HC4.Valuation
