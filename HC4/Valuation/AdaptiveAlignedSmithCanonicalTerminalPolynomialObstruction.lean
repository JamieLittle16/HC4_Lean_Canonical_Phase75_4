import HC4.Valuation.AdaptiveAlignedSmithSingletonRankThreeImpossible
import HC4.Polynomial.ComplementarySupportedEdgeImpossible
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalRigidityData

/-!
# A18.5.89: unconditional polynomial obstructions at a rank-three terminal

The final terminal consumer should not force every retained geometric branch
through one representation.  The current library has three genuinely
independent, already-closed polynomial contradictions:

* a positive exact singleton Smith fibre with a first longitudinal departure;
* a genuine complementary support edge (or exposed complementary edge); and
* the fully supported balanced rank-three edge package.

This file packages those alternatives behind one lossless terminal-facing
interface.  No implication from abstract Hessian/Schur rank-three geometry is
asserted here: later producer lemmas must construct one of these honest
polynomial objects from the retained terminal provenance.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact unconditional polynomial obstruction which is already known to be
impossible.  The constructors intentionally retain the complete hypotheses of
the corresponding verified endpoint theorem. -/
inductive AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction : Type (u + 1)
  | positiveSingleton
      (F : MvPolynomial (Fin 4) K)
      (e : SmithSupportExponent)
      (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
      (departure : HasFirstExactSmithExponentLongitudinalDeparture F e)
      (hessian_zero :
        hessianDeterminant
          (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0)
  | complementarySupported
      (a1 a2 b1 b2 h k M : ℕ)
      (F : MvPolynomial (Fin 4) K)
      (ha1 : 0 < a1) (ha2 : 0 < a2)
      (hb1 : 0 < b1) (hb2 : 0 < b2)
      (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
      (supported : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M F)
      (start_ne :
        MvPolynomial.coeff
          (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M 0) F ≠ 0)
      (end_ne :
        MvPolynomial.coeff
          (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M M) F ≠ 0)
      (hessian_zero : hessianDeterminant F = 0)
  | complementaryExposed
      (P : MvPolynomial (Fin 4) K)
      (w : Fin 4 → ℤ) (level : ℤ)
      (a1 a2 b1 b2 h k M : ℕ)
      (ha1 : 0 < a1) (ha2 : 0 < a2)
      (hb1 : 0 < b1) (hb2 : 0 < b2)
      (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
      (weight_bound : IsWeightLE w level P)
      (carrier_hessian_zero : hessianDeterminant P = 0)
      (supported : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M
        (initialForm w level P))
      (start_ne :
        MvPolynomial.coeff
          (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M 0)
          (initialForm w level P) ≠ 0)
      (end_ne :
        MvPolynomial.coeff
          (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M M)
          (initialForm w level P) ≠ 0)
  | balancedRankThree
      (data : AdaptiveAlignedSmithTerminalSupportedBalancedRankThreeData (K := K))

/-- Every completed polynomial obstruction is contradictory using only the
already-verified endpoint theorems. -/
theorem AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction.impossible
    [IsAlgClosed K]
    (O : AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K)) : False := by
  cases O with
  | positiveSingleton F e hb hc hd departure hessian_zero =>
      exact positive_singletonSmithFiber_impossible
        hb hc hd departure hessian_zero
  | complementarySupported a1 a2 b1 b2 h k M F
      ha1 ha2 hb1 hb2 hM hh hk supported start_ne end_ne hessian_zero =>
      exact complementary_supported_edge_hessian_impossible
        ha1 ha2 hb1 hb2 hM hh hk supported start_ne end_ne hessian_zero
  | complementaryExposed P w level a1 a2 b1 b2 h k M
      ha1 ha2 hb1 hb2 hM hh hk weight_bound carrier_hessian_zero
      supported start_ne end_ne =>
      exact complementary_exposed_edge_hessian_impossible
        ha1 ha2 hb1 hb2 hM hh hk weight_bound carrier_hessian_zero
        supported start_ne end_ne
  | balancedRankThree data =>
      exact data.impossible

end

end HC4.Valuation
