import HC4.Polynomial.RankThreeCubicDetOneWeightFiveAdjugateConstraint
import HC4.Polynomial.RankThreeCubicDetOneWeightedRepair
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Source weight-five adjugate constraint under the genuine pole quotient

The adjugate/trace pairing commutes with every ring homomorphism,
including evaluation of the original source at a longitudinal anchor
followed by quotienting by a genuine denominator pole.

In particular, det Hess F = 1 forces the first quadratic repair
pairing to vanish in the *same* quotient ring in which the cubic
pole residue is constructed. This is a necessary condition, not
yet a contradiction to the nonzero lower-layer repair.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators
noncomputable section

variable {R S ι : Type*} [CommRing R] [CommRing S]
variable [Fintype ι] [DecidableEq ι]

/-- First-variation adjugate pairing is preserved by arbitrary
commutative-ring homomorphisms, without invertibility assumptions. -/
theorem ringHom_map_adjugate_trace
    (φ : R →+* S) (A B : Matrix ι ι R) :
    ((φ.mapMatrix A).adjugate * φ.mapMatrix B).trace =
      φ ((A.adjugate * B).trace) := by
  rw [← RingHom.map_adjugate φ A,
    ← (φ.mapMatrix).map_mul (A.adjugate) B]
  exact (AddMonoidHom.map_trace φ.toAddMonoidHom (A.adjugate * B)).symm

end
end HC4.Polynomial

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The same genuine denominator-prime quotient receives the first
source quadratic adjugate constraint. No actual pole hypothesis is
needed for this identity: it holds in every such quotient. -/
theorem sourceCubic_detOne_slicedPole_firstCorrection_trace_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (a : K) (p : B3 K) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let L3 := initialForm transverseCubicWeight 3 F
    let L2 := initialForm transverseCubicWeight 2 F
    ((φ.mapMatrix (hessian L3)).adjugate *
      φ.mapMatrix (hessian L2)).trace = 0 := by
  classical
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
    q.comp (referenceSlice a).toRingHom
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  have hzero :
      ((hessian L3).adjugate * hessian L2).trace = 0 :=
    sourceCubic_detOne_firstCorrection_adjugate_trace_zero
      F hcap hdetOne
  change ((φ.mapMatrix (hessian L3)).adjugate *
      φ.mapMatrix (hessian L2)).trace = 0
  rw [ringHom_map_adjugate_trace φ (hessian L3) (hessian L2),
    hzero, map_zero]

end
end HC4.Polynomial.RankThreeCubic
