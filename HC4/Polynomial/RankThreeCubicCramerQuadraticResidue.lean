module

public import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
public import HC4.Polynomial.RankThreeCubicPoleDeterminant
public import Mathlib.Tactic

/-!
# Cramer's numerator obeys the quadratic transport residue equation

Given a rational transverse characteristic H V = r and a polynomial
quadratic transport identity along that characteristic, the exact
Cramer numerator A = adj(H) r obeys

  quadraticFamilyEval (Q mod p) (C (A mod p)) = 0

for every domain-valued residue map killing det(H). No squarefree determinant,
rank-two residue hypothesis, or extra source assumption is required
to derive this equality. Nonvanishing of A mod p remains separate.

This theorem is a base-ring algebraic bridge. The source coefficient
descent and source transport modules provide its hypotheses.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K]

namespace RankThreeCubicCramerQuadraticResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

end RankThreeCubicCramerQuadraticResidue

open RankThreeCubicCramerQuadraticResidue (B3 F3)

/-- The actual Cramer numerator, not an independently chosen kernel
vector, is annihilated by the transported quadratic family under
any homomorphism into a domain that kills det H.

At an irreducible determinant factor p, instantiate the residue map
with the quotient K[y] → K[y]/(p). -/
theorem cramerNumerator_quadraticResidue
    {E : Type*} [CommRing E] [IsDomain E]
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (res : B3 K →+* E) (hdetzero : res H.det = 0)
    (Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K))
    (b : B3 K)
    (htransport :
      quadraticFamilyEval
        (fun i j : Fin 3 =>
          (Q i j).map (algebraMap (B3 K) (F3 K)))
        (fun i : Fin 3 =>
          _root_.Polynomial.C
              (algebraMap (B3 K) (F3 K) (MvPolynomial.X i)) +
            _root_.Polynomial.X *
              _root_.Polynomial.C (V i)) =
        _root_.Polynomial.C (algebraMap (B3 K) (F3 K) b)) :
    quadraticFamilyEval
        (fun i j : Fin 3 => (Q i j).map res)
        (fun i : Fin 3 =>
          _root_.Polynomial.C (res ((H.adjugate *ᵥ r) i))) = 0 := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hinj : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  have hscale (i : Fin 3) :
      g ((H.adjugate *ᵥ r) i) = g H.det * V i :=
    (fractionKernel_adjugate_numerator_identity
      H r V hkernel i).symm
  exact quadraticFamilyEval_eq_zero_at_poleResidue
    g hinj res H.det b hdetzero Q
    (fun i : Fin 3 => MvPolynomial.X i)
    (fun i : Fin 3 => (H.adjugate *ᵥ r) i)
    V hscale htransport

end
end HC4.Polynomial.RankThreeCubic
