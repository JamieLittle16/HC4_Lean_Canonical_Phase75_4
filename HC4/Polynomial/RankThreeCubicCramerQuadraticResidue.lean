import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
import HC4.Polynomial.RankThreeCubicPoleDeterminant
import Mathlib.Tactic

/-!
# Cramer's numerator obeys the quadratic transport residue equation

Given a rational transverse characteristic H V = r and a polynomial
quadratic transport identity along that characteristic, the exact
Cramer numerator A = adj(H) r obeys

  quadraticFamilyEval (Q mod p) (C (A mod p)) = 0

for every polynomial factor p of det(H). No squarefree determinant,
rank-two residue hypothesis, or extra source assumption is required
to derive this equality. Nonvanishing of A mod p remains separate.

This theorem is a base-ring algebraic bridge. The source coefficient
descent and source transport modules provide its hypotheses.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)

/-- The actual Cramer numerator, not an independently chosen kernel
vector, is annihilated by the polynomial quadratic family modulo
every determinant factor. -/
theorem cramerNumerator_quadraticResidue
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun i => algebraMap (B3 K) (F3 K) (r i))
    (p : B3 K) (hpdet : p ∣ H.det)
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
        (fun i j : Fin 3 =>
          (Q i j).map (Ideal.Quotient.mk (Ideal.span {p})))
        (fun i : Fin 3 =>
          _root_.Polynomial.C
            ((Ideal.Quotient.mk (Ideal.span {p}))
              ((H.adjugate *ᵥ r) i))) = 0 := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  have hinj : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  have hpzero : q H.det = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr hpdet
  have hscale (i : Fin 3) :
      g ((H.adjugate *ᵥ r) i) = g H.det * V i :=
    (fractionKernel_adjugate_numerator_identity
      H r V hkernel i).symm
  exact quadraticFamilyEval_eq_zero_at_poleResidue
    g hinj q H.det b hpzero Q
    (fun i : Fin 3 => MvPolynomial.X i)
    (fun i : Fin 3 => (H.adjugate *ᵥ r) i)
    V hscale htransport

end
end HC4.Polynomial.RankThreeCubic
