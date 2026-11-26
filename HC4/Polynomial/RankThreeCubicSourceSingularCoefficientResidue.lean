module

public import HC4.Polynomial.RankThreeCubicSourceSingularTrichotomy
public import Mathlib.Tactic

/-!
# Every longitudinal coefficient of the cubic pole residue vanishes

The source-honest squarefree cubic pole certificate already gives the
quadratic gradient equations as identities of time polynomials over
K[y]/(p). Taking coefficients shows that the *same nonzero Cramer residue*
is annihilated by every longitudinal coefficient of each quadratic family.

This is a coefficientwise strengthening of the source-pole certificate, not
a proof that the nonzero singular residue is impossible. In particular,
we do not assert that the cubic pencil is smooth.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSourceSingularCoefficientResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSourceSingularCoefficientResidue

open RankThreeCubicSourceSingularCoefficientResidue (B3 F3 SB)

/-- A vanishing quadratic polynomial family at a constant vector
forces every time coefficient of the family to vanish at that vector. -/
theorem quadraticFamilyEval_zero_coefficients
    {R : Type*} [CommRing R]
    (Q : Fin 3 → Fin 3 → _root_.Polynomial R)
    (S : Fin 3 → R)
    (hzero :
      quadraticFamilyEval Q
        (fun i : Fin 3 => _root_.Polynomial.C (S i)) = 0)
    (n : ℕ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (Q i j).coeff n * S i * S j) = 0 := by
  have hterm (i j : Fin 3) :
      (Q i j * _root_.Polynomial.C (S i) *
        _root_.Polynomial.C (S j)).coeff n =
        (Q i j).coeff n * S i * S j := by
    rw [mul_assoc, ← _root_.Polynomial.C_mul,
      _root_.Polynomial.coeff_mul_C]
    ring
  have hc := congrArg
    (fun p : _root_.Polynomial R => p.coeff n) hzero
  simpa only [quadraticFamilyEval, Fin.sum_univ_three,
    _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_zero,
    hterm] using hc

/-- The source's nonzero Cramer pole residue satisfies the quadratic
gradient equations coefficient by coefficient in characteristic time,
not just as an undifferentiated polynomial identity.

The source third derivatives, the residue vector and the principal
Hessian pivot all refer to the same irreducible pole component. -/
theorem exists_sourceCubic_squarefreePole_coefficientwiseSingularResidue
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hsq : Squarefree
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det)
    (hnonpoly : ∃ i : Fin 3, ∀ b : B3 K,
      algebraMap (B3 K) (F3 K) b ≠ V (.inr i)) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let r := sourceNegativeMixedHessian a L
    ∃ p : B3 K, Irreducible p ∧ p ∣ H.det ∧
      let q := Ideal.Quotient.mk (Ideal.span {p})
      let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q ((H.adjugate *ᵥ r) j)
      S ≠ 0 ∧
      (H.map q) *ᵥ S = 0 ∧
      (∀ i : Fin 3,
        ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
          (∀ j k : Fin 3,
            (Q j k).map (algebraMap (B3 K) (F3 K)) =
              lineEval (transverseGenericPoint a) V
                (pderiv (.inr k) (pderiv (.inr j)
                  (pderiv (.inr i) L)))) ∧
          (∀ n : ℕ,
            (∑ j : Fin 3, ∑ k : Fin 3,
              q ((Q j k).coeff n) * S j * S k) = 0)) ∧
      (∃ k : Fin 3, ¬ p ∣ H.adjugate k k) := by
  classical
  obtain ⟨p, hp, hpdet, hS, hker, hquad, hpivot⟩ :=
    exists_sourceCubic_squarefreePole_nonzeroSingularResidue
      F a V hV hgrad hsq hnonpoly
  refine ⟨p, hp, hpdet, hS, hker, ?_, hpivot⟩
  intro i
  obtain ⟨Q, hQ, hres⟩ := hquad i
  refine ⟨Q, hQ, ?_⟩
  intro n
  have hcoef :=
    quadraticFamilyEval_zero_coefficients
      (fun j k : Fin 3 =>
        (Q j k).map (Ideal.Quotient.mk (Ideal.span {p})))
      (fun j : Fin 3 =>
        (Ideal.Quotient.mk (Ideal.span {p}))
          (((sourceTransverseHessian a
              (initialForm transverseCubicWeight 3 F)).adjugate *ᵥ
            sourceNegativeMixedHessian a
              (initialForm transverseCubicWeight 3 F)) j))
      hres n
  simpa only [_root_.Polynomial.coeff_map] using hcoef

end
end HC4.Polynomial.RankThreeCubic
