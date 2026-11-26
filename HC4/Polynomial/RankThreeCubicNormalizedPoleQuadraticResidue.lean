module

public import HC4.Polynomial.RankThreeCubicSourceQuadraticResidue
public import HC4.Polynomial.RankThreeCubicSourceSingularCoefficientResidue
public import Mathlib.Tactic

/-!
# Quadratic source residue with a normalized cubic characteristic pole

Unlike the raw-Cramer quadratic residue, this theorem uses an
*arbitrary genuine common denominator* s for the actual characteristic
and its polynomial numerator S, provided the input relation
    algebraMap(S j) = algebraMap(s) * V_j
is proved.

It works when a determinant factor is repeated and the raw adjugate
numerator vanishes modulo that factor. Every coefficient in the
characteristic time of each quadratic gradient is annihilated by
the normalized residue vector S mod p.

The construction and nonvanishing of S mod p are deliberately
separate tasks; no closing assumption is hidden here.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicNormalizedPoleQuadraticResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicNormalizedPoleQuadraticResidue

open RankThreeCubicNormalizedPoleQuadraticResidue (B3 F3 SB)

/-- Actual source gradient transport gives the quadratic
characteristic-time coefficient identities at any *normalized*
pole denominator. No squarefree Hessian determinant assumption. -/
theorem sourceCubic_normalizedPole_quadraticResidue_coefficients
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
    (p s : B3 K)
    (hp : Irreducible p)
    (hps : p ∣ s)
    (S : Fin 3 → B3 K)
    (hscale :
      ∀ j : Fin 3,
        algebraMap (B3 K) (F3 K) (S j) =
          algebraMap (B3 K) (F3 K) s * V (.inr j))
    (i : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
      (∀ j k : Fin 3,
        (Q j k).map (algebraMap (B3 K) (F3 K)) =
          lineEval (transverseGenericPoint a) V
            (pderiv (.inr k) (pderiv (.inr j)
              (pderiv (.inr i) L)))) ∧
      (∀ n : ℕ,
        (∑ j : Fin 3, ∑ k : Fin 3,
          q ((Q j k).coeff n) * q (S j) * q (S k)) = 0) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hqzero : q s = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hps)
  have hinj : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  obtain ⟨Q, hQ, htransport⟩ :=
    exists_sourceCubic_baseQuadraticTransport F a V hV hgrad i
  have hres :
      quadraticFamilyEval
        (fun j k : Fin 3 => (Q j k).map q)
        (fun j : Fin 3 => _root_.Polynomial.C (q (S j))) = 0 := by
    exact quadraticFamilyEval_eq_zero_at_poleResidue
      g hinj q s
      (2 * referenceSlice a (pderiv (.inr i) L))
      hqzero Q (fun j : Fin 3 => MvPolynomial.X j)
      S (fun j : Fin 3 => V (.inr j))
      hscale htransport
  refine ⟨Q, hQ, ?_⟩
  intro n
  have hcoeff :=
    quadraticFamilyEval_zero_coefficients
      (fun j k : Fin 3 => (Q j k).map q)
      (fun j : Fin 3 => q (S j)) hres n
  simpa only [_root_.Polynomial.coeff_map] using hcoeff

end
end HC4.Polynomial.RankThreeCubic
