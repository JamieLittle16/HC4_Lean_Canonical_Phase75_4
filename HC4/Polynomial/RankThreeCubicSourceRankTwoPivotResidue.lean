import HC4.Polynomial.RankThreeCubicPrincipalKernelPivot
import Mathlib.Tactic

/-!
# The source cubic's normalized residue has a nonzero Schur pivot

The actual nonpolynomial characteristic produces a nonzero
denominator-normalized vector S modulo its pole prime p, killed
by the transverse Hessian H and satisfying all transported
quadratic source identities.

In the principal rank-two chart a nonzero principal cofactor of
H forces the corresponding coordinate S(k) to be nonzero. We
also extract the time-zero source quadratic identities in the
concrete form
  sum_{j,l} (partial_i H_{j,l}) S_j S_l = 0.

This is exact source data for the rank-two Schur analysis, not an
assumption or a contradiction in itself. In particular p² | det(H)
already forces the first determinant derivatives to vanish modulo p.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- In the rank-two chart, the *genuine* normalized source pole
residue has a nonzero pivot coordinate and obeys the explicit
first-derivative Hessian quadratic identities modulo p.

There is no independent residue, chart vector, or pole-order
hypothesis. Only the principal rank-two cofactor is selected. -/
theorem sourceCubic_genuinePole_rankTwo_nonzeroPivot_and_quadraticHessian
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
    (j : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (k : Fin 3)
    (hk : ¬ p ∣
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate k k) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    ∃ (s : B3 K) (T : Fin 3 → B3 K),
      p ∣ s ∧
      (∀ l : Fin 3,
        algebraMap (B3 K) (F3 K) (T l) =
          algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
      let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun l => q (T l)
      S k ≠ 0 ∧
      (H.map q) *ᵥ S = 0 ∧
      (∀ i : Fin 3,
        (∑ l : Fin 3, ∑ m : Fin 3,
          q (pderiv i (H l m)) * S l * S m) = 0) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  obtain ⟨s, T, hps, hscale, hS, hSker, hquad⟩ :=
    sourceCubic_genuinePole_nonzeroNormalizedQuadraticResidue
      F a V hV hgrad j p hp hpd
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) := fun l => q (T l)
  have hcof' : q (H.adjugate k k) ≠ 0 := by
    intro hz
    exact hk
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hcof : (H.map q).adjugate k k ≠ 0 := by
    have hmap : (H.map q).adjugate = H.adjugate.map q :=
      (q.map_adjugate H).symm
    rw [hmap]
    exact hcof'
  have hSk : S k ≠ 0 :=
    principalCofactor_kernelVector_pivot_ne_zero
      (H.map q) S hSker hS k hcof
  refine ⟨s, T, hps, hscale, hSk, hSker, ?_⟩
  intro i
  obtain ⟨Q, hQ, hcoeff⟩ := hquad i
  have hQ0 (l m : Fin 3) :
      (Q l m).coeff 0 = pderiv i (H l m) :=
    cubic_sourceThirdDerivative_timeZero a L V i l m
      (Q l m) (hQ l m)
  simpa only [hQ0] using hcoeff 0

end
end HC4.Polynomial.RankThreeCubic
