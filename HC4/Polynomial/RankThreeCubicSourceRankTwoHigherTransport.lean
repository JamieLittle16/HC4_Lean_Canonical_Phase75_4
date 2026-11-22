import HC4.Polynomial.RankThreeCubicAlignedQuadraticColumn
import Mathlib.Tactic

/-!
# All higher-time source cubic pole identities on the adjugate column

The already verified normalized source pole residue supplies actual
polynomial-in-time representatives for every transverse third
derivative of the cubic source. For all coefficients n, the quadratic
source transport vanishes on the nonzero residue vector S.

In the principal rank-two chart, we use the source-honest
adjugate alignment to transfer *all* these coefficientwise identities
to the kth adjugate column. This is strictly more information than
the time-zero Jacobi derivative identities, which vanish formally
when p² divides the Hessian determinant.

No terminal contradiction or higher-order lift is asserted here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual rank-two genuine pole determines a nonzero residue
and forces every coefficient of every transported third derivative
quadratic family to annihilate the same principal adjugate column. -/
theorem sourceCubic_rankTwo_genuinePole_allTime_adjugateColumnQuadratics
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
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j)))
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
        q (H.adjugate k k) * S i =
          q (H.adjugate i k) * S k) ∧
      (∀ i : Fin 3,
        ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
          (∀ l m : Fin 3,
            (Q l m).map (algebraMap (B3 K) (F3 K)) =
              lineEval (transverseGenericPoint a) V
                (pderiv (.inr m) (pderiv (.inr l)
                  (pderiv (.inr i) L)))) ∧
          (∀ n : ℕ,
            (∑ l : Fin 3, ∑ m : Fin 3,
              q ((Q l m).coeff n) *
              q (H.adjugate l k) * q (H.adjugate m k)) = 0)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  obtain ⟨s, T, hps, hscale, hSk, hSker, halign, _⟩ :=
    sourceCubic_genuinePole_rankTwo_adjugateAlignedResidue
      F a V hV hgrad j p hp hpd hpn k hk
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun l => q (T l)
  refine ⟨s, T, hps, hscale, hSk, hSker, halign, ?_⟩
  intro i
  obtain ⟨Q, hQ, hcoeff⟩ :=
    sourceCubic_normalizedPole_quadraticResidue_coefficients
      F a V hV hgrad p s hp hps T hscale i
  refine ⟨Q, hQ, ?_⟩
  intro n
  exact alignedKernel_quadraticZero_implies_adjugateColumn_quadraticZero
    (H.adjugate.map q) S k hSk halign
    (fun l m : Fin 3 => q ((Q l m).coeff n)) (hcoeff n)

end
end HC4.Polynomial.RankThreeCubic
