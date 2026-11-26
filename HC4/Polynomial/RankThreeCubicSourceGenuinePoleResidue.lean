module

public import HC4.Polynomial.RankThreeCubicCommonDenominatorResidue
public import Mathlib.Tactic

/-!
# Genuine cubic source pole produces a nonzero normalized singular residue

The source's full gradient transport supplies a rational characteristic
H V = r and exact quadratic gradient identities. Every genuine prime
factor p of one reduced coordinate denominator now yields, *without*
squarefreeness or an assumed pole order:

* a common denominator s divisible by p;
* polynomial numerators T with image(T) = image(s) * V;
* a nonzero quotient vector S = T mod p;
* the Hessian kernel equation (H mod p) S = 0;
* every characteristic-time coefficient of each source cubic quadratic
  gradient equation vanishes on S.

The nonzero residue is derived from minimality of the LCM of reduced
denominators, not asserted as a new closing hypothesis. This theorem
does not yet rule out the singular direction.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSourceGenuinePoleResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSourceGenuinePoleResidue

open RankThreeCubicSourceGenuinePoleResidue (B3 F3 SB)

/-- A genuine reduced denominator prime of the *actual*
source characteristic supplies a nonzero kernel and all
source-derived quadratic time residues on the same prime divisor.
No squarefreeness, rank-two residue, or nonvanishing assumption. -/
theorem sourceCubic_genuinePole_nonzeroNormalizedQuadraticResidue
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
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K)) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    ∃ (s : B3 K) (T : Fin 3 → B3 K),
      p ∣ s ∧
      (∀ k : Fin 3,
        algebraMap (B3 K) (F3 K) (T k) =
          algebraMap (B3 K) (F3 K) s * V (.inr k)) ∧
      let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun k => q (T k)
      S ≠ 0 ∧
      (H.map q) *ᵥ S = 0 ∧
      (∀ i : Fin 3,
        ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
          (∀ k l : Fin 3,
            (Q k l).map (algebraMap (B3 K) (F3 K)) =
              lineEval (transverseGenericPoint a) V
                (pderiv (.inr l) (pderiv (.inr k)
                  (pderiv (.inr i) L)))) ∧
          (∀ n : ℕ,
            (∑ k : Fin 3, ∑ l : Fin 3,
              q ((Q k l).coeff n) * S k * S l) = 0)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hk : (H.map g) *ᵥ (fun k : Fin 3 => V (.inr k)) =
      fun k : Fin 3 => g (r k) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  obtain ⟨s, T, hps, hscale, hTnz⟩ :=
    exists_commonDenominator_nonzeroResidue_at_genuinePole
      (fun k : Fin 3 => V (.inr k)) p hp j hpd
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) := fun k => q (T k)
  obtain ⟨k, hTknz⟩ := hTnz
  have hSk : S k ≠ 0 := by
    intro hzero
    exact hTknz
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
  have hS : S ≠ 0 := by
    intro hzero
    exact hSk (by simpa using congrFun hzero k)
  have hcleared : H *ᵥ T = s • r :=
    normalized_fractionKernel_cleared
      H r T (fun k : Fin 3 => V (.inr k)) hk s hscale
  have hszero : q s = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hps)
  have hSker : (H.map q) *ᵥ S = 0 := by
    funext k
    change (∑ l : Fin 3, q (H k l) * q (T l)) = 0
    calc
      _ = q ((H *ᵥ T) k) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      _ = q (s * r k) := by rw [hcleared]; rfl
      _ = 0 := by rw [map_mul, hszero, zero_mul]
  refine ⟨s, T, hps, hscale, hS, hSker, ?_⟩
  intro i
  exact sourceCubic_normalizedPole_quadraticResidue_coefficients
    F a V hV hgrad p s hp hps T hscale i

end
end HC4.Polynomial.RankThreeCubic
