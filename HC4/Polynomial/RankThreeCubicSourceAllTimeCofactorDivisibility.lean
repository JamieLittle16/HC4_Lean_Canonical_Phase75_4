import HC4.Polynomial.RankThreeCubicRankTwoFullAdjugateContraction
import Mathlib.Tactic

/-!
# Actual source cubic: every transported time coefficient annihilates adj(H)

In the principal rank-two repeated pole case, the *source-derived*
normalized residue provides a nonzero kernel S modulo the prime p.
The residue is aligned with the principal adjugate column.

Applying the algebraic rank-one adjugate identity coefficientwise
to the full source gradient transport now proves

  p | sum_{j,l} (Q_i,j,l.coeff n) * adj(H)_{j,l}

for every source transverse derivative i and every characteristic
time exponent n. The time-zero case recovers the familiar Jacobi
derivative-divisibility identity, already automatic from p² | det(H).
For n>0 this is a longitudinal compatibility constraint, not merely
a repeat of the derivative of the determinant at the base slice.

No contradiction or extra hypothesis on the normalised residue
is asserted.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- On the actual source cubic's rank-two genuine repeated pole,
every characteristic-time coefficient of the transported third
transverse derivative family has zero *full adjugate* contraction.
This statement preserves the actual source characteristic, its
gradient transport, the pole divisor, and a chosen principal pivot. -/
theorem sourceCubic_rankTwo_genuinePole_allTime_cofactorContractions
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
    ∃ (s : B3 K) (T : Fin 3 → B3 K),
      p ∣ s ∧
      (∀ l : Fin 3,
        algebraMap (B3 K) (F3 K) (T l) =
          algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
      let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
        Ideal.Quotient.mk (Ideal.span {p})
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
            p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
              (Q l m).coeff n * H.adjugate l m))) := by
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
  have hpp : p * p ∣ H.det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad j p hp hpd hpn
  have hpdet : p ∣ H.det := by
    obtain ⟨u, hu⟩ := hpp
    refine ⟨p * u, ?_⟩
    calc
      H.det = (p * p) * u := hu
      _ = p * (p * u) := by ring
  have hqdet : q H.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hpdet)
  have hdetmod : (H.map q).det = 0 := by
    simpa only [RingHom.map_det] using hqdet
  have hSym : (H.map q).IsSymm := by
    have hHsym : H.IsSymm :=
      sourceTransverseHessian_isSymm a L
    apply Matrix.IsSymm.ext
    intro i j
    change q (H j i) = q (H i j)
    exact congrArg q (hHsym.apply i j)
  have hcof' : q (H.adjugate k k) ≠ 0 := by
    intro hz
    exact hk
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hmap : (H.map q).adjugate = H.adjugate.map q :=
    (q.map_adjugate H).symm
  have hcof : (H.map q).adjugate k k ≠ 0 := by
    rw [hmap]
    exact hcof'
  have halign' (i : Fin 3) :
      (H.map q).adjugate k k * S i =
        (H.map q).adjugate i k * S k := by
    rw [hmap]
    exact halign i
  refine ⟨s, T, hps, hscale, hSk, hSker, halign, ?_⟩
  intro i
  obtain ⟨Q, hQ, hcoeff⟩ :=
    sourceCubic_normalizedPole_quadraticResidue_coefficients
      F a V hV hgrad p s hp hps T hscale i
  refine ⟨Q, hQ, ?_⟩
  intro n
  have hcontraction :
      (∑ l : Fin 3, ∑ m : Fin 3,
        q ((Q l m).coeff n) * (H.map q).adjugate l m) = 0 :=
    alignedKernel_quadraticZero_implies_adjugateContraction
      (H.map q) hSym hdetmod S k hcof hSk halign'
      (fun l m => q ((Q l m).coeff n)) (hcoeff n)
  have hzero : q (∑ l : Fin 3, ∑ m : Fin 3,
      (Q l m).coeff n * H.adjugate l m) = 0 := by
    simp only [map_sum, map_mul]
    rw [hmap] at hcontraction
    exact hcontraction
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

end
end HC4.Polynomial.RankThreeCubic
