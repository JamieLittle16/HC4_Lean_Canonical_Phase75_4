import HC4.Polynomial.RankThreeCubicPrincipalAdjugateDirection
import HC4.Polynomial.RankThreeCubicSourceRankTwoPivotResidue
import Mathlib.Tactic

/-!
# The actual cubic pole residue aligns with a principal adjugate column

For the full source characteristic and its genuine denominator pole p,
the earlier normalized residue extraction supplies a nonzero kernel
vector S in K[y]/(p), together with the gradient quadratic identities.

When a principal 2x2 Hessian cofactor survives, this result identifies
the actual residue S with the corresponding adjugate column without
passing to a fraction field:
  q(adj(H)kk)*Si = q(adj(H)ik)*Sk.

This is a source-derived Schur direction on the very same pole
hyperplane. It does not assert that a rank-two repeated pole is
impossible; the next obstruction must use further transport data.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The genuine rank-two source pole residue is proportional to
the principal adjugate column, and retains its nonzero pivot and
all time-zero Hessian quadratic transport identities. -/
theorem sourceCubic_genuinePole_rankTwo_adjugateAlignedResidue
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
        (∑ l : Fin 3, ∑ m : Fin 3,
          q (pderiv i (H l m)) * S l * S m) = 0) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  obtain ⟨s, T, hps, hscale, hSk, hSker, hquad⟩ :=
    sourceCubic_genuinePole_rankTwo_nonzeroPivot_and_quadraticHessian
      F a V hV hgrad j p hp hpd k hk
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
  have hcof' : q (H.adjugate k k) ≠ 0 := by
    intro hz
    exact hk
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hmap : (H.map q).adjugate = H.adjugate.map q :=
    (q.map_adjugate H).symm
  have hcof : (H.map q).adjugate k k ≠ 0 := by
    rw [hmap]
    exact hcof'
  have halign (i : Fin 3) :
      q (H.adjugate k k) * S i =
        q (H.adjugate i k) * S k := by
    have h :=
      principalCofactor_kernelVector_adjugate_proportional
        (H.map q) S hSker hdetmod k hcof i
    rw [hmap] at h
    exact h
  exact ⟨s, T, hps, hscale, hSk, hSker, halign, hquad⟩

end
end HC4.Polynomial.RankThreeCubic
