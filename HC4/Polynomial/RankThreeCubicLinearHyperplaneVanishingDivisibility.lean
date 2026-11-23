import HC4.Polynomial.RankThreeCubicDetOnePolePlaneCubicCofactorZero
import Mathlib.Tactic

/-!
# Vanishing on a rational linear hyperplane implies polynomial divisibility

Let K be a characteristic-zero field, p(y)=ell·y a nonzero
linear form on three variables, and Q any polynomial.

If Q(z)=0 at every K-point z on p(z)=0, then p divides Q.

This proof needs no algebraic closure and does not assume
irreducibility as a separate input. It substitutes a polynomial
projection of K³ onto the plane, then uses extensionality of
polynomial functions over an infinite field.

Crucially the projection differs from the identity by a
multiple of p, hence is identical modulo the original ideal (p).
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- Over an infinite field, the ideal of a nonzero linear
hyperplane consists exactly of its polynomial multiples. -/
theorem linearHyperplane_dvd_of_vanishes_on_plane
    (p Q : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (hzero : ∀ z : Fin 3 → K,
      MvPolynomial.aeval z p = 0 →
        MvPolynomial.aeval z Q = 0) :
    p ∣ Q := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, ell k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hell
    funext i
    exact h i
  let d : K := (ell k)⁻¹
  let projection (i : Fin 3) : B3 K :=
    MvPolynomial.X i -
      (if i = k then MvPolynomial.C d * p else 0)
  let ψ : B3 K →ₐ[K] B3 K := MvPolynomial.aeval projection
  have hprojSum :
      (∑ i : Fin 3, projection i * MvPolynomial.C (ell i)) =
        p - (MvPolynomial.C d * p) * MvPolynomial.C (ell k) := by
    calc
      _ = (∑ i : Fin 3,
            (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i)) -
          (∑ i : Fin 3,
            (if i = k then MvPolynomial.C d * p else 0) *
              MvPolynomial.C (ell i)) := by
          simp only [projection, sub_mul, Finset.sum_sub_distrib]
      _ = p - (MvPolynomial.C d * p) * MvPolynomial.C (ell k) := by
          rw [← hpoly]
          simp
  have hψp : ψ p = 0 := by
    calc
      ψ p = ∑ i : Fin 3,
          projection i * MvPolynomial.C (ell i) := by
            rw [hpoly]
            simp only [map_sum, map_mul, MvPolynomial.aeval_X,
              MvPolynomial.aeval_C]
      _ = p - (MvPolynomial.C d * p) * MvPolynomial.C (ell k) :=
        hprojSum
      _ = p - MvPolynomial.C (d * ell k) * p := by
        rw [map_mul]
        ring
      _ = 0 := by
        have hd : d * ell k = 1 := inv_mul_cancel₀ hk
        rw [hd, map_one, one_mul, sub_self]
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  have hqp : q p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self p)
  have hqproj (i : Fin 3) :
      q (projection i) = q (MvPolynomial.X i) := by
    by_cases hik : i = k
    · simp only [projection, hik, ite_true, map_sub,
        map_mul, hqp, mul_zero, sub_zero]
    · simp only [projection, hik, ite_false, sub_zero]
  have hqψ : q.comp ψ.toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ψ]
    · intro i
      change q (projection i) = q (MvPolynomial.X i)
      exact hqproj i
  have hcomp (z : Fin 3 → K) (f : B3 K) :
      MvPolynomial.aeval z (ψ f) =
        MvPolynomial.aeval
          (fun i => MvPolynomial.aeval z (projection i)) f := by
    exact MvPolynomial.comp_aeval_apply (MvPolynomial.aeval z) f
  have hψQ : ψ Q = 0 := by
    apply MvPolynomial.funext
    intro z
    let v : Fin 3 → K :=
      fun i => MvPolynomial.aeval z (projection i)
    have hpv : MvPolynomial.aeval v p = 0 := by
      calc
        MvPolynomial.aeval v p =
            MvPolynomial.aeval z (ψ p) := (hcomp z p).symm
        _ = 0 := by rw [hψp]; simp
    calc
      MvPolynomial.aeval z (ψ Q) =
        MvPolynomial.aeval v Q := hcomp z Q
      _ = 0 := hzero v hpv
  have hqQ : q Q = 0 := by
    have heq := congrArg (fun h : B3 K →+* R => h Q) hqψ
    change q (ψ Q) = q Q at heq
    rw [hψQ] at heq
    simpa using heq.symm
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hqQ)

end
end HC4.Polynomial.RankThreeCubic
