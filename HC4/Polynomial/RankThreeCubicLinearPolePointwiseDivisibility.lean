import HC4.Polynomial.RankThreeCubicDetOnePolePlaneCubicCofactorZero
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Pointwise vanishing on a linear hyperplane implies exact divisibility

Over an infinite field K, a polynomial vanishing at every
K-rational point of the hyperplane p(y)=ell·y is divisible
by p, provided ell is a nonzero linear functional.

The proof uses a polynomial projection to the hyperplane.
Choose k with ell[k] != 0, and replace X[k] by
  X[k] - C(ell[k]⁻¹) * p.
The new polynomial variables satisfy p=0 exactly.
The projection is identity modulo p.

This proof does not assume K algebraically closed and does not
introduce any radical or endpoint assumption.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- A polynomial vanishing at all rational points of the
linear hyperplane ell·y=0 is divisible by its defining
linear polynomial, given any nonzero coefficient ell[k]. -/
theorem linearPole_dvd_of_forall_pointEval_zero_at
    (p f : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (k : Fin 3) (hk : ell k ≠ 0)
    (hzero : ∀ z : Fin 3 → K,
      MvPolynomial.aeval z p = 0 →
        MvPolynomial.aeval z f = 0) :
    p ∣ f := by
  classical
  let u : B3 K := MvPolynomial.C ((ell k)⁻¹) * p
  let s : Fin 3 → B3 K :=
    fun i => if i = k then MvPolynomial.X i - u else MvPolynomial.X i
  have hsum : (∑ i : Fin 3, s i * MvPolynomial.C (ell i)) =
      p - u * MvPolynomial.C (ell k) := by
    calc
      _ = (∑ i : Fin 3,
          (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i)) -
            u * MvPolynomial.C (ell k) := by
          fin_cases k <;>
            simp [s, Fin.sum_univ_three] <;> ring
      _ = p - u * MvPolynomial.C (ell k) := by rw [hlin]
  have hcoeff : (MvPolynomial.C ((ell k)⁻¹) : B3 K) *
      MvPolynomial.C (ell k) = 1 := by
    rw [← map_mul]
    simp [hk]
  have huc : u * MvPolynomial.C (ell k) = p := by
    dsimp [u]
    calc
      _ = (MvPolynomial.C ((ell k)⁻¹) *
            MvPolynomial.C (ell k)) * p := by ring
      _ = p := by rw [hcoeff]; ring
  have hpSub : MvPolynomial.aeval s p = 0 := by
    calc
      MvPolynomial.aeval s p =
          ∑ i : Fin 3, s i * MvPolynomial.C (ell i) := by
            rw [hlin]
            simp only [map_sum, map_mul, MvPolynomial.aeval_X,
              MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      _ = p - u * MvPolynomial.C (ell k) := hsum
      _ = 0 := by rw [huc, sub_self]
  have hsubzero : MvPolynomial.aeval s f = 0 := by
    apply MvPolynomial.funext
    intro y
    let z : Fin 3 → K := fun i => MvPolynomial.aeval y (s i)
    have hcomp (F : B3 K) :
        MvPolynomial.aeval y (MvPolynomial.aeval s F) =
          MvPolynomial.aeval z F :=
      MvPolynomial.comp_aeval_apply (f := s) (MvPolynomial.aeval y) F
    have hpz : MvPolynomial.aeval z p = 0 := by
      rw [← hcomp p, hpSub]
      simp
    have hfz := hzero z hpz
    change MvPolynomial.aeval y (MvPolynomial.aeval s f) =
      MvPolynomial.aeval y (0 : B3 K)
    rw [hcomp f, map_zero]
    exact hfz
  let Q := B3 K ⧸ Ideal.span {p}
  let qA : B3 K →ₐ[K] Q :=
    Ideal.Quotient.mkₐ K (Ideal.span {p})
  have hqp : qA p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton p))
  have hqcomp : qA.comp (MvPolynomial.aeval s) = qA := by
    ext i
    have hi : qA (s i) = qA (MvPolynomial.X i) := by
      by_cases hik : i = k
      · subst i
        simp only [s, if_pos rfl]
        dsimp [u]
        rw [map_sub, map_mul, hqp, mul_zero, sub_zero]
      · simp only [s, if_neg hik]
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hi
  have hqzero : qA f = 0 := by
    have hident : qA (MvPolynomial.aeval s f) = qA f :=
      AlgHom.congr_fun hqcomp f
    rw [← hident, hsubzero]
    simp
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)

/-- No particular pivot index is needed: a nonzero
linear functional has at least one nonzero coordinate. -/
theorem linearPole_dvd_of_forall_pointEval_zero
    (p f : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (hzero : ∀ z : Fin 3 → K,
      MvPolynomial.aeval z p = 0 →
        MvPolynomial.aeval z f = 0) :
    p ∣ f := by
  classical
  have hsome : ∃ k : Fin 3, ell k ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hell
    funext i
    exact hnone i
  obtain ⟨k, hk⟩ := hsome
  exact linearPole_dvd_of_forall_pointEval_zero_at p f ell hlin k hk hzero

end
end HC4.Polynomial.RankThreeCubic
