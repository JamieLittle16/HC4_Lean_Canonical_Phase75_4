import HC4.Polynomial.RankThreeCubicSourceQuadraticResidue
import HC4.Polynomial.RankThreeCubicSquarefreeCramerNonzero
import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib.Tactic

/-!
# Nonzero quadratic singular direction from a genuine squarefree source pole

For the *actual* full-transverse-rank cubic source characteristic,
assume its chosen transverse Hessian determinant is squarefree and
the rational transverse velocity is not polynomial.

The exact Cramer numerator then survives on an irreducible factor p.
For this *same* p and *same nonzero residue vector*, full
gradient transport produces, for all three transverse gradient
components, a quadratic equation with source third-derivative
time coefficients. The same component has a principal 2x2 minor.

Squarefreeness and nonpolynomiality here are case hypotheses
from the existing source cubic trichotomy, not new HC4 endpoint
assumptions. No claim that the singular-direction case is
contradictory has yet been made.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- At a genuine squarefree pole of the source cubic characteristic,
the nonzero residue of the actual Cramer numerator is a common zero
of all three source-derived time-dependent quadratic gradients, while
a principal Hessian cofactor survives on the same factor. -/
theorem exists_sourceCubic_squarefreePole_nonzeroSingularResidue
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
          quadraticFamilyEval
            (fun j k : Fin 3 => (Q j k).map q)
            (fun j : Fin 3 => _root_.Polynomial.C (S j)) = 0) ∧
      (∃ k : Fin 3, ¬ p ∣ H.adjugate k k) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  have hk :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ
        (fun j : Fin 3 => V (.inr j)) =
      fun j : Fin 3 => algebraMap (B3 K) (F3 K) (r j) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  obtain ⟨p, i, hp, hpdet, hAnz⟩ :=
    exists_squarefreePole_CramerNumerator_not_dvd
      H r (fun j : Fin 3 => V (.inr j)) hk hnonpoly hsq
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q ((H.adjugate *ᵥ r) j)
  have hSi : S i ≠ 0 := by
    intro hz
    apply hAnz
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hS : S ≠ 0 := by
    intro hz
    exact hSi (by simpa using congrFun hz i)
  have hdetzero : q H.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hpdet)
  have hadj : H *ᵥ (H.adjugate *ᵥ r) = H.det • r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hker : (H.map q) *ᵥ S = 0 := by
    funext j
    change (∑ k : Fin 3, q (H j k) * q ((H.adjugate *ᵥ r) k)) = 0
    calc
      _ = q ((H *ᵥ (H.adjugate *ᵥ r)) j) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      _ = q (H.det * r j) := by
        rw [hadj]
        rfl
      _ = 0 := by rw [map_mul, hdetzero, zero_mul]
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp.prime
  have hquad (i : Fin 3) :
      ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
        (∀ j k : Fin 3,
          (Q j k).map (algebraMap (B3 K) (F3 K)) =
            lineEval (transverseGenericPoint a) V
              (pderiv (.inr k) (pderiv (.inr j)
                (pderiv (.inr i) L)))) ∧
        quadraticFamilyEval
          (fun j k : Fin 3 => (Q j k).map q)
          (fun j : Fin 3 => _root_.Polynomial.C (S j)) = 0 := by
    obtain ⟨Q, hQ, hres⟩ :=
      exists_sourceCubic_cramerQuadraticResidue
        F a V hV hgrad q hdetzero i
    exact ⟨Q, hQ, hres⟩
  have hcof : ∃ k : Fin 3, ¬ p ∣ H.adjugate k k :=
    exists_principal_cofactor_not_dvd H
      (sourceTransverseHessian_isSymm a L) p hp.prime hpdet
      (exists_cofactor_not_dvd_of_cramer_numerator_not_dvd
        H r p ⟨i, hAnz⟩)
  exact ⟨p, hp, hpdet, hS, hker, hquad, hcof⟩

end
end HC4.Polynomial.RankThreeCubic
