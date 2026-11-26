module

public import HC4.Polynomial.RankThreeCubicPoleJacobiBridge
public import Mathlib.Tactic

/-!
# Cubic source: a squarefree pole would divide all Jacobi derivatives

The same actual four-variable source supplies a nonzero Cramer residue,
a principal adjugate pivot and coefficientwise transported third-derivative
equations. The rank-one Jacobi bridge forces every partial derivative of
the transverse Hessian determinant to vanish on the same pole divisor.

This is the source-level derivative-divisibility obstruction. The final
characteristic-zero squarefree-factor contradiction is separate.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSquarefreePoleDerivativeObstruction

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSquarefreePoleDerivativeObstruction

open RankThreeCubicSquarefreePoleDerivativeObstruction (B3 F3 SB)

/-- The actual source cubic cannot have a *squarefree* nonpolynomial
characteristic without yielding an irreducible Hessian determinant
factor that divides every first transverse derivative of that determinant.

The source, anchor, characteristic and irreducible component are the
same throughout the extraction; no arbitrary pole-vector data are assumed. -/
theorem exists_sourceCubic_squarefreePole_factor_dvd_allJacobiDerivatives
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
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
    ∃ p : B3 K, Irreducible p ∧ p ∣ H.det ∧
      ∀ i : Fin 3, p ∣ pderiv i H.det := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  obtain ⟨p, hp, hpdet, hS, _hker, hquad, hpivot⟩ :=
    exists_sourceCubic_squarefreePole_coefficientwiseSingularResidue
      F a V hV hgrad hsq hnonpoly
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q ((H.adjugate *ᵥ r) j)
  have hSvec :
      (H.adjugate.map q) *ᵥ (fun j : Fin 3 => q (r j)) = S := by
    funext j
    change (∑ l : Fin 3, q (H.adjugate j l) * q (r l)) =
      q ((H.adjugate *ᵥ r) j)
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hSnonzero :
      (H.adjugate.map q) *ᵥ (fun j : Fin 3 => q (r j)) ≠ 0 := by
    rw [hSvec]
    exact hS
  obtain ⟨k, hkpivot⟩ := hpivot
  have hk : q (H.adjugate k k) ≠ 0 := by
    intro hz
    exact hkpivot
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hdetzero : q H.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hpdet)
  have hquadratic (i : Fin 3) :
      (∑ j : Fin 3, ∑ l : Fin 3,
        q (pderiv i (H j l)) *
          ((H.adjugate.map q) *ᵥ
            (fun n : Fin 3 => q (r n))) j *
          ((H.adjugate.map q) *ᵥ
            (fun n : Fin 3 => q (r n))) l) = 0 := by
    obtain ⟨Q, hQ, hcoeff⟩ := hquad i
    have hQzero (j l : Fin 3) :
        (Q j l).coeff 0 = pderiv i (H j l) :=
      cubic_sourceThirdDerivative_timeZero a L V i j l
        (Q j l) (hQ j l)
    have hzero :
        (∑ j : Fin 3, ∑ l : Fin 3,
          q (pderiv i (H j l)) * S j * S l) = 0 := by
      simpa only [hQzero] using hcoeff 0
    simpa only [← hSvec] using hzero
  have hvanish :=
    cubic_rankOneCramer_Jacobi_zero H
      (sourceTransverseHessian_isSymm a L)
      q hdetzero r k hk hSnonzero hquadratic
  refine ⟨p, hp, hpdet, ?_⟩
  intro i
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (hvanish i))

end
end HC4.Polynomial.RankThreeCubic
