import HC4.Polynomial.RankThreeCubicPoleFinalTrichotomy
import Mathlib

/-!
# From a surviving cofactor to a principal Schur pivot on a cubic pole

For any symmetric 3x3 matrix over a commutative ring, if a prime element
divides its determinant but not one entry of the adjugate, then some
*diagonal* adjugate entry is not divisible by that prime.

The proof uses the 3x3 identity
  adj(adj(H)) = det(H) • H.
Modulo the prime, this forces all off-diagonal adjugate entries to
vanish if its diagonal entries vanish.

This is a nonvanishing principal 2x2 Hessian minor on the actual cubic
source component. No contradiction or lift to the original polynomial
source endpoint is asserted here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

/-- A nonzero cofactor of a symmetric 3x3 matrix on a prime determinant
component forces a nonzero *principal* cofactor on the same component. -/
theorem exists_principal_cofactor_not_dvd
    {R : Type*} [CommRing R] (H : Matrix (Fin 3) (Fin 3) R)
    (hSym : H.IsSymm) (p : R) (hp : Prime p)
    (hdet : p ∣ H.det)
    (hcof : ∃ i j : Fin 3, ¬ p ∣ H.adjugate i j) :
    ∃ k : Fin 3, ¬ p ∣ H.adjugate k k := by
  classical
  let B := H.adjugate
  by_contra h
  push_neg at h
  have hdiag (i : Fin 3) : p ∣ B i i := h i
  have hBSym : B.IsSymm := Matrix.IsSymm.adjugate hSym
  have hadjadj : B.adjugate = H.det • H := by
    simpa [B] using (Matrix.adjugate_adjugate H
      (by decide : Fintype.card (Fin 3) ≠ 1))
  have hadjdiv (k : Fin 3) : p ∣ B.adjugate k k := by
    rw [hadjadj]
    change p ∣ H.det * H k k
    exact dvd_mul_of_dvd_left hdet _
  have hminor22 : B.adjugate 2 2 =
      B 0 0 * B 1 1 - B 0 1 * B 1 0 := by
    rw [Matrix.adjugate_fin_three]
    simp
  have hminor11 : B.adjugate 1 1 =
      B 0 0 * B 2 2 - B 0 2 * B 2 0 := by
    rw [Matrix.adjugate_fin_three]
    simp
  have hminor00 : B.adjugate 0 0 =
      B 1 1 * B 2 2 - B 1 2 * B 2 1 := by
    rw [Matrix.adjugate_fin_three]
    simp
  have hprod01 : p ∣ B 0 1 * B 1 0 := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_left (hdiag 0) (B 1 1)) (hadjdiv 2)
    rw [hminor22] at hd
    convert hd using 1 <;> ring
  have hprod02 : p ∣ B 0 2 * B 2 0 := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_left (hdiag 0) (B 2 2)) (hadjdiv 1)
    rw [hminor11] at hd
    convert hd using 1 <;> ring
  have hprod12 : p ∣ B 1 2 * B 2 1 := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_left (hdiag 1) (B 2 2)) (hadjdiv 0)
    rw [hminor00] at hd
    convert hd using 1 <;> ring
  have h01 : p ∣ B 0 1 :=
    hp.dvd_of_dvd_pow (n := 2) (by
      simpa only [pow_two, hBSym.apply (0 : Fin 3) (1 : Fin 3)]
        using hprod01)
  have h02 : p ∣ B 0 2 :=
    hp.dvd_of_dvd_pow (n := 2) (by
      simpa only [pow_two, hBSym.apply (0 : Fin 3) (2 : Fin 3)]
        using hprod02)
  have h12 : p ∣ B 1 2 :=
    hp.dvd_of_dvd_pow (n := 2) (by
      simpa only [pow_two, hBSym.apply (1 : Fin 3) (2 : Fin 3)]
        using hprod12)
  have h10 : p ∣ B 1 0 := by
    simpa only [hBSym.apply (0 : Fin 3) (1 : Fin 3)] using h01
  have h20 : p ∣ B 2 0 := by
    simpa only [hBSym.apply (0 : Fin 3) (2 : Fin 3)] using h02
  have h21 : p ∣ B 2 1 := by
    simpa only [hBSym.apply (1 : Fin 3) (2 : Fin 3)] using h12
  have hall (i j : Fin 3) : p ∣ B i j := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hdiag 0
      | exact hdiag 1
      | exact hdiag 2
      | exact h01
      | exact h02
      | exact h12
      | exact h10
      | exact h20
      | exact h21
  obtain ⟨i, j, hij⟩ := hcof
  exact hij (hall i j)

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- Symmetry of the actual transverse Hessian, without an added chart
assumption: it follows from commutation of source mixed partials. -/
theorem sourceTransverseHessian_isSymm
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K) :
    (sourceTransverseHessian a L).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change referenceSlice a
      (pderiv (.inr i) (pderiv (.inr j) L)) =
    referenceSlice a
      (pderiv (.inr j) (pderiv (.inr i) L))
  rw [HC4.Newton.pderiv_comm_backport (.inr i) (.inr j) L]

/-- Source-honest cubic classification in which the squarefree pole
branch now supplies a *principal* 2x2 Schur pivot on the same
irreducible component as the nonzero residue Hessian kernel. -/
theorem exists_sourceCubic_linear_or_repeatedLinear_or_principalResidue
    [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FractionRing (B3 K)),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (FractionRing (B3 K))) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (FractionRing (B3 K))
            (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (FractionRing (B3 K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ p : B3 K, Irreducible p ∧
            p * p ∣ (sourceTransverseHessian a L).det ∧
            p.totalDegree = 1)
        ∨ (∃ p : B3 K, Irreducible p ∧
            p ∣ (sourceTransverseHessian a L).det ∧
            (∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
              S ≠ 0 ∧
              ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) ∧
            (∃ k : Fin 3, ¬ p ∣
              (sourceTransverseHessian a L).adjugate k k))) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linear_or_repeatedLinear_or_residueCofactor
      F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hrep | hres
  · exact Or.inl hlin
  · exact Or.inr (Or.inl hrep)
  · rcases hres with ⟨p, hp, hpdet, hS, i, j, hcof⟩
    have hSym : (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).IsSymm :=
      sourceTransverseHessian_isSymm a _
    obtain ⟨k, hk⟩ := exists_principal_cofactor_not_dvd
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F))
      hSym p hp.prime hpdet ⟨i, j, hcof⟩
    exact Or.inr (Or.inr ⟨p, hp, hpdet, hS, k, hk⟩)

end
end HC4.Polynomial.RankThreeCubic
