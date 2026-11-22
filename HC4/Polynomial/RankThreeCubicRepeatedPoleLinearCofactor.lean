import HC4.Polynomial.RankThreeCubicSourceRepeatedGenuinePole
import Mathlib.Tactic

/-!
# Cubic repeated-pole determinant has a degree-one residual factor

If a nonzero degree-at-most-three polynomial has a repeated
irreducible degree-one factor p, then after removing p², the
remaining factor has total degree at most one.

Applied to the genuine denominator pole singled out by the
source-level repeated-pole theorem, this gives the shape

    det H = p² * c,    totalDegree c ≤ 1,

with p simultaneously a reduced characteristic denominator prime.
This is a degree constraint, not yet a contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- In a nonzero cubic determinant, division by a repeated degree-one
factor leaves a polynomial of degree at most one. -/
theorem cubic_repeatedFactor_has_linear_cofactor
    (D p : B3 K)
    (hD : D ≠ 0)
    (hdeg : D.totalDegree ≤ 3)
    (hp : Irreducible p)
    (hpp : p * p ∣ D) :
    ∃ c : B3 K, D = (p * p) * c ∧ c ≠ 0 ∧ c.totalDegree ≤ 1 := by
  classical
  obtain ⟨c, hc⟩ := hpp
  have hc0 : c ≠ 0 := by
    intro hz
    apply hD
    rw [hc, hz, mul_zero]
  have hpdeg : p.totalDegree = 1 :=
    degree_one_of_specified_repeated_factor D p hD hdeg hp hpp
  have hmul :
      D.totalDegree = (p * p).totalDegree + c.totalDegree := by
    rw [hc]
    exact MvPolynomial.totalDegree_mul_of_isDomain
      (mul_ne_zero hp.ne_zero hp.ne_zero) hc0
  have hsq :
      (p * p).totalDegree = p.totalDegree + p.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hp.ne_zero hp.ne_zero
  refine ⟨c, hc, hc0, ?_⟩
  omega

/-- The source's genuine repeated pole determines a concrete
factorization of the *same* transverse Hessian determinant:
D = p² c with c nonzero and degree at most one. This theorem does
not assert that the repeated-pole branch is impossible. -/
theorem exists_sourceCubic_linear_or_repeatedGenuinePole_withCofactor
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → F3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V (pderiv i L) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K)) *ᵥ
            (fun i : Fin 3 => V (.inr i)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (F3 K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨
        (∃ (i : Fin 3) (p c : B3 K),
          Irreducible p ∧
          (sourceTransverseHessian a L).det = (p * p) * c ∧
          c ≠ 0 ∧ c.totalDegree ≤ 1 ∧
          p.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr i)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr i)))) := by
  classical
  obtain ⟨a, V, hreg, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_repeatedGenuinePole F hcap hdet htrans
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin | hrep
  · exact Or.inl hlin
  · obtain ⟨i, p, hp, hpp, hpdeg, hpd, hpn⟩ := hrep
    obtain ⟨c, hfact, hc0, hcdeg⟩ :=
      cubic_repeatedFactor_has_linear_cofactor
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F)).det
        p hreg
        (sourceCubic_transverseHessian_det_homogeneous_three a F).totalDegree_le
        hp hpp
    exact Or.inr ⟨i, p, c, hp, hfact, hc0, hcdeg, hpdeg, hpd, hpn⟩

end
end HC4.Polynomial.RankThreeCubic
