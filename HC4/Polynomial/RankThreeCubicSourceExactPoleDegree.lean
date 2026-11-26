module

public import HC4.Polynomial.RankThreeCubicSourceSinglePoleNormalForm
public import Mathlib.Tactic

/-!
# Exact factorization of a cubic source repeated characteristic pole

The transverse Hessian determinant of the actual cubic initial form
is homogeneous of degree three, not merely of degree at most three.
Consequently in the genuine-pole case D = p²*c with p irreducible
of total degree one, the complementary factor c has *exactly*
total degree one.

The resulting sole pole hyperplane need not yet be impossible;
there is still a double-vs-triple repeated-factor alternative.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSourceExactPoleDegree

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSourceExactPoleDegree

open RankThreeCubicSourceExactPoleDegree (B3 F3 SB)

/-- A nonzero homogeneous cubic with a repeated irreducible factor
has an *exactly linear* nonzero complementary factor. -/
theorem cubic_homogeneous_repeatedFactor_exact_linear_cofactor
    (D p : B3 K)
    (hhom : D.IsHomogeneous 3)
    (hD : D ≠ 0)
    (hp : Irreducible p)
    (hpp : p * p ∣ D) :
    ∃ c : B3 K, D = (p * p) * c ∧ c ≠ 0 ∧
      p.totalDegree = 1 ∧ c.totalDegree = 1 := by
  classical
  have hDdeg : D.totalDegree = 3 := hhom.totalDegree hD
  have hdeg : D.totalDegree ≤ 3 := by omega
  obtain ⟨c, hc, hc0, hcdeg⟩ :=
    cubic_repeatedFactor_has_linear_cofactor D p hD hdeg hp hpp
  have hpdeg : p.totalDegree = 1 :=
    degree_one_of_specified_repeated_factor D p hD hdeg hp hpp
  have hmul : D.totalDegree =
      (p * p).totalDegree + c.totalDegree := by
    rw [hc]
    exact MvPolynomial.totalDegree_mul_of_isDomain
      (mul_ne_zero hp.ne_zero hp.ne_zero) hc0
  have hp2deg : (p * p).totalDegree =
      p.totalDegree + p.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hp.ne_zero hp.ne_zero
  refine ⟨c, hc, hc0, hpdeg, ?_⟩
  omega

/-- Source-level dichotomy with a genuine denominator pole p and a
nonzero *degree exactly one* complementary factor c. The pole class
is unique up to association for all transverse characteristic
coordinates, and full source gradient transport is preserved. -/
theorem exists_sourceCubic_linear_or_singleGenuinePole_exactCofactor
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
        (∃ (j : Fin 3) (p c : B3 K),
          Irreducible p ∧
          (sourceTransverseHessian a L).det = (p * p) * c ∧
          c ≠ 0 ∧
          p.totalDegree = 1 ∧
          c.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j)) ∧
          (∀ (k : Fin 3) (q : B3 K),
            Irreducible q →
            q ∣ (IsFractionRing.den (B3 K) (V (.inr k)) : B3 K) →
            ¬ q ∣ IsFractionRing.num (B3 K) (V (.inr k)) →
            Associated q p))) := by
  classical
  obtain ⟨a, V, hreg, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_singleGenuinePole F hcap hdet htrans
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin | ⟨j, p, c, hp, hfact, hc0, hcdeg, hpdeg, hpd, hpn, huniq⟩
  · exact Or.inl hlin
  · have hDdeg : (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det.totalDegree = 3 :=
      (sourceCubic_transverseHessian_det_homogeneous_three a F).totalDegree hreg
    have hmul :
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F)).det.totalDegree =
        (p * p).totalDegree + c.totalDegree := by
      rw [hfact]
      exact MvPolynomial.totalDegree_mul_of_isDomain
        (mul_ne_zero hp.ne_zero hp.ne_zero) hc0
    have hp2deg : (p * p).totalDegree =
        p.totalDegree + p.totalDegree :=
      MvPolynomial.totalDegree_mul_of_isDomain hp.ne_zero hp.ne_zero
    have hc1 : c.totalDegree = 1 := by omega
    exact Or.inr ⟨j, p, c, hp, hfact, hc0, hpdeg, hc1, hpd, hpn, huniq⟩

end
end HC4.Polynomial.RankThreeCubic
