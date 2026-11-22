import HC4.Polynomial.RankThreeCubicSourceExactDoubleOrTriple
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import Mathlib.Tactic

/-!
# Canonical source cubic obstruction: linear velocity or exact double/triple rank-two pole

The full original source hypotheses imply one of two alternatives:

(1) The transverse rational characteristic is constant-linear.
(2) A unique reduced-denominator prime p exists, forced to be a
    homogeneous linear form with a surviving principal rank-two
    Hessian cofactor. The remaining Hessian geometry is either
      (2a) det H = p²*c, p does not divide c, and the pole normal
           annihilates every adjugate column modulo p; or
      (2b) det H = C(lambda)*p³ with lambda nonzero.

The source anchor, characteristic transport and uniqueness of
the genuine denominator pole are preserved. Neither remaining
rank-two case is declared impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The original full-rank cubic source reduces without additional
endpoint hypotheses to polynomial velocity, an exactly-double
rank-two pole with normal-adjugate annihilation, or an exact
scalar triple rank-two pole. The unique-pole statement refers
to the actual reduced rational-coordinate denominators. -/
theorem exists_sourceCubic_linear_or_exactDoubleNormal_or_exactTriple
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
        (∃ (u : Fin 3) (p : B3 K) (ell : Fin 3 → K) (k : Fin 3),
          Irreducible p ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u)) ∧
          p = ∑ i : Fin 3,
            (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
          (¬ p ∣ (sourceTransverseHessian a L).adjugate k k) ∧
          ((∃ c : B3 K,
              (sourceTransverseHessian a L).det = (p * p) * c ∧
              c ≠ 0 ∧
              ¬ p ∣ c ∧
              (∀ j : Fin 3,
                p ∣ (∑ i : Fin 3,
                  MvPolynomial.C (ell i) *
                    (sourceTransverseHessian a L).adjugate i j)))
           ∨
           (∃ lambda : K, lambda ≠ 0 ∧
              (sourceTransverseHessian a L).det =
                MvPolynomial.C lambda * (p * p * p))) ∧
          (∀ (v : Fin 3) (q : B3 K),
            Irreducible q →
            q ∣ (IsFractionRing.den (B3 K) (V (.inr v)) : B3 K) →
            ¬ q ∣ IsFractionRing.num (B3 K) (V (.inr v)) →
            Associated q p))) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  obtain ⟨a, V, hregular, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_singleGenuinePole_exactCofactor
      F hcap hdet htrans
  refine ⟨a, V, hregular, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin |
      ⟨u, p, c, hp, hfactor, hc0, hpdeg, hcdeg, hpd, hpn, huniq⟩
  · exact Or.inl hlin
  · obtain ⟨ell, k, hpoly, hk, hsplit⟩ :=
      sourceCubic_genuineRankTwo_exactDoubleNormal_or_exactTriple
        F a V hV hgrad hregular u p hp hpd hpn
    exact Or.inr
      ⟨u, p, ell, k, hp, hpd, hpn, hpoly, hk, hsplit, huniq⟩

end
end HC4.Polynomial.RankThreeCubic
