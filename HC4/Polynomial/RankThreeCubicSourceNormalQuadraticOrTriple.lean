import HC4.Polynomial.RankThreeCubicSourceNormalAdjugateOrTriple
import Mathlib.Tactic

/-!
# The normal Hessian cofactor quadratic form vanishes at an exact double pole

If the source's rank-two repeated denominator pole has no third
determinant factor p, the pole normal ell annihilates every
adjugate column modulo p. In particular the scalar expression

    ellᵀ adj(H) ell

vanishes along the full pole hyperplane. This is invariant under
linear coordinate changes: in a frame with pole equation y₀=0,
it corresponds (up to a nonzero scalar) to the determinant
of the binary tangential Hessian block.

The source alternative remains precise: the normal cofactor
quadratic divisibility holds, or p divides the complementary
degree-one factor c. No triple-pole exclusion is assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Divisibility of every normal adjugate column contraction implies
divisibility of its normal quadratic contraction. -/
theorem normalAdjugateColumns_dvd_normalQuadratic
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (p : B3 K) (ell : Fin 3 → K)
    (hcol : ∀ j : Fin 3,
      p ∣ (∑ i : Fin 3,
        MvPolynomial.C (ell i) * H.adjugate i j)) :
    p ∣ (∑ i : Fin 3, ∑ j : Fin 3,
      MvPolynomial.C (ell i) *
        MvPolynomial.C (ell j) * H.adjugate i j) := by
  classical
  have hrearrange :
      (∑ i : Fin 3, ∑ j : Fin 3,
        MvPolynomial.C (ell i) *
          MvPolynomial.C (ell j) * H.adjugate i j) =
      ∑ j : Fin 3, MvPolynomial.C (ell j) *
        (∑ i : Fin 3,
          MvPolynomial.C (ell i) * H.adjugate i j) := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hrearrange]
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (hcol j) _

/-- The actual source cubic's genuine repeated rank-two pole
has vanishing *normal Hessian cofactor quadratic* along p,
unless the Hessian determinant has a triple linear factor. -/
theorem sourceCubic_genuineRankTwo_normalQuadratic_or_triple
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
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (u : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u))) :
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
    ∃ (c : B3 K) (ell : Fin 3 → K) (k : Fin 3),
      H.det = (p * p) * c ∧
      c ≠ 0 ∧
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      (¬ p ∣ H.adjugate k k) ∧
      ((p ∣ ∑ i : Fin 3, ∑ j : Fin 3,
          MvPolynomial.C (ell i) *
            MvPolynomial.C (ell j) * H.adjugate i j) ∨ p ∣ c) := by
  classical
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
  obtain ⟨c, ell, k, hfactor, hc, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_adjugateNormalZero_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨c, ell, k, hfactor, hc, hpoly, hk, ?_⟩
  rcases hsplit with hcol | hc
  · exact Or.inl (normalAdjugateColumns_dvd_normalQuadratic H p ell hcol)
  · exact Or.inr hc

end
end HC4.Polynomial.RankThreeCubic
