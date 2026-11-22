import HC4.Polynomial.RankThreeCubicSourceUnconditionalRankTwoTransport
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import HC4.Polynomial.RankThreeCubicLinearPoleFrame
import Mathlib.Tactic

/-!
# Genuine source pole: explicit homogeneous linear equation and tangent frame

The new rank-one obstruction already forces every genuinely reduced
denominator pole of the source cubic to be a rank-two hyperplane.
For the next rank-two analysis we also need an *adapted transverse
basis* whose last two directions lie tangent to that hyperplane.

This theorem derives all the required chart data directly:
* exact source Hessian determinant factorisation D = p²*c;
* p,c of total degree exactly one, c nonzero;
* a nonzero coefficient vector ell representing p;
* an invertible matrix M with columns 1,2 annihilated by ell;
* a surviving principal rank-two cofactor of the actual source.

There is no new choice-of-chart or pole-homogeneity hypothesis.
It is preparation for the remaining rank-two pencil classification,
not a claim that rank two is impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A genuine reduced denominator pole of the original cubic source
has a source-derived invertible transverse coordinate frame tangent
to its forced principal rank-two hyperplane. -/
theorem sourceCubic_genuinePole_rankTwo_adaptedLinearFrame
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
    (j : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j))) :
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
    ∃ (c : B3 K) (ell : Fin 3 → K)
      (M : Matrix (Fin 3) (Fin 3) K) (k : Fin 3),
      H.det = (p * p) * c ∧
      c ≠ 0 ∧
      p.totalDegree = 1 ∧
      c.totalDegree = 1 ∧
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      ell ≠ 0 ∧
      M.det ≠ 0 ∧
      (∑ i : Fin 3, ell i * M i 1) = 0 ∧
      (∑ i : Fin 3, ell i * M i 2) = 0 ∧
      (¬ p ∣ H.adjugate k k) := by
  classical
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a (initialForm transverseCubicWeight 3 F)
  have hpp : p * p ∣ H.det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad j p hp hpd hpn
  obtain ⟨c, hfactor, hc0, hpdeg, hcdeg⟩ :=
    cubic_homogeneous_repeatedFactor_exact_linear_cofactor
      H.det p
      (sourceCubic_transverseHessian_det_homogeneous_three a F)
      hregular hp hpp
  obtain ⟨ell, hpoly, hell⟩ :=
    homogeneousCubic_repeatedDegreeOneFactor_linearForm
      H.det p c
      (sourceCubic_transverseHessian_det_homogeneous_three a F)
      hfactor hp.ne_zero hc0 hpdeg hcdeg
  obtain ⟨M, hM, hM1, hM2⟩ :=
    exists_invertible_frame_annihilating_linearFunctional ell hell
  obtain ⟨k, hk⟩ :=
    sourceCubic_genuinePole_has_principalRankTwo
      F a V hV hgrad hregular j p hp hpd hpn
  exact ⟨c, ell, M, k,
    hfactor, hc0, hpdeg, hcdeg, hpoly, hell,
    hM, hM1, hM2, hk⟩

end
end HC4.Polynomial.RankThreeCubic
