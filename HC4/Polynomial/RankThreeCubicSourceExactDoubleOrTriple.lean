import HC4.Polynomial.RankThreeCubicExactTriplePoleNormalForm
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import Mathlib.Tactic

/-!
# Genuine source cubic pole: exact double versus exact triple Hessian geometry

The actual source repeated-pole branch has now been sharpened
beyond rank-two tangency:

* An exactly-double factor det H = p²*c, with c nonzero and
  not divisible by p, forces the pole normal ell to annihilate
  every adjugate column modulo p.
* Otherwise the source determinant is exactly lambda*p³
  for some nonzero scalar lambda in the ground field.

The source pole p and its normal ell are inherited from the
actual characteristic; the principal rank-two cofactor survives
in both alternatives. Neither case is dismissed by hypothesis.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Exact source-derived geometric classification of a genuine
rank-two cubic characteristic pole: either the exactly-double
Hessian pole has all normal adjugate columns divisible by p,
or the Hessian determinant is a scalar multiple of p cubed. -/
theorem sourceCubic_genuineRankTwo_exactDoubleNormal_or_exactTriple
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
    ∃ (ell : Fin 3 → K) (k : Fin 3),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      (¬ p ∣ H.adjugate k k) ∧
      ((∃ c : B3 K,
          H.det = (p * p) * c ∧
          c ≠ 0 ∧
          ¬ p ∣ c ∧
          (∀ j : Fin 3,
            p ∣ (∑ i : Fin 3,
              MvPolynomial.C (ell i) * H.adjugate i j)))
       ∨
       (∃ lambda : K, lambda ≠ 0 ∧
          H.det = MvPolynomial.C lambda * (p * p * p))) := by
  classical
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
  obtain ⟨c, ell, k, hfactor, hc0, hpoly, hk, hsplit⟩ :=
    sourceCubic_genuineRankTwo_adjugateNormalZero_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  have hpp : p * p ∣ H.det := ⟨c, hfactor⟩
  obtain ⟨c', hfactor', hc0', hpdeg, hcdeg'⟩ :=
    cubic_homogeneous_repeatedFactor_exact_linear_cofactor
      H.det p (sourceCubic_transverseHessian_det_homogeneous_three a F)
      hregular hp hpp
  have hceq : c = c' := by
    apply mul_left_cancel₀ (mul_ne_zero hp.ne_zero hp.ne_zero)
    exact hfactor.symm.trans hfactor'
  have hcdeg : c.totalDegree = 1 := by
    rw [hceq]
    exact hcdeg'
  by_cases hpc : p ∣ c
  · exact Or.inr
      (repeatedLinearCofactor_dvd_implies_exactTriple
        H.det p c hfactor hp.ne_zero hc0 hpdeg hcdeg hpc)
  · left
    refine ⟨c, hfactor, hc0, hpc, ?_⟩
    rcases hsplit with hnormal | htriple
    · exact hnormal
    · exact False.elim (hpc htriple)

end
end HC4.Polynomial.RankThreeCubic
