import HC4.Polynomial.RankThreeCubicRepeatedFactorHomogeneous
import HC4.Polynomial.RankThreeCubicSourcePoleRankSplit
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import Mathlib.Tactic

/-!
# The genuine repeated cubic source pole has principal rank two

For the actual source cubic's homogeneous, nonzero transverse
Hessian determinant D = p²*c, with p irreducible and the
degree-one complementary factor c, Euler's identity forces
the pole p to be a homogeneous linear form.

The source-honest arbitrary-plane rank-one obstruction then rules
out divisibility of every 2x2 cofactor by p. The existing symmetric
matrix rank split produces a surviving *principal* 2x2 cofactor.

Thus the repeated genuine-pole branch is necessarily rank two along
its sole pole hyperplane. No extra chart, residue, or source endpoint
is assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A factored homogeneous cubic source Hessian cannot have
rank at most one on its repeated pole divisor: a principal
2x2 cofactor necessarily survives. -/
theorem sourceCubic_repeatedFactor_has_principalRankTwo
    (F : SB K) (a : K)
    (p c : B3 K)
    (hp : Irreducible p)
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (hfactor :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det = (p * p) * c)
    (hc : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1) :
    ∃ k : Fin 3,
      ¬ p ∣ (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate k k := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, hpoly, hell⟩ :=
    homogeneousCubic_repeatedDegreeOneFactor_linearForm
      H.det p c (sourceCubic_transverseHessian_det_homogeneous_three a F)
      hfactor hp.ne_zero hc hpdeg hcdeg
  have hnotall : ¬ ∀ i j : Fin 3, p ∣ H.adjugate i j := by
    intro hall
    exact sourceCubic_homogeneousLinearPole_rankOne_impossible
      F a p ell hpoly hell hregular hall
  have hpdet : p ∣ H.det := by
    refine ⟨p * c, ?_⟩
    rw [hfactor]
    ring
  rcases sourceCubic_primeHessian_rankOne_or_principalRankTwo
      a L p hp hpdet with hlow | hhigh
  · exact False.elim (hnotall hlow)
  · exact hhigh

/-- Every genuine denominator pole of an actual source cubic
characteristic must admit a surviving principal Hessian cofactor.
The genuine repeated factor, complementary linear factor and their
exact degrees are derived from the full source gradient transport. -/
theorem sourceCubic_genuinePole_has_principalRankTwo
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
    ∃ k : Fin 3,
      ¬ p ∣ (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate k k := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  have hpp : p * p ∣ H.det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad j p hp hpd hpn
  obtain ⟨c, hc, hc0, hpdeg, hcdeg⟩ :=
    cubic_homogeneous_repeatedFactor_exact_linear_cofactor
      H.det p (sourceCubic_transverseHessian_det_homogeneous_three a F)
      hregular hp hpp
  exact sourceCubic_repeatedFactor_has_principalRankTwo
    F a p c hp hregular hc hc0 hpdeg hcdeg

end
end HC4.Polynomial.RankThreeCubic
