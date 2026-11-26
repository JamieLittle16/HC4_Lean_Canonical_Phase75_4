module

public import HC4.Polynomial.RankThreeCubicThirdDerivativePolynomialTime
public import Mathlib.Tactic

/-!
# Cubic third-derivative time families descend to the transverse base ring

The source's triple transverse derivatives already evaluate on the actual
normalised rational characteristic to ground-field time polynomials K[t].
Here we lift those coefficients to the transverse base ring B = K[y]
via its canonical constant-polynomial map C : K → B.

The lifted family lies in B[t] and maps *exactly* to the gradient-transport
coefficient family in Frac(B)[t]. This is the precise polynomiality input
for a subsequent residue reduction at an irreducible determinant factor.
It does not assert that the pole branch has been excluded.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicThirdDerivativeBasePolynomialTime

abbrev PB (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev PF (K : Type*) [Field K] := FractionRing (PB K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicThirdDerivativeBasePolynomialTime

open RankThreeCubicThirdDerivativeBasePolynomialTime (PB PF SB)

/-- Scalar extension of a time polynomial along K → K[y] → Frac(K[y])
is exactly its direct extension along K → Frac(K[y]). -/
theorem polynomial_sourceConstants_map_fraction
    (q : _root_.Polynomial K) :
    (_root_.Polynomial.mapRingHom (algebraMap (PB K) (PF K)))
      ((_root_.Polynomial.mapRingHom (MvPolynomial.C : K →+* PB K)) q) =
      (_root_.Polynomial.mapRingHom (algebraMap K (PF K))) q := by
  ext n
  change ((q.map (MvPolynomial.C : K →+* PB K)).map
      (algebraMap (PB K) (PF K))).coeff n =
    (q.map (algebraMap K (PF K))).coeff n
  simp only [_root_.Polynomial.coeff_map]
  exact (IsScalarTower.algebraMap_apply K (PB K) (PF K) (q.coeff n)).symm

/-- Every actual source triple transverse derivative has a
time-polynomial representative with coefficients in the transverse
base ring B = K[y], whose fraction-field image is the *same* line
evaluation used in the source gradient transport. -/
theorem exists_sourceCubic_thirdTransverse_basePolynomialTime
    (F : SB K) (a : K) (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1) (i j k : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let Q := pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
    ∃ T : _root_.Polynomial (PB K),
      lineEval (transverseGenericPoint a) V Q =
        (_root_.Polynomial.mapRingHom
          (algebraMap (PB K) (PF K))) T := by
  classical
  obtain ⟨q, hq⟩ :=
    sourceCubic_thirdTransverse_lineEval_polynomialTime F a V hV i j k
  refine ⟨(_root_.Polynomial.mapRingHom
    (MvPolynomial.C : K →+* PB K)) q, ?_⟩
  rw [polynomial_sourceConstants_map_fraction]
  exact hq

/-- Simultaneously choose the complete 3×3×3 third-derivative family
in K[y][t]; all coefficients descend before choosing a pole prime. -/
theorem exists_sourceCubic_thirdTransverse_basePolynomialFamily
    (F : SB K) (a : K) (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ Q : Fin 3 → Fin 3 → Fin 3 → _root_.Polynomial (PB K),
      ∀ i j k : Fin 3,
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) =
          (_root_.Polynomial.mapRingHom
            (algebraMap (PB K) (PF K))) (Q i j k) := by
  classical
  have h (i j k : Fin 3) :
      ∃ T : _root_.Polynomial (PB K),
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j)
            (pderiv (.inr i) (initialForm transverseCubicWeight 3 F)))) =
          (_root_.Polynomial.mapRingHom
            (algebraMap (PB K) (PF K))) T :=
    exists_sourceCubic_thirdTransverse_basePolynomialTime F a V hV i j k
  choose Q hQ using h
  exact ⟨Q, hQ⟩

end
end HC4.Polynomial.RankThreeCubic
