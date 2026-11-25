import HC4.Polynomial.RationalCharacteristicRankOneJetPropagation
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# A single noncharacteristic line for the whole velocity field

Choose a coordinate line through a point where all the cleared
differential coefficients are nonzero. The line specialization
commutes with the tangent partial. By the zero-jet theorem every
nonzero reduced numerator and denominator of an invariant rational
function survives this *same* specialization.

The next step extends this specialization to a field embedding.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev P (K : Type*) := _root_.Polynomial K
private abbrev I := Unit ⊕ Fin 3

/-- Leave the pivot coordinate free and specialize all others
to ground-field constants. -/
def rankOne_coordinateLine (j : Fin 3) (c : Fin 3 → K) : B K →ₐ[K] P K :=
  MvPolynomial.aeval (fun i => if i = j then _root_.Polynomial.X
    else _root_.Polynomial.C (c i))

theorem rankOne_coordinateLine_X (j : Fin 3) (c : Fin 3 → K) (i : Fin 3) :
    rankOne_coordinateLine j c (X i) =
      if i = j then _root_.Polynomial.X else _root_.Polynomial.C (c i) :=
  MvPolynomial.aeval_X _ _

/-- The ordinary univariate derivative is exactly the specialized
tangent partial, on all multivariate polynomials. -/
theorem rankOne_coordinateLine_derivative
    (j : Fin 3) (c : Fin 3 → K) (p : B K) :
    (rankOne_coordinateLine j c p).derivative =
      rankOne_coordinateLine j c (pderiv j p) := by
  let φ := rankOne_coordinateLine j c
  change (φ p).derivative = φ (pderiv j p)
  have hC (a : K) : φ (MvPolynomial.C a) = _root_.Polynomial.C a :=
    φ.commutes a
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [hC, _root_.Polynomial.derivative_C, pderiv_C, map_zero]
  | add p q hp hq =>
    rw [map_add, _root_.Polynomial.derivative_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    have hX : φ (X i) = if i = j then _root_.Polynomial.X
        else _root_.Polynomial.C (c i) := rankOne_coordinateLine_X j c i
    rw [map_mul, _root_.Polynomial.derivative_mul, hp,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    by_cases h : i = j
    · subst i
      rw [hX, if_pos rfl, _root_.Polynomial.derivative_X, pderiv_X, map_one]
      ring
    · rw [hX, if_neg h, _root_.Polynomial.derivative_C,
        pderiv_X_of_ne h, map_zero]
      ring

theorem rankOne_coordinateLine_tangent
    (j : Fin 3) (c : Fin 3 → K) (p : B K)
    (hp : rankOne_coordinateLine j c p = 0) :
    rankOne_coordinateLine j c (pderiv j p) = 0 := by
  rw [← rankOne_coordinateLine_derivative, hp, _root_.Polynomial.derivative_zero]

/-- Evaluating the free coordinate at its original value recovers
evaluation of the multivariate polynomial at the original point. -/
theorem rankOne_coordinateLine_eval
    (j : Fin 3) (c : Fin 3 → K) (p : B K) :
    (rankOne_coordinateLine j c p).eval (c j) = MvPolynomial.eval c p := by
  let e : P K →ₐ[K] K := _root_.Polynomial.aeval (c j)
  let φ := rankOne_coordinateLine j c
  have h : e.comp φ = MvPolynomial.aeval c := by
    apply MvPolynomial.algHom_ext
    intro i
    change e (φ (X i)) = c i
    rw [show φ (X i) = if i = j then _root_.Polynomial.X
      else _root_.Polynomial.C (c i) from rankOne_coordinateLine_X j c i]
    by_cases hi : i = j
    · subst i
      simp [e]
    · simp [e, hi]
  exact congrArg (fun f : B K →ₐ[K] K => f p) h

/-- There is one coordinate line where every member of a finite
family of nonzero polynomials specializes to a nonzero polynomial. -/
theorem rankOne_coordinateLine_exists_regular
    (j : Fin 3) (b : Fin 3 → B K) (hb : ∀ l, b l ≠ 0) :
    ∃ c : Fin 3 → K, ∀ l, rankOne_coordinateLine j c (b l) ≠ 0 := by
  classical
  let g : B K := ∏ l : Fin 3, b l
  have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun l _ => hb l)
  have hex : ∃ c : Fin 3 → K, MvPolynomial.eval c g ≠ 0 := by
    by_contra hn
    apply hg
    apply MvPolynomial.funext
    intro c
    rw [map_zero]
    by_contra hc
    exact hn ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  intro l hl
  have hz : rankOne_coordinateLine j c g = 0 := by
    change rankOne_coordinateLine j c (∏ l : Fin 3, b l) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) hl
  apply hc
  rw [← rankOne_coordinateLine_eval j c g, hz, _root_.Polynomial.eval_zero]

/-- For a nonzero rank-one Jacobian there is a single coordinate
line on which every nonzero reduced numerator and every reduced
denominator belonging to the velocity field is nonzero.

The quantification over fractions is *inside* the choice of line;
no fraction-dependent specialization is needed. -/
theorem rankOne_velocityField_exists_regular_line
    (V : I → E K) (i j : Fin 3)
    (hp : rationalCharacteristicJacobian V i j ≠ 0)
    (hm : ∀ a b : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ c : Fin 3 → K, ∀ p q : B K, q ≠ 0 → IsRelPrime p q →
      algebraMap (B K) (E K) p / algebraMap (B K) (E K) q ∈
        IntermediateField.adjoin K (Set.range (fun a : Fin 3 => V (.inr a))) →
      (rankOne_coordinateLine j c q ≠ 0 ∧
        (p ≠ 0 → rankOne_coordinateLine j c p ≠ 0)) := by
  classical
  let t (l : Fin 3) := rationalCharacteristicJacobian V i l /
    rationalCharacteristicJacobian V i j
  let a (l : Fin 3) : B K := IsFractionRing.num (B K) (t l)
  let b (l : Fin 3) : B K := IsFractionRing.den (B K) (t l)
  have hb (l : Fin 3) : b l ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) (t l))
  have hab (l : Fin 3) : algebraMap (B K) (E K) (a l) /
      algebraMap (B K) (E K) (b l) = t l :=
    IsFractionRing.mk'_num_den' (B K) (t l)
  obtain ⟨c, hc⟩ := rankOne_coordinateLine_exists_regular j b hb
  refine ⟨c, ?_⟩
  intro p q hq hcop hz
  have hd (l : Fin 3) :=
    rankOne_velocityField_reducedPair_dvd V i j l hp hm (a l) (b l) p q
      (hb l) (hab l) hq hcop hz
  let φ := rankOne_coordinateLine j c
  have htan (f : B K) (hf : φ f = 0) : φ (pderiv j f) = 0 :=
    rankOne_coordinateLine_tangent j c f hf
  refine ⟨?_, ?_⟩
  · exact rankOne_specialization_ne_zero_of_differentialEquations φ j a b q hq
      htan (fun l _ => hc l) (fun l _ => (hd l).2)
  · intro hn
    exact rankOne_specialization_ne_zero_of_differentialEquations φ j a b p hn
      htan (fun l _ => hc l) (fun l _ => (hd l).1)

end
end HC4.Polynomial.RankThreeCubic
