import HC4.Polynomial.RankThreeCubicThirdDerivativeLongitudinal
import HC4.Polynomial.RankThreeCubicLongitudinalPolynomialMap
import Mathlib.Tactic

/-!
# Actual cubic third derivatives have pole-free time coefficients

The preceding source-support theorem writes each third transverse derivative
of the cubic initial form as a renamed polynomial in the single longitudinal
variable. This module proves that a normalized characteristic evaluates
that polynomial at a+t, with coefficients in the *ground field* K.

Thus rational transverse characteristic components cannot introduce
denominators into the time-dependent third-derivative coefficients.
The construction does not require squarefreeness, a pole factor, or any
extra assumption about the source.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev PB (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev PF (K : Type*) [Field K] := FractionRing (PB K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A longitudinal source polynomial evaluated along a characteristic
with longitudinal velocity one is the ground-field polynomial T(a+t),
embedded in the fraction field of the transverse source ring. -/
theorem lineEval_renamed_longitudinal_eq_groundPolynomial
    (a : K) (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1)
    (T : MvPolynomial Unit K) :
    lineEval (transverseGenericPoint a) V
        (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) =
      (_root_.Polynomial.mapRingHom (algebraMap K (PF K)))
        (MvPolynomial.aeval
          (fun _ : Unit => _root_.Polynomial.C a + _root_.Polynomial.X) T) := by
  classical
  let E : SB K →ₐ[K] _root_.Polynomial (PF K) :=
    lineEval (transverseGenericPoint a) V
  let z : Unit → _root_.Polynomial (PF K) :=
    fun _ => _root_.Polynomial.C (algebraMap K (PF K) a) + _root_.Polynomial.X
  have hX (i : Unit) :
      E (MvPolynomial.X (.inl i)) = z i := by
    cases i
    simp [E, z, lineEval, transverseGenericPoint, hV]
  have hren (T : MvPolynomial Unit K) :
      E (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) =
        MvPolynomial.aeval z T := by
    induction T using MvPolynomial.induction_on with
    | C c =>
      simp [E, z, lineEval]
    | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | mul_X p i hp =>
      calc
        E (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3)
            (p * MvPolynomial.X i)) =
          E (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) p) *
            E (MvPolynomial.X (.inl i)) := by simp
        _ = MvPolynomial.aeval z p * z i := by rw [hp, hX i]
        _ = MvPolynomial.aeval z (p * MvPolynomial.X i) := by simp
  change E (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) = _
  rw [hren]
  exact (longitudinalPolynomial_eval_map (F := PF K) a T).symm

/-- Every actual source triple transverse derivative, evaluated along
any normalized rational characteristic, is a polynomial in time with
coefficients in the ground field K. -/
theorem exists_sourceCubic_thirdDerivative_groundPolynomialTime
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1)
    (i j k : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ q : _root_.Polynomial K,
      lineEval (transverseGenericPoint a) V
        (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) =
      (_root_.Polynomial.mapRingHom (algebraMap K (PF K))) q := by
  classical
  obtain ⟨T, hT⟩ :=
    exists_sourceCubic_thirdTransverse_longitudinal F i j k
  refine ⟨MvPolynomial.aeval
    (fun _ : Unit => _root_.Polynomial.C a + _root_.Polynomial.X) T, ?_⟩
  rw [← hT]
  exact lineEval_renamed_longitudinal_eq_groundPolynomial a V hV T

/-- Package polynomial-time coefficients for all 27 source third
transverse derivatives, without separate existential witnesses
depending on the chosen pole component. -/
theorem exists_sourceCubic_thirdDerivative_groundPolynomialFamily
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ q : Fin 3 → Fin 3 → Fin 3 → _root_.Polynomial K,
      ∀ i j k : Fin 3,
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) =
          (_root_.Polynomial.mapRingHom (algebraMap K (PF K))) (q i j k) := by
  classical
  have h (i j k : Fin 3) :
      ∃ q : _root_.Polynomial K,
        lineEval (transverseGenericPoint a) V
          (pderiv (.inr k) (pderiv (.inr j)
            (pderiv (.inr i) (initialForm transverseCubicWeight 3 F)))) =
          (_root_.Polynomial.mapRingHom (algebraMap K (PF K))) q :=
    exists_sourceCubic_thirdDerivative_groundPolynomialTime F a V hV i j k
  choose q hq using h
  exact ⟨q, hq⟩

end
end HC4.Polynomial.RankThreeCubic
