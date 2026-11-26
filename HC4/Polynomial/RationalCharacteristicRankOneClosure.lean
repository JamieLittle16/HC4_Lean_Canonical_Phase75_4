module

public import HC4.Polynomial.RationalCharacteristicRankOneLurothBridge
public import Mathlib.FieldTheory.RatFunc.Luroth

/-!
# Unconditional rank-at-most-one rational characteristic closure

Discharge the sole simple-generation premise in the verified rank-one
bridge by the Mathlib's kernel-checked univariate Lüroth theorem.
No extra field-generation or transverse degree assumptions are needed.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RationalCharacteristicRankOneClosure

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev I := Unit ⊕ Fin 3
abbrev S (K : Type*) [Field K] := MvPolynomial I K
abbrev P (K : Type*) [Field K] := _root_.Polynomial K

end RationalCharacteristicRankOneClosure

open RationalCharacteristicRankOneClosure (B E I S P)

/-- Univariate Lüroth in exactly the form needed by the velocity field bridge. -/
theorem rationalCharacteristic_univariateSimpleGeneration
    (G : IntermediateField K (RatFunc K)) :
    ∃ u : RatFunc K, G = IntermediateField.adjoin K {u} :=
  ⟨RatFunc.Luroth.generator G, RatFunc.Luroth.eq_adjoin_generator (E := G)⟩

variable [CharZero K]

/-- Every nonzero characteristic Jacobian with vanishing two-by-two
minors has a common rational parameter for all three velocities. -/
theorem rankOne_commonParameter
    (V : I → E K)
    (hn : rationalCharacteristicJacobian V ≠ 0)
    (hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (t : E K) (A Q : Fin 3 → P K),
      (∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
      ∀ i, V (.inr i) = (A i).eval₂ (algebraMap K (E K)) t /
        (Q i).eval₂ (algebraMap K (E K)) t :=
  rankOne_commonParameter_of_univariateSimpleGeneration
    rationalCharacteristic_univariateSimpleGeneration V hn hm

/-- Source adjugate annihilation for normalized anchored characteristics
whose Jacobian has rank at most one, with no Lüroth premise. -/
theorem rationalCharacteristic_rankAtMostOne_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 :=
  rationalCharacteristic_rankAtMostOne_adjugate_of_univariateSimpleGeneration
    rationalCharacteristic_univariateSimpleGeneration a L V hdet hV hreg hgrad hm

end
end HC4.Polynomial.RankThreeCubic
