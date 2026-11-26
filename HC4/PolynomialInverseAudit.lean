import HC4.StatementAudit
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial inverse audit

Keep this extension separate from the verified conditional equivalence.
Surjectivity on points makes polynomial substitution injective. A reduced
rational inverse coordinate of a surjective polynomial map has unit
denominator, by the Nullstellensatz. Thus once rational inverse coordinates
are constructed, both polynomial composition identities follow.

No claim of rational inverse existence is made in this file.
-/

namespace HC4.PolynomialInverseAudit

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Surjectivity of a polynomial map on points makes its pullback on
polynomials injective. -/
theorem bind_injective_of_point_surjective {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) K)
    (hs : Function.Surjective (fun x : Fin n → K => fun i => eval x (F i))) :
    Function.Injective (bind₁ F) := by
  intro A B h
  apply MvPolynomial.funext
  intro y
  obtain ⟨x, rfl⟩ := hs y
  have he : aeval x (bind₁ F A) = aeval x (bind₁ F B) :=
    congrArg (fun p : MvPolynomial (Fin n) K => aeval x p) h
  rw [aeval_bind₁, aeval_bind₁] at he
  exact he

/-- Surjectivity forces the denominator of a reduced rational inverse
coordinate to be a unit. Here A(F(x)) = B(F(x)) * x_i is an exact
polynomial identity, not a generic-point equality assumed to hold everywhere. -/
theorem denominator_isUnit_of_reduced_coordinate {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) K)
    (hs : Function.Surjective (fun x : Fin n → K => fun i => eval x (F i)))
    (A B : MvPolynomial (Fin n) K) (i : Fin n)
    (hrel : IsRelPrime B A)
    (h : bind₁ F A = bind₁ F B * X i) :
    IsUnit B := by
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span {B}
  have hrad : A ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    change ∀ y ∈ MvPolynomial.zeroLocus K I, aeval y A = 0
    intro y hy
    have hb : aeval y B = 0 :=
      hy B (Ideal.subset_span (Set.mem_singleton B))
    obtain ⟨x, rfl⟩ := hs y
    have he : aeval x (bind₁ F A) = aeval x (bind₁ F B * X i) :=
      congrArg (fun p : MvPolynomial (Fin n) K => aeval x p) h
    rw [map_mul, aeval_bind₁, aeval_bind₁, aeval_X] at he
    change aeval (fun j => aeval x (F j)) B = 0 at hb
    rw [hb, zero_mul] at he
    exact he
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hrad
  have hd : B ∣ A ^ m := Ideal.mem_span_singleton.mp hm
  exact (hrel.pow_right (n := m)).isUnit_of_dvd hd

/-- Once reduced rational coordinates are known, a surjective map has a
two-sided polynomial inverse, in exactly the external composition convention. -/
theorem polynomial_inverse_of_reduced_coordinates {n : ℕ}
    (F : Fin n → MvPolynomial (Fin n) K)
    (hs : Function.Surjective (fun x : Fin n → K => fun i => eval x (F i)))
    (hr : ∀ i : Fin n, ∃ A B : MvPolynomial (Fin n) K,
      IsRelPrime B A ∧ bind₁ F A = bind₁ F B * X i) :
    ∃ G : Fin n → MvPolynomial (Fin n) K,
      (∀ i, bind₁ G (F i) = X i) ∧
      (∀ i, bind₁ F (G i) = X i) := by
  classical
  have hcoord (i : Fin n) : ∃ g : MvPolynomial (Fin n) K,
      bind₁ F g = X i := by
    obtain ⟨A,B,hrel,h⟩ := hr i
    have hu := denominator_isUnit_of_reduced_coordinate F hs A B i hrel h
    obtain ⟨u, rfl⟩ := hu
    refine ⟨(↑u⁻¹ : MvPolynomial (Fin n) K) * A, ?_⟩
    rw [map_mul, h, ← mul_assoc, ← map_mul]
    simp
  choose G hG using hcoord
  refine ⟨G, ?_, hG⟩
  intro i
  apply bind_injective_of_point_surjective F hs
  rw [bind₁_bind₁, show (fun j => bind₁ F (G j)) = X from funext hG,
    bind₁_X_left]
  simp

end
end HC4.PolynomialInverseAudit

#print axioms HC4.PolynomialInverseAudit.bind_injective_of_point_surjective
#print axioms HC4.PolynomialInverseAudit.denominator_isUnit_of_reduced_coordinate
#print axioms HC4.PolynomialInverseAudit.polynomial_inverse_of_reduced_coordinates

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``HC4.PolynomialInverseAudit.bind_injective_of_point_surjective,
      ``HC4.PolynomialInverseAudit.denominator_isUnit_of_reduced_coordinate,
      ``HC4.PolynomialInverseAudit.polynomial_inverse_of_reduced_coordinates] do
    for dep in (← Lean.collectAxioms decl) do
      unless allowed.contains dep do
        throwError "Unexpected logical dependency {dep} in {decl}"
