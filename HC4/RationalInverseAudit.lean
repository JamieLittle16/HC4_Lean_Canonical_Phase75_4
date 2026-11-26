import HC4.PolynomialInverseAudit
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Rational inverse existence

For an injective polynomial map over an algebraically closed field:
* Nullstellensatz transports the collision obstruction to every field extension.
* In characteristic zero, a field extension with only one embedding into
  its algebraic closure is trivial (Mathlib's separable degree).
* Apply this to the fraction field over the image of polynomial substitution.
  This yields reduced rational inverse coordinates, to which the separate
  polynomial inverse audit applies.

All results below are independent of the Jacobian conjecture.
-/

namespace HC4.PolynomialInverseAudit

open MvPolynomial

noncomputable section

/-- Injectivity on points over an algebraically closed coefficient field
implies injectivity after evaluation in any extension field. -/
theorem injective_aeval_of_injective_eval
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K)
    (hi : Function.Injective (fun x : Fin n → K => fun i => eval x (F i))) :
    Function.Injective (fun x : Fin n → L => fun i => aeval x (F i)) := by
  classical
  let D (j : Fin n) : MvPolynomial (Fin n ⊕ Fin n) K :=
    rename Sum.inl (F j) - rename Sum.inr (F j)
  let I : Ideal (MvPolynomial (Fin n ⊕ Fin n) K) := Ideal.span (Set.range D)
  intro x y hxy
  have hz : Sum.elim x y ∈ MvPolynomial.zeroLocus L I := by
    change Sum.elim x y ∈ MvPolynomial.zeroLocus L (Ideal.span (Set.range D))
    rw [MvPolynomial.zeroLocus_span]
    intro p hp
    obtain ⟨j, rfl⟩ := hp
    simp only [D, map_sub, aeval_rename]
    change aeval x (F j) - aeval y (F j) = 0
    exact sub_eq_zero.mpr (congrFun hxy j)
  funext i
  let d : MvPolynomial (Fin n ⊕ Fin n) K := X (Sum.inl i) - X (Sum.inr i)
  have hd : d ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I]
    change ∀ z ∈ MvPolynomial.zeroLocus K I, aeval z d = 0
    intro z hz'
    have hF : (fun j => eval (fun k => z (Sum.inl k)) (F j)) =
        (fun j => eval (fun k => z (Sum.inr k)) (F j)) := by
      funext j
      have hDj : aeval z (D j) = 0 :=
        hz' (D j) (Ideal.subset_span (Set.mem_range_self j))
      simp only [D, map_sub, aeval_rename] at hDj
      exact sub_eq_zero.mp hDj
    have hpoint := congrFun (hi hF) i
    simpa only [d, map_sub, aeval_X, sub_eq_zero] using hpoint
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hd
  have hp : aeval (Sum.elim x y) (d ^ m) = 0 := hz _ hm
  rw [map_pow] at hp
  have hzero : aeval (Sum.elim x y) d = 0 := by
    by_contra hne
    exact (pow_ne_zero m hne) hp
  simpa only [d, map_sub, aeval_X, Sum.elim_inl, Sum.elim_inr, sub_eq_zero] using hzero

/-- A characteristic-zero field extension with only one embedding into the
algebraic closure of the upper field is trivial. No finite-extension
assumption is needed. -/
theorem algebraMap_surjective_of_subsingleton_emb
    (S E : Type*) [Field S] [Field E] [Algebra S E] [CharZero S]
    [Subsingleton (Field.Emb S E)] :
    Function.Surjective (algebraMap S E) := by
  classical
  have hd : Field.finSepDegree S E = 1 := Nat.card_unique
  haveI : Algebra.IsAlgebraic S E := by
    by_contra h
    haveI : Algebra.Transcendental S E :=
      Algebra.transcendental_iff_not_isAlgebraic.mpr h
    have hz := Field.finSepDegree_eq_zero_of_transcendental S E
    rw [hd] at hz
    exact one_ne_zero hz
  haveI : Algebra.IsSeparable S E := inferInstance
  have hr : Module.finrank S E = 1 :=
    (Field.finSepDegree_eq_finrank_of_isSeparable S E).symm.trans hd
  obtain ⟨v, hv, hspan⟩ := Module.finrank_eq_one_iff'.mp hr
  obtain ⟨a, ha⟩ := hspan (1 : E)
  intro w
  obtain ⟨b, hb⟩ := hspan w
  have ha' : algebraMap S E a * v = 1 := by simpa only [Algebra.smul_def] using ha
  have hb' : algebraMap S E b * v = w := by simpa only [Algebra.smul_def] using hb
  have hane : a ≠ 0 := by
    intro h
    simp [h] at ha'
  refine ⟨b / a, ?_⟩
  rw [map_div₀, div_eq_iff (map_ne_zero hane)]
  rw [← hb', mul_assoc, mul_comm v, ha', mul_one]

/-- The pullback of an injective polynomial map over an algebraically
closed characteristic-zero field is surjective on fraction fields. -/
theorem reduced_coordinates_of_injective_eval
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K)
    (hi : Function.Injective (fun x : Fin n → K => fun i => eval x (F i))) :
    ∀ i : Fin n, ∃ A B : MvPolynomial (Fin n) K,
      IsRelPrime B A ∧ bind₁ F A = bind₁ F B * X i := by
  classical
  let R := MvPolynomial (Fin n) K
  let E := FractionRing R
  let L := AlgebraicClosure E
  have hs := ax_grothendieck_univ F hi
  let g₀ : R →ₐ[K] E :=
    (IsScalarTower.toAlgHom K R E).comp (bind₁ F)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective R E).comp (bind_injective_of_point_surjective F hs)
  let g : E →ₐ[K] E := IsFractionRing.liftAlgHom hg₀
  have hg (p : R) : g (algebraMap R E p) = algebraMap R E (bind₁ F p) := by
    change IsFractionRing.lift hg₀ (algebraMap R E p) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  let S : IntermediateField K E := g.fieldRange
  have hgen (j : Fin n) : algebraMap R E (F j) ∈ S := by
    change ∃ z : E, g z = algebraMap R E (F j)
    refine ⟨algebraMap R E (X j), ?_⟩
    rw [hg, bind₁_X_right]
  haveI : Subsingleton (Field.Emb S E) := by
    constructor
    intro f f'
    let u : Fin n → L := fun j => f (algebraMap R E (X j))
    let v : Fin n → L := fun j => f' (algebraMap R E (X j))
    let φ : R →ₐ[K] L := (f.restrictScalars K).comp (IsScalarTower.toAlgHom K R E)
    let ψ : R →ₐ[K] L := (f'.restrictScalars K).comp (IsScalarTower.toAlgHom K R E)
    have hφ : φ = aeval u := aeval_unique φ
    have hψ : ψ = aeval v := aeval_unique ψ
    have hmaps : (fun j => aeval u (F j)) = (fun j => aeval v (F j)) := by
      funext j
      rw [← hφ, ← hψ]
      let s : S := ⟨algebraMap R E (F j), hgen j⟩
      change f (algebraMap S E s) = f' (algebraMap S E s)
      rw [f.commutes, f'.commutes]
    have huv : u = v := injective_aeval_of_injective_eval F hi hmaps
    have heq : φ = ψ := by rw [hφ, hψ, huv]
    have heq' : f.toRingHom = f'.toRingHom :=
      IsFractionRing.ringHom_ext (A := R) (fun p => DFunLike.congr_fun heq p)
    exact AlgHom.ext (fun z => DFunLike.congr_fun heq' z)
  have hS : Function.Surjective (algebraMap S E) :=
    algebraMap_surjective_of_subsingleton_emb S E
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨w, hw⟩ := hS z
    have hw' : (w : E) = z := hw
    have hm := w.property
    change ∃ q : E, g q = (w : E) at hm
    simpa only [hw'] using hm
  intro i
  obtain ⟨z, hz⟩ := hsurj (algebraMap R E (X i))
  let A : R := IsFractionRing.num R z
  let B : R := IsFractionRing.den R z
  refine ⟨A, B, (IsFractionRing.num_den_reduced R z).symm, ?_⟩
  have he : z * algebraMap R E B = algebraMap R E A :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (A := R)).mpr rfl
  have hm : g (z * algebraMap R E B) = g (algebraMap R E A) :=
    congrArg (fun t : E => g t) he
  rw [map_mul, hz, hg, hg] at hm
  apply IsFractionRing.injective R E
  rw [map_mul]
  exact hm.symm.trans (mul_comm _ _)

/-- An injective polynomial self-map over an algebraically closed field of
characteristic zero has a two-sided polynomial inverse. -/
theorem polynomial_inverse_of_injective_eval
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (F : Fin n → MvPolynomial (Fin n) K)
    (hi : Function.Injective (fun x : Fin n → K => fun i => eval x (F i))) :
    ∃ G : Fin n → MvPolynomial (Fin n) K,
      (∀ i, bind₁ G (F i) = X i) ∧ (∀ i, bind₁ F (G i) = X i) :=
  polynomial_inverse_of_reduced_coordinates F (ax_grothendieck_univ F hi)
    (reduced_coordinates_of_injective_eval F hi)

end
end HC4.PolynomialInverseAudit

#print axioms HC4.PolynomialInverseAudit.injective_aeval_of_injective_eval
#print axioms HC4.PolynomialInverseAudit.algebraMap_surjective_of_subsingleton_emb
#print axioms HC4.PolynomialInverseAudit.reduced_coordinates_of_injective_eval
#print axioms HC4.PolynomialInverseAudit.polynomial_inverse_of_injective_eval

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``HC4.PolynomialInverseAudit.injective_aeval_of_injective_eval,
      ``HC4.PolynomialInverseAudit.algebraMap_surjective_of_subsingleton_emb,
      ``HC4.PolynomialInverseAudit.reduced_coordinates_of_injective_eval,
      ``HC4.PolynomialInverseAudit.polynomial_inverse_of_injective_eval] do
    for dep in (← Lean.collectAxioms decl) do
      unless allowed.contains dep do
        throwError "Unexpected logical dependency {dep} in {decl}"
