/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-

Vendored from mathlib4 commit 348837d3aa976624060d7c35c183fff587c5a24a, Mathlib/FieldTheory/RatFunc/Luroth.lean.
Modified for HC4: remove newer module visibility/documentation commands and redirect
local backport imports. Original mathematical proof retained.
-/

import HC4.Backport.RatFuncIntermediateField

import Mathlib.Algebra.Polynomial.Basis
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Lüroth's theorem

This file proves Lüroth's theorem, which says that for every field `K`, every
intermediate field between `K` and the rational function field `(RatFunc K)` is either
`K` or isomorphic to `K(X)` as an K-algebra, see `Luroth.eq_adjoin_generator`. The proof
depends on the following lemma on degrees of rational functions:

Let `f` be a rational function, i.e. an element in the field `(RatFunc K)`.
Let `p` be its numerator and `q` its denominator. Then the degree of the
field extension `(RatFunc K)/K⟮f⟯` equals the maximum of the degrees of `p` and `q`,
see `finrank_eq_max_natDegree`. Since `finrank` is defined to be zero when the
extension is infinite, this holds even when `f` is constant.

## References

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- [P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*][cohn_2003], Theorem 11.3.4
- [N. Jacobson, *Basic Algebra II: Second Edition*][jacobson1989], Theorem 8.38
-/

variable {K : Type*} [Field K]

open IntermediateField

namespace RatFunc.Luroth

noncomputable section

open algebraAdjoinAdjoin Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K (RatFunc K)}

-- The proof of Lüroth's theorem begins here. We follow the approach from
-- [Cohn, Basic Algebra: Groups, Rings and Fields][cohn_2003].

variable (E) in
/-- The minimal polynomial of `X` with coefficients in `E`. -/
abbrev φ : E[X] := minpoly E (X : (RatFunc K))

lemma φ_ne_zero (h : E ≠ ⊥) : φ E ≠ 0 :=
  minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

lemma φ_monic (h : E ≠ ⊥) : (φ E).Monic :=
  minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

lemma φ_natDegree (h : E ≠ ⊥) : (φ E).natDegree = Module.finrank E (RatFunc K) := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq,
    adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

/-- Since `X` is transcendental over `K`, not all coefficients of `φ` can be in `K`. -/
lemma exists_φ_coeff_not_mem (h : E ≠ ⊥) :
    ∃ i, (φ E).coeff i ∉ (algebraMap K E).range := by
  classical
  by_contra hn
  push_neg at hn
  choose a ha using hn
  let f : K[X] := ∑ i ∈ (φ E).support, monomial i (a i)
  have hf : f.map (algebraMap K E) = φ E := by
    change (∑ i ∈ (φ E).support, monomial i (a i)).map (algebraMap K E) = _
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_monomial, ha]
    exact sum_monomial_eq _
  refine transcendental_X ⟨f, ?_, ?_⟩
  · intro hz
    apply φ_ne_zero h
    rw [← hf, hz, Polynomial.map_zero]
  · rw [← aeval_map_algebraMap E, hf]
    exact minpoly.aeval E _

/-- A choice of coefficient index `i` such that `φ.coeff i` is not in `K`. -/
def generatorIndex (h : E ≠ ⊥) : ℕ :=
  (exists_φ_coeff_not_mem h).choose

variable (E) in
open scoped Classical in
/-- A choice of a generator for Lüroth's theorem, see `Luroth.eq_adjoin_generator`. -/
def generator : (RatFunc K) :=
  if h : E = ⊥ then 0 else (φ E).coeff (generatorIndex h)

lemma generator_eq_zero (h : E = ⊥) : generator E = 0 :=
  by simp [generator, h]

lemma generator_eq_coeff (h : E ≠ ⊥) : generator E = (φ E).coeff (generatorIndex h) :=
  by simp [generator, h]

lemma generator_mem : generator E ∈ E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h]
    exact SetLike.coe_mem _

lemma generator_spec (h : E ≠ ⊥) : generator E ∉ (algebraMap K (RatFunc K)).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

lemma generator_ne_C (h : E ≠ ⊥) : ¬ ∃ c, generator E = C c :=
  fun ⟨c, hc⟩ ↦ generator_spec h ⟨c, (by simpa using hc.symm)⟩

lemma transcendental_generator (h : E ≠ ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

lemma generator_ne_zero (h : E ≠ ⊥) : generator E ≠ 0 :=
  fun H ↦ generator_ne_C h ⟨0, by simp [H]⟩

lemma adjoin_generator_le : K⟮generator E⟯ ≤ E :=
  adjoin_simple_le_iff.mpr generator_mem

variable (E) in
/-- The numerator of the generator. -/
abbrev f : K[X] := (generator E).num

variable (E) in
/-- The denominator of the generator. -/
abbrev g : K[X] := generator E |>.denom

-- The next step is to define a bivariate polynomial `Φ`, which is a multiple of `φ`.
-- Cohn does this my "multiplying with the lowest common denominator". In this formalisation,
-- we first define `Φ'` as any integer multiple of `φ`, and then set `Φ` to be its
-- primitive part.

variable (E) in
/-- The integer normalization of `φ` as a bivariate polynomial. -/
abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E (RatFunc K)))

lemma Φ'_ne_zero (h : E ≠ ⊥) : Φ' E ≠ 0 :=
  IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))

variable (E) in
/-- A polynomial `b` that satisfies `b * φ = Φ'`. -/
def b : K[X] :=
  (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E (RatFunc K)))).choose

lemma b_ne_zero : b E ≠ 0 :=
  nonZeroDivisors.coe_ne_zero (IsLocalization.integerNormalization_map_to_map
    (nonZeroDivisors K[X]) ((φ E).map (algebraMap E (RatFunc K)))).choose

lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] (RatFunc K)) = (b E) • (φ E).map (algebraMap ..) :=
  (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E (RatFunc K)))).choose_spec

variable (E) in
open scoped Classical in
/-- A rational function `c` that satisfies `c * φ = Φ`. This is `ν₀(x)` in Cohn's notation. -/
abbrev c : (RatFunc K) :=
  (algebraMap K[X] (RatFunc K) (Φ' E).content)⁻¹ * (algebraMap K[X] (RatFunc K) (b E))

open scoped Classical in
lemma c_ne_zero (h : E ≠ ⊥) : c E ≠ 0 :=
  mul_ne_zero_iff.mpr ⟨inv_ne_zero <| (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr <|
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

variable (E) in
open scoped Classical in
/-- The primitive part of `Φ'`. -/
abbrev Φ : K[X][Y] := (Φ' E).primPart

/-- We have `c * φ = Φ` as polynomials with coefficients in `Ratfunc K`. See Equation
  (11.3.5) in Cohn's proof. -/
lemma C_c_mul_φ (h : E ≠ ⊥) :
    Polynomial.C (c E) * (φ E).map (algebraMap E (RatFunc K)) = (Φ E).map (algebraMap ..) := by
  classical
  rw [map_mul, mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← Φ'_map, eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀, map_one, one_mul]
  rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
  exact Φ'_ne_zero h

lemma Φ_natDegree_eq_φ_natDegree (h : E ≠ ⊥) : (Φ E).natDegree = (φ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K), ← C_c_mul_φ h,
    natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h)), natDegree_C,
    natDegree_map, zero_add]

lemma Φ_coeff_φ_natDegree (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (φ E).natDegree) = c E := by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
    φ_monic h, OneMemClass.coe_one, mul_one] at this
  exact this.symm

lemma c_denom (h : E ≠ ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

lemma Φ_coeff_φ_natDegree' (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

lemma Φ_coeff_φ_natDegree_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (φ E).natDegree ≠ 0 := by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

lemma Φ_coeff_generatorIndex (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] (RatFunc K) (c E).num * generator E := by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply,
    ← num_div_denom (c E), c_denom h, map_one, div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

lemma Φ_coeff_generatorIndex_ne_zero (h : E ≠ ⊥) :
    (Φ E).coeff (generatorIndex h) ≠ 0 := by
  apply_fun algebraMap K[X] (RatFunc K)
  rw [map_zero, Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

lemma generator_denom_dvd_c_num (h : E ≠ ⊥) : (g E) ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h,
    mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

lemma Φ_ne_zero (h : E ≠ ⊥) : Φ E ≠ 0 := by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

-- Next, we show that `Φ` has degree at least `m := max(deg(f), deg(g))` in `x`, where
-- `f` and `g` are the numerator and denominator of the `generator`. Cohn mentions
-- this right after Equation (11.3.8). To prove it, we show that the leading coefficient
-- `ν₀(x)` has degree at least `deg(f)`, while `νᵢ(x)` (our chosen coefficient index) has
-- degree at least `deg(g)`. The claim then follows from the fact that the monomials `X ^ i`
-- are linearly independent, see `le_swap_Φ_natDegree`.

lemma le_Φ_coeff_generatorIndex_natDegree (h : E ≠ ⊥) :
    (f E).natDegree ≤ ((Φ E).coeff (generatorIndex h)).natDegree := by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] (RatFunc K) (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc, div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero),
    ← map_mul, ← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero,
    natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  have hd := natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))
  change (generator E).denom.natDegree ≤ (c E).num.natDegree at hd
  change (generator E).num.natDegree ≤ ((Φ E).coeff (generatorIndex h)).natDegree
  omega

lemma le_Φ_coeff_natDegree_natDegree (h : E ≠ ⊥) :
    (g E).natDegree ≤ ((Φ E).coeff (φ E).natDegree).natDegree := by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

variable (E) in
/-- The height of `generator E`. -/
abbrev m : ℕ := max (f E).natDegree (g E).natDegree

/-- Compatibility: the older bivariate swap is already an involution. -/
private theorem swap_twice (p : K[X][Y]) : Bivariate.swap (Bivariate.swap p) = p :=
  AlgEquiv.symm_apply_apply Bivariate.swap p

private theorem swap_const (p : K[X]) :
    Bivariate.swap (Polynomial.C p) = p.map Polynomial.C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, Polynomial.map_add]
  | monomial n a =>
    simpa [Polynomial.map_monomial] using
      (Bivariate.swap_monomial_monomial (R := K) 0 n a)

private theorem swap_map_const (p : K[X]) :
    Bivariate.swap (p.map Polynomial.C) = Polynomial.C p := by
  rw [← swap_const, swap_twice]

private theorem swap_const_const (a : K) :
    Bivariate.swap (Polynomial.C (Polynomial.C a)) = Polynomial.C (Polynomial.C a) := by
  rw [swap_const, map_C]

/-- Interchanging variables transposes the coefficient array. -/
private theorem swap_coeff_coeff (p : K[X][Y]) (i j : ℕ) :
    ((Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, coeff_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [monomial_add, map_add, coeff_add, coeff_add, coeff_add, coeff_add, ha, hb]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hi : i = m <;> by_cases hj : j = n <;>
        simp [coeff_monomial, hi, hj, eq_comm]

private theorem coeff_degree_le_swap (p : K[X][Y]) (i : ℕ) :
    (p.coeff i).natDegree ≤ (Bivariate.swap p).natDegree := by
  by_cases h : p.coeff i = 0
  · simp [h]
  · apply le_natDegree_of_ne_zero
    intro hz
    have hh := congrArg (fun q : K[X] => q.coeff i) hz
    change ((Bivariate.swap p).coeff (p.coeff i).natDegree).coeff i =
      (0 : K[X]).coeff i at hh
    rw [swap_coeff_coeff, coeff_zero, coeff_natDegree] at hh
    exact leadingCoeff_ne_zero.mpr h hh

lemma m_le_swap_Φ_natDegree (h : E ≠ ⊥) :
    m E ≤ (Bivariate.swap (Φ E)).natDegree := by
  exact max_le
    ((le_Φ_coeff_generatorIndex_natDegree h).trans (coeff_degree_le_swap _ _))
    ((le_Φ_coeff_natDegree_natDegree h).trans (coeff_degree_le_swap _ _))

instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

instance : IsScalarTower K⟮generator E⟯ E (RatFunc K) where
  smul_assoc x y z := by
    change ((x : RatFunc K) * (y : RatFunc K)) * z =
      (x : RatFunc K) * ((y : RatFunc K) * z)
    exact mul_assoc _ _ _

/-- Since `minpolyX` of our `generator` annihilates `X`, the minimal polynomial `φ`
must divide it. -/
lemma φ_dvd_generator_minpolyX :
    φ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hcomp : (algebraMap E (RatFunc K)).comp (algebraMap K⟮generator E⟯ E) =
      algebraMap K⟮generator E⟯ (RatFunc K) := by
    ext x
    rfl
  rw [hcomp]
  exact (generator E).minpolyX_aeval_X

variable (E) in
/-- A polynomial `q` that satisfies `φ * q = (generator E).minpolyX`. -/
abbrev q : E[X] := φ_dvd_generator_minpolyX.choose

lemma φ_mul_q :
    φ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  φ_dvd_generator_minpolyX.choose_spec.symm

lemma q_ne_zero (h : E ≠ ⊥) : q E ≠ 0 := right_ne_zero_of_mul <|
  φ_mul_q (E := E) ▸ Polynomial.map_ne_zero <|
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

-- The next series of definitions concerns the polynomial `Q` in Cohn's proof.
-- A priori, it will be a polynomial with coefficients in `(RatFunc K)`, which we call `Q₀`.
-- We then show that `Q₀` is also a polynomial in the other variable, hence we get
-- a bivariate polynomial `Q₁`. Then we show that it is independent of `X`, hence we may
-- replace it by a univariate polynomial `Q₂`. Finally, we prove that it is also independent
-- of `x`, hence we replace it by a constant `Q₃`.

variable (E) in
/-- A polynomial `Q₀` with coefficients in `(RatFunc K)` that satisfies `Q₀ * Φ = θ`. -/
abbrev Q₀ : (RatFunc K)[X] :=
  Polynomial.C ((algebraMap K[X] (RatFunc K) (g E)) / c E) * (q E).map (algebraMap E (RatFunc K))

lemma Q₀_ne_zero (h : E ≠ ⊥) : Q₀ E ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

variable (E) in
/-- The bivariate polynomial `g(X) * f(Y) - f(X) * g(Y)`, where `f` and `g` are
the numerator and denominator of `generator`. This is an auxiliary definition
for the proof of Lüroth's theorem. -/
abbrev θ : K[X][Y] :=
  Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

lemma swap_θ : Bivariate.swap (θ E) = -(θ E) := by
  rw [map_sub, map_mul, map_mul, swap_const, swap_map_const, swap_const,
    swap_map_const]
  ring

lemma θ_natDegree_le (h : E ≠ ⊥) : (θ E).natDegree ≤ m E := by
  convert natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

/-- Equation (11.3.8) from Cohn's proof, viewed as an equation of polynomials with coefficients
in `(RatFunc K)`. -/
lemma Q₀_mul_Φ (h : E ≠ ⊥) :
    Q₀ E * (Φ E).map (algebraMap K[X] (RatFunc K)) = (θ E).map (algebraMap K[X] (RatFunc K)) := by
  suffices
    Polynomial.C ((algebraMap K[X] (RatFunc K)) (g E)) * (q E).map (algebraMap (↥E) (RatFunc K)) *
       (φ E).map (algebraMap (↥E) (RatFunc K)) = (θ E).map (algebraMap K[X] (RatFunc K)) by
    rw [← C_c_mul_φ h, mul_assoc, ← mul_assoc _ (Polynomial.C (c E)) _,
      mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc, ← Polynomial.map_mul, mul_comm (q E) (φ E), φ_mul_q,
    Polynomial.map_map]
  have hcomp : (algebraMap E (RatFunc K)).comp (algebraMap K⟮generator E⟯ E) =
      algebraMap K⟮generator E⟯ (RatFunc K) := by
    ext x
    rfl
  rw [hcomp]
  have hmap : ((generator E).minpolyX K⟮generator E⟯).map
      (algebraMap K⟮generator E⟯ (RatFunc K)) =
      (f E).map (algebraMap K (RatFunc K)) -
        Polynomial.C (generator E) * (g E).map (algebraMap K (RatFunc K)) := by
    rw [RatFunc.minpolyX, Polynomial.map_sub, Polynomial.map_mul, map_C,
      Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    rfl
  rw [hmap, mul_sub, ← mul_assoc, ← Polynomial.C_mul]
  have hg : algebraMap K[X] (RatFunc K) (g E) * generator E =
      algebraMap K[X] (RatFunc K) (f E) := by
    rw [mul_comm]
    exact ((div_eq_iff (algebraMap_ne_zero (generator E).denom_ne_zero)).mp
      (num_div_denom (generator E))).symm
  rw [hg]
  simp only [θ, Polynomial.map_sub, Polynomial.map_mul, map_C, Polynomial.map_map,
    RatFunc.algebraMap_comp_C, RatFunc.algebraMap_eq_C]

/-- Primitive factors do not hide denominators in a polynomial product.
This is the needed part of the upstream Gauss lemma backport. -/
private theorem primitive_product_lifts
    (f : K[X][Y]) (hf : f.IsPrimitive) (g : (RatFunc K)[X])
    (k : K[X][Y])
    (hk : k.map (algebraMap K[X] (RatFunc K)) =
      g * f.map (algebraMap K[X] (RatFunc K))) :
    ∃ q : K[X][Y], q.map (algebraMap K[X] (RatFunc K)) = g := by
  classical
  let g' := IsLocalization.integerNormalization (nonZeroDivisors K[X]) g
  obtain ⟨⟨b, hb₁⟩, hb₂⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X]) g
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hnorm : g'.map (algebraMap K[X] (RatFunc K)) = b • g := hb₂
  have hprod : g' * f = b • k := by
    apply Polynomial.map_injective (algebraMap K[X] (RatFunc K)) (RatFunc.algebraMap_injective K)
    rw [Polynomial.map_smul, algebraMap_smul, hk, ← smul_mul_assoc, ← hnorm, Polynomial.map_mul]
  have hc : g'.content = b * (normUnit b : K[X]) * k.content := by
    have hh := congrArg Polynomial.content hprod
    rw [Polynomial.smul_eq_C_mul] at hh
    simpa only [content_mul, hf.content_eq_one, mul_one, content_C,
      normalize_apply] using hh
  refine ⟨Polynomial.C (normUnit b : K[X]) * Polynomial.C k.content * g'.primPart, ?_⟩
  rw [← smul_right_inj hb, ← hnorm]
  rw (occs := [2]) [eq_C_content_mul_primPart g']
  rw [hc]
  simp only [Polynomial.map_mul, map_C, map_mul, Algebra.smul_def,
    Polynomial.algebraMap_apply]
  ring

lemma Q₀_mem_lifts (h : E ≠ ⊥) : Q₀ E ∈ lifts (algebraMap K[X] (RatFunc K)) := by
  classical
  exact primitive_product_lifts (Φ E) ((Φ' E).isPrimitive_primPart)
    (Q₀ E) (θ E) (Q₀_mul_Φ h).symm

/-- A bivariate polynomial `Q₁` that satisfies `Q₁ * Φ = θ`. -/
abbrev Q₁ (h : E ≠ ⊥) : K[X][Y] := (Q₀_mem_lifts h).choose

lemma map_Q₁ (h : E ≠ ⊥) : (Q₁ h).map (algebraMap K[X] (RatFunc K)) = Q₀ E :=
  (Q₀_mem_lifts h).choose_spec

lemma Q₁_ne_zero (h : E ≠ ⊥) : Q₁ h ≠ 0 := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K))
  rw [map_Q₁, Polynomial.map_zero]
  exact Q₀_ne_zero h

/-- Equation (11.3.8) from Cohn's proof, viewed as an equation of bivariate polynomials. -/
lemma Q₁_mul_Φ (h : E ≠ ⊥) : Q₁ h * Φ E = θ E := by
  apply_fun Polynomial.map (algebraMap K[X] (RatFunc K)) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul, map_Q₁, Q₀_mul_Φ h]

lemma swap_Q₁_natDegree (h : E ≠ ⊥) : (Bivariate.swap (Q₁ h)).natDegree = 0 := by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree ≤ m E := by
    rw [swap_θ, natDegree_neg]
    exact θ_natDegree_le h
  have hm := m_le_swap_Φ_natDegree h
  omega

/-- A univariate polynomial `Q₂` that satisfies `Q₂ * Φ = θ`. -/
abbrev Q₂ (h : E ≠ ⊥) : K[X] := (Bivariate.swap (Q₁ h)).coeff 0

lemma Q₂_map (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C = Q₁ h := by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [swap_twice, swap_const] at this
  exact this.symm

lemma Q₂_ne_zero (h : E ≠ ⊥) : Q₂ h ≠ 0 := by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero, Q₂_map]
  exact Q₁_ne_zero h

/-- Equation (11.3.8) from Cohn's proof, where we view `Q` as a univariate polynomial. -/
lemma Q₂_mul_Φ (h : E ≠ ⊥) : (Q₂ h).map Polynomial.C * Φ E = θ E := by
  rw [Q₂_map h, Q₁_mul_Φ h]

attribute [local instance] Polynomial.algebra in
lemma Q₂_natDegree (h : E ≠ ⊥) : (Q₂ h).natDegree = 0 := by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).backport_eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not, ← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (fun hz => H (by rw [hz]))
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def, eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C, isUnit_iff_ne_zero, Polynomial.isUnit_C, isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero) <|
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero, ← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
      exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))) <|
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
  have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom <|
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂, Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have hfunit : IsUnit ((f E).mapRingHom (algebraMap K F)) :=
    isCoprime.isRelPrime dvd_rfl this.dvd
  have hgunit : IsUnit ((g E).mapRingHom (algebraMap K F)) :=
    this.isUnit hfunit
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit hfunit),
    by simpa using (natDegree_eq_zero_of_isUnit hgunit)⟩

/-- A constant `Q₃` that satisfies `Q₃ * Φ = θ`. -/
abbrev Q₃ (h : E ≠ ⊥) : K := (Q₂ h).coeff 0

lemma Q₃_map (h : E ≠ ⊥) : Polynomial.C (Q₃ h) = Q₂ h :=
  (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

/-- Equation (11.3.8) from Cohn's proof, where we view `Q` as a constant. -/
lemma Q₃_mul_Φ (h : E ≠ ⊥) : (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E := by
  rw [Q₃_map h, Q₂_mul_Φ h]

lemma Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Φ E).natDegree = (θ E).natDegree := by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

lemma swap_Φ_natDegree_eq_θ_natDegree (h : E ≠ ⊥) :
    (Bivariate.swap (Φ E)).natDegree = (θ E).natDegree := by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, swap_const_const,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this

/-- Lüroth's theorem. Any intermediate field between `K` and `(RatFunc K)` is
generated by a single element `generator E`. See also `transcendental_generator`
for the statement that the generator is transcendental if `E ≠ ⊥`. -/
theorem eq_adjoin_generator : E = K⟮generator E⟯ := by
  by_cases h : E = ⊥
  · rwa [generator_eq_zero h, adjoin_zero]
  have hd : (φ E).natDegree = m E := by
    rw [← Φ_natDegree_eq_φ_natDegree h, Φ_natDegree_eq_θ_natDegree h]
    exact le_antisymm (θ_natDegree_le h)
      (swap_Φ_natDegree_eq_θ_natDegree h ▸ m_le_swap_Φ_natDegree h)
  have hm : m E ≠ 0 := by
    intro H
    exact generator_ne_C h ((backport_eq_C_iff _).mpr (Nat.max_eq_zero_iff.mp H))
  have hr : relfinrank K⟮generator E⟯ E = 1 := by
    have hh := relfinrank_mul_finrank_top (adjoin_generator_le (E := E))
    rw [← φ_natDegree h, hd, (generator E).finrank_eq_max_natDegree] at hh
    exact (mul_eq_right₀ hm).mp hh
  rw [relfinrank_eq_finrank_of_le (adjoin_generator_le (E := E)),
    IntermediateField.finrank_eq_one_iff] at hr
  have hh := congrArg (IntermediateField.restrictScalars K) hr
  simpa only [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_bot_eq_self] using hh


end

end RatFunc.Luroth
