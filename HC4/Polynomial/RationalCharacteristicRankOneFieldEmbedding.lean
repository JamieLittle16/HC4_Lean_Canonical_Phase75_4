module

public import HC4.Polynomial.RationalCharacteristicRankOneCoordinateLine
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Specialization as a genuine field embedding

A polynomial map which does not kill the reduced denominators
of an intermediate field extends to that field. Cross multiplication
gives independence of any regular fraction representation, and
the resulting algebra homomorphism is injective because its
domain is a field.

Apply this to the uniform regular coordinate line for a rank-one
velocity Jacobian. The target is mathlib's actual RatFunc field.
-/

@[expose] public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RationalCharacteristicRankOneFieldEmbedding

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev I := Unit ⊕ Fin 3

end RationalCharacteristicRankOneFieldEmbedding

open RationalCharacteristicRankOneFieldEmbedding (B E I)

section Specialization

variable {G : Type*} [Field G] [Algebra K G]

/-- Evaluate the canonical reduced numerator and denominator. -/
def rationalField_specialize
    (F : IntermediateField K (E K)) (φ : B K →ₐ[K] G) (z : F) : G :=
  φ (IsFractionRing.num (B K) (z : E K)) /
    φ (IsFractionRing.den (B K) (z : E K))

/-- Any fraction with a surviving denominator gives the same value
as the canonical reduced pair. -/
theorem rationalField_specialize_eq_div
    (F : IntermediateField K (E K)) (φ : B K →ₐ[K] G)
    (hφ : ∀ z : F, φ (IsFractionRing.den (B K) (z : E K)) ≠ 0)
    (z : F) (p q : B K) (hq : φ q ≠ 0)
    (hz : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = (z : E K)) :
    rationalField_specialize F φ z = φ p / φ q := by
  let e := algebraMap (B K) (E K)
  let n : B K := IsFractionRing.num (B K) (z : E K)
  let d : B K := IsFractionRing.den (B K) (z : E K)
  have hd : d ≠ 0 := nonZeroDivisors.coe_ne_zero
    (IsFractionRing.den (B K) (z : E K))
  have hq0 : q ≠ 0 := by
    intro h
    exact hq (by rw [h, map_zero])
  have hde : e d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hd
  have hqe : e q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq0
  have he : e n / e d = (z : E K) := IsFractionRing.mk'_num_den' (B K) (z : E K)
  have hcross : n * q = p * d := by
    apply IsFractionRing.injective (B K) (E K)
    change e (n * q) = e (p * d)
    simp only [map_mul]
    exact (div_eq_div_iff hde hqe).mp (he.trans hz.symm)
  change φ n / φ d = φ p / φ q
  apply (div_eq_div_iff (hφ z) hq).mpr
  simpa only [map_mul] using congrArg φ hcross

/-- A surviving-denominator specialization is a ground-field
algebra homomorphism on the entire intermediate field. -/
def rationalField_specializationHom
    (F : IntermediateField K (E K)) (φ : B K →ₐ[K] G)
    (hφ : ∀ z : F, φ (IsFractionRing.den (B K) (z : E K)) ≠ 0) :
    F →ₐ[K] G where
  toFun := rationalField_specialize F φ
  map_zero' := by
    rw [rationalField_specialize_eq_div F φ hφ 0 0 1 (by simp) (by simp)]
    simp
  map_one' := by
    rw [rationalField_specialize_eq_div F φ hφ 1 1 1 (by simp) (by simp)]
    simp
  map_add' := by
    intro x y
    let e := algebraMap (B K) (E K)
    let p : B K := IsFractionRing.num (B K) (x : E K)
    let q : B K := IsFractionRing.den (B K) (x : E K)
    let r : B K := IsFractionRing.num (B K) (y : E K)
    let s : B K := IsFractionRing.den (B K) (y : E K)
    have hx : e p / e q = (x : E K) := IsFractionRing.mk'_num_den' (B K) (x : E K)
    have hy : e r / e s = (y : E K) := IsFractionRing.mk'_num_den' (B K) (y : E K)
    have hq : φ q ≠ 0 := hφ x
    have hs : φ s ≠ 0 := hφ y
    have hqe : e q ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne
        (nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) (x : E K)))
    have hse : e s ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne
        (nonZeroDivisors.coe_ne_zero (IsFractionRing.den (B K) (y : E K)))
    have hqs : φ (q * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hq hs
    have hxy : e (p * s + r * q) / e (q * s) = ((x + y : F) : E K) := by
      change e (p * s + r * q) / e (q * s) = (x : E K) + (y : E K)
      rw [← hx, ← hy, map_add, map_mul, map_mul, map_mul]
      field_simp [hqe, hse] <;> ring
    rw [rationalField_specialize_eq_div F φ hφ (x+y) _ _ hqs hxy]
    change φ (p * s + r * q) / φ (q * s) = φ p / φ q + φ r / φ s
    simp only [map_add, map_mul]
    field_simp [hq, hs] <;> ring
  map_mul' := by
    intro x y
    let e := algebraMap (B K) (E K)
    let p : B K := IsFractionRing.num (B K) (x : E K)
    let q : B K := IsFractionRing.den (B K) (x : E K)
    let r : B K := IsFractionRing.num (B K) (y : E K)
    let s : B K := IsFractionRing.den (B K) (y : E K)
    have hx : e p / e q = (x : E K) := IsFractionRing.mk'_num_den' (B K) (x : E K)
    have hy : e r / e s = (y : E K) := IsFractionRing.mk'_num_den' (B K) (y : E K)
    have hqs : φ (q * s) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero (hφ x) (hφ y)
    have hxy : e (p * r) / e (q * s) = ((x * y : F) : E K) := by
      change e (p * r) / e (q * s) = (x : E K) * (y : E K)
      rw [← hx, ← hy, map_mul, map_mul, div_mul_div_comm]
    rw [rationalField_specialize_eq_div F φ hφ (x*y) _ _ hqs hxy]
    change φ (p * r) / φ (q * s) = φ p / φ q * (φ r / φ s)
    rw [map_mul, map_mul, div_mul_div_comm]
  commutes' := by
    intro a
    have ha : algebraMap (B K) (E K) (MvPolynomial.C a) /
        algebraMap (B K) (E K) 1 =
          ((algebraMap K F a : F) : E K) := by
      rw [map_one, div_one]
      exact (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    rw [rationalField_specialize_eq_div F φ hφ (algebraMap K F a)
      (MvPolynomial.C a) 1 (by simp) ha, map_one, div_one]
    exact φ.commutes a

end Specialization

variable [CharZero K]

/-- The field of the actual rank-one velocity components embeds
over K into the univariate rational function field. -/
theorem rankOne_velocityField_exists_embedding
    (V : I → E K)
    (hn : rationalCharacteristicJacobian V ≠ 0)
    (hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    let F := IntermediateField.adjoin K (Set.range (fun a : Fin 3 => V (.inr a)))
    ∃ ψ : F →ₐ[K] RatFunc K, Function.Injective ψ := by
  classical
  obtain ⟨i, j, hp, _⟩ := rankOne_jacobian_exists_pivot V hn hm
  obtain ⟨c, hc⟩ := rankOne_velocityField_exists_regular_line V i j hp
    (fun a b => hm a b i j)
  let F := IntermediateField.adjoin K (Set.range (fun a : Fin 3 => V (.inr a)))
  let φ := (IsScalarTower.toAlgHom K (_root_.Polynomial K) (RatFunc K)).comp
    (rankOne_coordinateLine j c)
  have hφ (z : F) : φ (IsFractionRing.den (B K) (z : E K)) ≠ 0 := by
    let p : B K := IsFractionRing.num (B K) (z : E K)
    let q : B K := IsFractionRing.den (B K) (z : E K)
    have hq : q ≠ 0 := nonZeroDivisors.coe_ne_zero
      (IsFractionRing.den (B K) (z : E K))
    have hcop : IsRelPrime p q := IsFractionRing.num_den_reduced (B K) (z : E K)
    have hz : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q ∈ F := by
      rw [IsFractionRing.mk'_num_den' (B K) (z : E K)]
      exact z.property
    have h := (hc p q hq hcop hz).1
    change algebraMap (_root_.Polynomial K) (RatFunc K)
      (rankOne_coordinateLine j c q) ≠ 0
    simpa only [map_zero] using (RatFunc.algebraMap_injective (K := K)).ne h
  let ψ := rationalField_specializationHom F φ hφ
  exact ⟨ψ, ψ.toRingHom.injective⟩

end
end HC4.Polynomial.RankThreeCubic
