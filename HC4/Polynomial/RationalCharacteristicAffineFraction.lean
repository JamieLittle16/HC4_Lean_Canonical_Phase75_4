module

public import HC4.Polynomial.RationalCharacteristicAffineCoordinates
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Invertible affine substitution and rational extension

The affine polynomial chart has an explicit inverse, and its
fraction-field extension is a ground-field algebra homomorphism.
In particular the transformed source Hessian is regular. These
facts require no bound on the degree of the reference polynomial.

The next bridge transports the characteristic operator and
normalizes its affine parameter pair.
-/

@[expose] public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

namespace RationalCharacteristicAffineFraction

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev Mat (K : Type*) := Matrix (Fin 3) (Fin 3) K

end RationalCharacteristicAffineFraction

open RationalCharacteristicAffineFraction (B E Mat)

theorem rationalAffine_substitution_X
    (M : Mat K) (c : Fin 3 → K) (i : Fin 3) :
    rationalAffine_substitution M c (X i) =
      MvPolynomial.C (c i) + ∑ j : Fin 3, MvPolynomial.C (M i j) * X j := by
  exact MvPolynomial.aeval_X _ _

theorem rationalAffine_substitution_C
    (M : Mat K) (c : Fin 3 → K) (k : K) :
    rationalAffine_substitution M c (MvPolynomial.C k) = MvPolynomial.C k := by
  exact (rationalAffine_substitution M c).commutes k

/-- The contravariant composition law for affine polynomial charts. -/
theorem rationalAffine_substitution_comp
    (M P : Mat K) (c d : Fin 3 → K) :
    (rationalAffine_substitution P d).comp (rationalAffine_substitution M c) =
      rationalAffine_substitution (M * P) (c + M.mulVec d) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  change rationalAffine_substitution P d (rationalAffine_substitution M c (X i)) =
    rationalAffine_substitution (M * P) (c + M.mulVec d) (X i)
  rw [rationalAffine_substitution_X, map_add, map_sum]
  simp only [map_mul, rationalAffine_substitution_C, rationalAffine_substitution_X,
    Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp only [Fin.sum_univ_three, map_add, map_mul]
  ring

/-- The identity chart really is the identity algebra homomorphism. -/
theorem rationalAffine_substitution_one_zero :
    rationalAffine_substitution (1 : Mat K) 0 = AlgHom.id K (B K) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  rw [rationalAffine_substitution_X]
  change MvPolynomial.C (0 : K) +
    ∑ j : Fin 3, MvPolynomial.C ((1 : Mat K) i j) * X j = X i
  rw [map_zero, zero_add, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- An invertible linear part gives a left inverse to the entire
affine substitution, including its translation term. -/
theorem rationalAffine_substitution_injective
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0) :
    Function.Injective (rationalAffine_substitution M c) := by
  classical
  let P : Mat K := M⁻¹
  let d : Fin 3 → K := P.mulVec (-c)
  have hMP : M * P = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have hd : M.mulVec d = -c := by
    change M *ᵥ (P *ᵥ (-c)) = -c
    rw [Matrix.mulVec_mulVec, hMP, Matrix.one_mulVec]
  have hcomp :
      (rationalAffine_substitution P d).comp (rationalAffine_substitution M c) =
        AlgHom.id K (B K) := by
    rw [rationalAffine_substitution_comp, hMP, hd, add_neg_cancel,
      rationalAffine_substitution_one_zero]
  intro f g h
  have he := congrArg (rationalAffine_substitution P d) h
  change ((rationalAffine_substitution P d).comp
    (rationalAffine_substitution M c)) f =
      ((rationalAffine_substitution P d).comp (rationalAffine_substitution M c)) g at he
  rw [hcomp] at he
  exact he

/-- The chart followed by the fraction-field embedding is injective. -/
theorem rationalAffine_embedded_injective
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0) :
    Function.Injective ((IsScalarTower.toAlgHom K (B K) (E K)).comp
      (rationalAffine_substitution M c)) :=
  (IsFractionRing.injective (B K) (E K)).comp
    (rationalAffine_substitution_injective M c hM)

/-- Extend the polynomial chart to the genuine transverse fraction
field. No denominators are discarded by this extension. -/
def rationalAffine_fraction
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0) : E K →ₐ[K] E K :=
  IsFractionRing.liftAlgHom (rationalAffine_embedded_injective M c hM)

theorem rationalAffine_fraction_algebraMap
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0) (f : B K) :
    rationalAffine_fraction M c hM (algebraMap (B K) (E K) f) =
      algebraMap (B K) (E K) (rationalAffine_substitution M c f) := by
  unfold rationalAffine_fraction
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- Source regularity survives the invertible affine chart, with
the exact polynomial determinant identity supplied by the chain rule. -/
theorem rationalAffine_substitution_hessian_det_ne_zero
    (M : Mat K) (c : Fin 3 → K) (hM : M.det ≠ 0)
    (f : B K) (hf : (hessian f).det ≠ 0) :
    (hessian (rationalAffine_substitution M c f)).det ≠ 0 := by
  rw [rationalAffine_substitution_hessian, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  have hC : (M.map (MvPolynomial.C : K →+* B K)).det ≠ 0 := by
    change ((MvPolynomial.C : K →+* B K).mapMatrix M).det ≠ 0
    rw [← RingHom.map_det]
    simpa only [map_zero] using (MvPolynomial.C_injective (Fin 3) K).ne hM
  have hS : ((hessian f).map (rationalAffine_substitution M c).toRingHom).det ≠ 0 := by
    change ((rationalAffine_substitution M c).toRingHom.mapMatrix (hessian f)).det ≠ 0
    rw [← RingHom.map_det]
    change rationalAffine_substitution M c (hessian f).det ≠ 0
    simpa only [map_zero] using (rationalAffine_substitution_injective M c hM).ne hf
  exact mul_ne_zero (mul_ne_zero hC hS) hC

end
end HC4.Polynomial.RankThreeCubic
