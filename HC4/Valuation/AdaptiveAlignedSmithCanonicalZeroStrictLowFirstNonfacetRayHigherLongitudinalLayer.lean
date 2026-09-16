import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayAllLayersPreclosing
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOnePencil
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import Mathlib.Tactic

/-!
# A19.109: the strict-low source forces a higher-longitudinal ray deformation

The locked `.qs` ray is degree one in source coordinate `0`: every supported
ray monomial has longitudinal exponent at most one.  The actual strict-low
source, however, contains a certified supported monomial with longitudinal
exponent at least two.

For the A19.104b reverse-Rees weight this monomial therefore cannot have maximal
weight, because the maximal initial form is literally the locked ray.  Its
weight drop is strictly positive, so it occurs in an honest positive parameter
layer of the ray-leading family.  A19.107 then puts that layer strictly before
Hessian determinant closure.

This is the concrete degree-at-least-two staircase seed which the old abstract
weighted-profile certificate was missing.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- A genuine positive reverse-Rees layer carrying an actual source monomial
with longitudinal exponent at least two. -/
structure QsOtherFacetRayHigherLongitudinalLayerWitness
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (R : QsOtherFacetRayReverseReesPackage C) where
  order : ℕ
  order_pos : 0 < order
  order_mem :
    order ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)
  order_lt_defect :
    order < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i
  exponent : Fin 4 →₀ ℕ
  exponent_source :
    exponent ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support
  exponent_layer :
    exponent ∈
      (familyParameterLayer
        (reverseWeightedReesFamily R.weight R.level
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) R.bound)
        order).support
  longitudinal_two_le : 2 ≤ exponent (0 : Fin 4)
  ordinaryDegree_three_le : 3 ≤ HC4.Polynomial.ordinaryDegree4 exponent

/-- **A19.109 higher-longitudinal staircase seed.** -/
theorem QsOtherFacetRayReverseReesPackage.higherLongitudinalLayerWitness
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    Nonempty (QsOtherFacetRayHigherLongitudinalLayerWitness C R) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let Q : MvPolynomial (Fin 4) (Polynomial K) :=
    reverseWeightedReesFamily R.weight R.level F R.bound
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨e, heF, hedeg, he0, _hecodim⟩

  have heweight_le : Finsupp.weight R.weight e ≤ R.level :=
    R.bound e heF
  have heweight_lt : Finsupp.weight R.weight e < R.level := by
    by_contra hnot
    have heq : Finsupp.weight R.weight e = R.level := by omega
    have heqZ :
        Finsupp.weight (fun i : Fin 4 => (R.weight i : ℤ)) e =
          (R.level : ℤ) := by
      rw [weight_natCast_eq]
      exact_mod_cast heq
    have hcoeffInit :
        MvPolynomial.coeff e
          (HC4.Polynomial.initialForm
            (fun i : Fin 4 => (R.weight i : ℤ))
            (R.level : ℤ) F) ≠ 0 := by
      rw [HC4.Polynomial.coeff_initialForm, if_pos heqZ]
      exact MvPolynomial.mem_support_iff.mp heF
    have heRay : e ∈ C.ray.face.support := by
      have hmem := MvPolynomial.mem_support_iff.mpr hcoeffInit
      rw [R.initialForm_eq_ray] at hmem
      exact hmem
    have hidx :
        e (0 : Fin 4) ∈ C.ray.zeroCoefficientPolynomial.support :=
      C.ray.zeroCoefficientPolynomial_mem_of_face_mem heRay
    have hdegRay : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
      C.qs_ray_terminal_degreeOne hthree
    have he0le : e (0 : Fin 4) ≤ 1 := by
      rw [← hdegRay]
      exact Polynomial.le_natDegree_of_mem_supp _ hidx
    omega

  let n : ℕ := R.level - Finsupp.weight R.weight e
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have heLayer :
      e ∈ (familyParameterLayer Q n).support := by
    dsimp [Q]
    rw [reverseWeightedReesFamily_parameterLayer_mem_iff]
    exact ⟨heF, rfl⟩
  have hlayerCoeff :
      MvPolynomial.coeff e (familyParameterLayer Q n) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp heLayer
  have hQcoeffn : (MvPolynomial.coeff e Q).coeff n ≠ 0 := by
    rw [← familyParameterLayer_coeff]
    exact hlayerCoeff
  have heQ : e ∈ Q.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hQcoeffn
    simp at hQcoeffn
  have hnmem : n ∈ familyParameterLayerOrders Q :=
    (mem_familyParameterLayerOrders_iff Q n).2 ⟨e, heQ, hQcoeffn⟩
  have hnlt : n < 4 * R.level - 2 * ∑ i : Fin 4, R.weight i := by
    dsimp [Q] at hnmem
    exact R.actualLayerOrder_lt_defect hnmem

  exact ⟨{
    order := n
    order_pos := hnpos
    order_mem := by simpa [Q] using hnmem
    order_lt_defect := hnlt
    exponent := e
    exponent_source := by simpa [F] using heF
    exponent_layer := by simpa [Q] using heLayer
    longitudinal_two_le := he0
    ordinaryDegree_three_le := hedeg
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
