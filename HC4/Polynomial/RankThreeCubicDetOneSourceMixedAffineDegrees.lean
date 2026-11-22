import HC4.Polynomial.RankThreeCubicDetOnePoleAffineUnitLinearDivisibility
import Mathlib.Tactic

/-!
# Actual source mixed-Hessian correction is affine in transverse variables

For F of transverse weight at most three, the true weight-two
source layer L2 has longitudinal/transverse Hessian entries of
weight one. The strict subquadratic remainder Rlow has mixed
entries of weight zero. After specializing the longitudinal
variable x=a, pairing each mixed row with any fixed transverse
direction w gives:

  f2(y)   = sum_j Hess(L2)_(x,j)(a,y) w_j  homogeneous degree 1
  flow(y) = sum_j Hess(Rlow)_(x,j)(a,y) w_j  homogeneous degree 0

Thus flow is exactly a scalar constant polynomial, not merely
constant modulo the genuine denominator prime.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The original exact weight-two source layer has a
degree-one mixed Hessian after longitudinal specialization. -/
theorem sourceCubic_secondLayer_mixedSlice_homogeneous_one
    (F : SB K) (a : K) (j : Fin 3) :
    (referenceSlice a
      (hessian (initialForm transverseCubicWeight 2 F)
        (.inl ()) (.inr j))).IsHomogeneous 1 := by
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  have hL2 : L2.IsWeightedHomogeneous transverseCubicWeight 2 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 2 F
  have hH :
      (hessian L2 (.inl ()) (.inr j)).IsWeightedHomogeneous
        transverseCubicWeight 1 := by
    have h := pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL2 (.inl ())) (.inr j)
    simpa [hessian_apply, transverseCubicWeight] using h
  exact referenceSlice_isHomogeneous_of_transverseWeight a _ 1 hH

/-- The original strict-below-two source remainder has
a degree-zero mixed Hessian after longitudinal specialization. -/
theorem sourceCubic_subTwo_mixedSlice_homogeneous_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (j : Fin 3) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    (referenceSlice a (hessian Rlow (.inl ()) (.inr j))).IsHomogeneous 0 := by
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  have hz := sourceCubic_subTwo_mixedHessian_eq_weightZero F hcap j
  have hH :
      (hessian Rlow (.inl ()) (.inr j)).IsWeightedHomogeneous
        transverseCubicWeight 0 := by
    have hi := initialForm_isWeightedHomogeneous transverseCubicWeight 0
      (hessian Rlow (.inl ()) (.inr j))
    rw [hz] at hi
    exact hi
  exact referenceSlice_isHomogeneous_of_transverseWeight a _ 0 hH

/-- The directional mixed Hessian of the source's true
quadratic layer is a homogeneous linear transverse polynomial. -/
theorem sourceCubic_secondLayer_mixedDirectional_homogeneous_one
    (F : SB K) (a : K) (w0 : Fin 3 → K) :
    (∑ j : Fin 3,
      referenceSlice a
        (hessian (initialForm transverseCubicWeight 2 F)
          (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)).IsHomogeneous 1 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  have hj := sourceCubic_secondLayer_mixedSlice_homogeneous_one F a j
  have hc : (MvPolynomial.C (w0 j) : B3 K).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (Fin 3) (w0 j)
  simpa only [add_zero] using hj.mul hc

/-- The directional strictly subquadratic mixed Hessian has
exact transverse degree zero after specializing x=a. -/
theorem sourceCubic_subTwo_mixedDirectional_homogeneous_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (w0 : Fin 3 → K) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    (∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)).IsHomogeneous 0 := by
  classical
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  have hj := sourceCubic_subTwo_mixedSlice_homogeneous_zero F hcap a j
  have hc : (MvPolynomial.C (w0 j) : B3 K).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (Fin 3) (w0 j)
  simpa only [zero_add] using hj.mul hc

/-- The actual strictly subquadratic mixed-directional correction
is a base-field scalar polynomial, before reducing modulo p. -/
theorem sourceCubic_subTwo_mixedDirectional_eq_C
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (w0 : Fin 3 → K) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    let flow : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)
    flow = MvPolynomial.C (flow.coeff 0) := by
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  let flow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
        MvPolynomial.C (w0 j)
  have hh : flow.IsHomogeneous 0 :=
    sourceCubic_subTwo_mixedDirectional_homogeneous_zero
      F hcap a w0
  have hd : flow.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2 hh
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd

end
end HC4.Polynomial.RankThreeCubic
