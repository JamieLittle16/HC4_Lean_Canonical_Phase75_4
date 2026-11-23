import HC4.Polynomial.RankThreeCubicDetOneSourceRankThreeRepairIsotropic
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# The genuine source cubic leading Hessian is globally singular

For the original source F of transverse weight at most three,
the full four-by-four Hessian determinant has maximum possible
transverse weight six. Its weight-six component is exactly the
determinant of the full Hessian of the actual cubic layer L3.

If det Hess F = 1, this weight-six component vanishes.
Consequently det Hess L3 = 0 *in the original source ring*.
In particular every longitudinal slice and every denominator
prime quotient inherits the exact singularity identity.

This eliminates any need to assume singularity as an extra
endpoint or pole-chart hypothesis. It does NOT distinguish
rank two from rank three, nor close either remaining branch.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual source weight-three leading Hessian has identically
zero full four-variable determinant, with no auxiliary assumptions. -/
theorem sourceCubic_detOne_leadingFullHessian_det_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    (hessian (initialForm transverseCubicWeight 3 F)).det = 0 := by
  classical
  have hmax :=
    initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      transverseCubicWeight 3 F hcap
  have hw :
      (Fintype.card (Unit ⊕ Fin 3) : ℤ) * 3 -
        2 * ∑ i : Unit ⊕ Fin 3, transverseCubicWeight i = 6 := by
    decide
  rw [hw, hdetOne] at hmax
  have htop :
      initialForm transverseCubicWeight 6 (1 : SB K) = 0 := by
    have hz := initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C
        transverseCubicWeight (1 : K)) 6 (by norm_num)
    simpa only [map_one] using hz
  change initialForm transverseCubicWeight 6 (1 : SB K) =
    (hessian (initialForm transverseCubicWeight 3 F)).det at hmax
  exact hmax.symm.trans htop

/-- The singularity persists under the actual longitudinal
source slice and reduction modulo any transverse polynomial p.
No irreducibility, rank, or characteristic-pole hypothesis is
needed for this purely functorial consequence. -/
theorem sourceCubic_detOne_slicedFullCubicHessian_det_zero
    (F : SB K) (a : K) (p : B3 K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    (φ.mapMatrix (hessian
      (initialForm transverseCubicWeight 3 F))).det = 0 := by
  classical
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
    q.comp (referenceSlice a).toRingHom
  have hzero := sourceCubic_detOne_leadingFullHessian_det_zero
    F hcap hdetOne
  have hmapped := congrArg φ hzero
  simpa only [RingHom.map_det, map_zero] using hmapped

end
end HC4.Polynomial.RankThreeCubic
