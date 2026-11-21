import HC4.Polynomial.RankThreeFractionBridge
import HC4.Polynomial.LogHessianMoments
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# A18.5.5: rank-three moment determinant to fraction-core determinant

`RankThreeFractionBridge` starts from the logarithmic core after the ratios
`rho = E(phi)/phi` and `eta = A(phi)/phi^2` have already been formed.
`LogHessianMoments` supplies the more geometric line-moment matrix, but until
now only the complementary-edge branch had a fraction-field adapter from that
matrix.

This file records the rank-three analogue.  It is purely algebraic and mirrors
the already-green complementary theorem:

    det(lineMomentHessian) = 0
        -> det(rankThreeLogHessianCore) = 0
        -> RankThreeFractionCoreDetZero.

The only nonvanishing hypothesis is `phi != 0`, needed to divide by the zeroth
moment in the fraction field.  No target-denominator hypothesis is used.
-/

namespace HC4.Polynomial

noncomputable section

/-- Moment-level rank-three determinant equation in the fraction field of
`K[X]`. -/
def RankThreeFractionMomentDetZero
    {K : Type*} [Field K]
    (phi : Polynomial K)
    (v2 v3 v4 w1 w2 w3 w4 : K) : Prop :=
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let S0 := ι phi
  let S1 := ι (eulerDerivative phi)
  let S2 := ι (eulerDerivative (eulerDerivative phi))
  (lineMomentHessian
      (rankThreeLogBaseExponent
        (ι (Polynomial.C v2))
        (ι (Polynomial.C v3))
        (ι (Polynomial.C v4)))
      (rankThreeLogDirection
        (ι (Polynomial.C w1))
        (ι (Polynomial.C w2))
        (ι (Polynomial.C w3))
        (ι (Polynomial.C w4)))
      S0 S1 S2).det = 0

/-- **Moment-to-fraction rank-three bridge.**
A zero determinant for the honest first three coefficient moments gives the
exact substituted rank-three logarithmic-core determinant used by the mature
rational-rigidity stack. -/
theorem rankThree_fraction_core_det_zero_of_moment_det_zero
    {K : Type*} [Field K]
    {phi : Polynomial K}
    {v2 v3 v4 w1 w2 w3 w4 : K}
    (hphi : phi ≠ 0)
    (hdet : RankThreeFractionMomentDetZero
      phi v2 v3 v4 w1 w2 w3 w4) :
    RankThreeFractionCoreDetZero
      phi v2 v3 v4 w1 w2 w3 w4 := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  let S0 : F := ι phi
  let S1 : F := ι (eulerDerivative phi)
  let S2 : F := ι (eulerDerivative (eulerDerivative phi))

  have hS0 : S0 ≠ 0 := by
    dsimp [S0]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr hphi

  have hmoment :
      (lineMomentHessian
        (rankThreeLogBaseExponent
          (ι (Polynomial.C v2))
          (ι (Polynomial.C v3))
          (ι (Polynomial.C v4)))
        (rankThreeLogDirection
          (ι (Polynomial.C w1))
          (ι (Polynomial.C w2))
          (ι (Polynomial.C w3))
          (ι (Polynomial.C w4)))
        S0 S1 S2).det = 0 := by
    simpa [RankThreeFractionMomentDetZero, F, ι, S0, S1, S2] using hdet

  have hcore :=
    rankThree_core_det_zero_of_lineMoment_det_zero
      (K := F)
      (v2 := ι (Polynomial.C v2))
      (v3 := ι (Polynomial.C v3))
      (v4 := ι (Polynomial.C v4))
      (w1 := ι (Polynomial.C w1))
      (w2 := ι (Polynomial.C w2))
      (w3 := ι (Polynomial.C w3))
      (w4 := ι (Polynomial.C w4))
      (S0 := S0) (S1 := S1) (S2 := S2)
      hS0 hmoment

  have hA :
      ι (logarithmicEtaNumerator phi) = S2 * S0 - S1^2 := by
    dsimp [S0, S1, S2]
    simp [logarithmicEtaNumerator, map_sub, map_mul, map_pow]

  unfold RankThreeFractionCoreDetZero
  simpa [F, ι, S0, S1, S2, hA] using hcore

end

end HC4.Polynomial
