import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# A18.4.40: zero determinant clock already contains transverse rank-two geometry

A raw Hessian clock of zero is not a terminal contradiction: it is exactly the
unit-Hessian-determinant HC4 geometry.  The historical A17.9 assembly left this
state by a transverse Rees construction and then changed the finite repair tag
without retaining a rank witness.

There is a direct source-honest replacement.  Write the genuine symmetric
family Hessian as

    [ a  b  p  q ]
    [ b  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ].

If the three principal `2 x 2` minors of the transverse block and the cross
minor `d*y-r*s` all vanish, a division-free four-block identity forces the
complete `4 x 4` determinant to vanish.  At raw defect zero that determinant
is the unit polynomial, a contradiction.  Hence the actual family already
contains a nonzero transverse `2 x 2` Hessian minor.

Only after storing that literal minor do we attach the canonical rank-one to
rank-two repair transition.  The target changes no polynomial-family datum and
is therefore a genuine same-scale global-key decrease justified by retained
geometry.  No Rees re-entry, homogeneity hypothesis, or repair-only shortcut
is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u v

variable {K : Type u} [Field K] [CharZero K]

/-- Four transverse rank-one relations already force the full determinant of
a symmetric four-block to vanish.

The proof is division-free.  If `d = 0`, the first two square relations kill
`r,s` and the third relation kills the remaining determinant.  If `d != 0`,
we multiply by `d^2`, use the three relations through the `d` pivot, and
cancel the nonzero square. -/
theorem determinantCore_eq_zero_of_transverse_rankOne
    {R : Type v} [CommRing R] [IsDomain R]
    (H : GeneralFourBlock R)
    (hdx : H.d * H.x - H.r * H.r = 0)
    (hdz : H.d * H.z - H.s * H.s = 0)
    (hxz : H.x * H.z - H.y * H.y = 0)
    (hdy : H.d * H.y - H.r * H.s = 0) :
    H.determinantCore = 0 := by
  by_cases hd : H.d = 0
  · have hr2 : H.r * H.r = 0 := by
      simpa [hd] using hdx
    have hs2 : H.s * H.s = 0 := by
      simpa [hd] using hdz
    have hr : H.r = 0 := by
      rcases mul_eq_zero.mp hr2 with h | h <;> exact h
    have hs : H.s = 0 := by
      rcases mul_eq_zero.mp hs2 with h | h <;> exact h
    unfold GeneralFourBlock.determinantCore
    rw [hd, hr, hs]
    linear_combination -(H.b * H.b) * hxz
  · have hd2 : H.d * H.d ≠ 0 := mul_ne_zero hd hd
    have hmul : H.d * H.d * H.determinantCore = 0 := by
      unfold GeneralFourBlock.determinantCore
      linear_combination
        (H.a * H.d ^ 2 * H.z - H.a * H.d * H.s ^ 2 -
          H.b ^ 2 * H.d * H.z + 2 * H.b * H.d * H.q * H.s -
          H.d ^ 2 * H.q ^ 2) * hdx +
        (-H.a * H.d ^ 2 * H.y + H.a * H.d * H.r * H.s +
          H.b ^ 2 * H.d * H.y + H.b ^ 2 * H.r * H.s -
          2 * H.b * H.d * H.p * H.s - 2 * H.b * H.d * H.q * H.r +
          2 * H.d ^ 2 * H.p * H.q) * hdy +
        (-H.b ^ 2 * H.r ^ 2 + 2 * H.b * H.d * H.p * H.r -
          H.d ^ 2 * H.p ^ 2) * hdz
    have hmul' : (H.d * H.d) * H.determinantCore = 0 := by
      simpa [mul_assoc] using hmul
    exact (mul_eq_zero.mp hmul').resolve_left hd2

/-- The honest family Hessian of one scale-aware restart state, packaged as a
symmetric four-block over the original polynomial coefficient ring. -/
noncomputable def scaleAwareFamilyHessianFourBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  GeneralFourBlock.ofSymmetricMatrix (HC4.Polynomial.hessian s.family)

/-- Displaying the scale-aware family four-block recovers the literal Hessian
matrix. -/
theorem scaleAwareFamilyHessianFourBlock_matrix
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareFamilyHessianFourBlock s).matrix =
      HC4.Polynomial.hessian s.family := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  change
    MvPolynomial.pderiv j (MvPolynomial.pderiv i s.family) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j s.family)
  rw [pderiv_comm_commRing]

/-- The four-block determinant is the state's exact raw Hessian clock. -/
theorem scaleAwareFamilyHessianFourBlock_determinantCore
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareFamilyHessianFourBlock s).determinantCore =
      MvPolynomial.C (Polynomial.X ^ s.rawDefect) := by
  rw [← GeneralFourBlock.matrix_det]
  rw [scaleAwareFamilyHessianFourBlock_matrix]
  exact s.hessianDefect

/-- Concrete transverse `2 x 2` Hessian geometry present in every raw-defect
zero state.  The four constructors are literal minors of the actual family
Hessian, not a numerical repair label. -/
inductive AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | minor12
      (hne :
        let H := scaleAwareFamilyHessianFourBlock s
        H.d * H.x - H.r * H.r ≠ 0)
  | minor13
      (hne :
        let H := scaleAwareFamilyHessianFourBlock s
        H.d * H.z - H.s * H.s ≠ 0)
  | minor23
      (hne :
        let H := scaleAwareFamilyHessianFourBlock s
        H.x * H.z - H.y * H.y ≠ 0)
  | cross123
      (hne :
        let H := scaleAwareFamilyHessianFourBlock s
        H.d * H.y - H.r * H.s ≠ 0)

/-- **Unit Hessian determinant forces transverse rank-two geometry.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_rankTwoGeometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry s := by
  let H := scaleAwareFamilyHessianFourBlock s
  by_cases h12 : H.d * H.x - H.r * H.r = 0
  · by_cases h13 : H.d * H.z - H.s * H.s = 0
    · by_cases h23 : H.x * H.z - H.y * H.y = 0
      · by_cases hcross : H.d * H.y - H.r * H.s = 0
        · have hdet0 : H.determinantCore = 0 :=
            determinantCore_eq_zero_of_transverse_rankOne H
              h12 h13 h23 hcross
          have hdet1 : H.determinantCore = 1 := by
            rw [show H = scaleAwareFamilyHessianFourBlock s by rfl,
              scaleAwareFamilyHessianFourBlock_determinantCore, hzero]
            simp
          rw [hdet1] at hdet0
          exact (one_ne_zero hdet0).elim
        · exact .cross123 (by simpa [H] using hcross)
      · exact .minor23 (by simpa [H] using h23)
    · exact .minor13 (by simpa [H] using h13)
  · exact .minor12 (by simpa [H] using h12)

/-- Geometry-carrying rank promotion for the zero-clock endpoint.  The target
is literally the same family/section/scale with only the finite active-rank
bookkeeping advanced, and the nonzero transverse minor is retained beside the
transition. -/
structure AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  source_zero : s.rawDefect = 0
  geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry s
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq : target = s.withRepairOnly (rankTwoRepairState complexity)
  sameScaleProgress : CertifiedSameScaleEpisodeProgress RR target s
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- Attach the finite rank promotion only after the unit-determinant source has
supplied an actual nonzero transverse Hessian minor. -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_globalRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hzero : s.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalGlobalZeroDefectRankTwoProgress
      RR s complexity := by
  let G := s.zeroDefect_rankTwoGeometry hzero
  let target := s.withRepairOnly (rankTwoRepairState complexity)
  have hrepair : RepairProgress s.repair (rankTwoRepairState complexity) := by
    simpa [hsrepair] using rankOne_to_rankTwo_repairProgress complexity
  have hsame : CertifiedSameScaleEpisodeProgress RR target s := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    exact (certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_repairProgress
      (K := K) (t := target) (s := s) rfl hrepair).progress
  exact {
    source_zero := hzero
    geometry := G
    target := target
    target_eq := rfl
    sameScaleProgress := hsame
    globalProgress := hglobal
  }

end

end HC4.Valuation