import HC4.Valuation.QuadraticFirstLayerPolynomialRankTwo
import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# Fixed transverse principal pivots on the actual quadratic first layer

The reachable quadratic E3 first-positive layer has one of six nonzero
transverse 2x2 Hessian minors. Three can be mixed rather than principal.
A mixed minor cannot be passed unchanged to the existing principal-active
Schur interfaces.

For a symmetric 3x3 block, this file proves a finite principalisation:
one of the three coordinate 2-planes, or one of the three planes obtained
by replacing one transverse basis vector by the sum of two, has a
nondegenerate restricted quadratic form. The three non-coordinate planes
are realised by determinant-one transverse source shears of coefficient 1.

The conclusion is attached to the ACTUAL marked-axis first-positive
coefficient, not an auxiliary fabricated quadratic source. This provides
a concrete finite pivot for a subsequent source-honest Schur chart;
it does not assert terminal closure, or identify a positive Rees clock
with the original zero-defect terminal.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Six ordinary / one-shear principal pivots for the symmetric block
    [a b c; b d e; c e f].

The final three expressions are the principal determinants on
  span(e1+e2,e3), span(e1+e3,e2), span(e2+e3,e1).
All shears fix the marked longitudinal axis, and no generic choice of
parameters or algebraic closure is required. -/
theorem symmetricThreeBlock_sixMinors_fixedPrincipalPivots
    (a b c d e f : K)
    (hminor :
      d * f - e * e ≠ 0 ∨
      b * f - c * e ≠ 0 ∨
      b * e - c * d ≠ 0 ∨
      a * f - c * c ≠ 0 ∨
      a * e - b * c ≠ 0 ∨
      a * d - b * b ≠ 0) :
    d * f - e * e ≠ 0 ∨
    a * f - c * c ≠ 0 ∨
    a * d - b * b ≠ 0 ∨
    (a + 2 * b + d) * f - (c + e) * (c + e) ≠ 0 ∨
    (a + 2 * c + f) * d - (b + e) * (b + e) ≠ 0 ∨
    (d + 2 * e + f) * a - (b + c) * (b + c) ≠ 0 := by
  rcases hminor with h | h | h | h | h | h
  · exact Or.inl h
  · by_cases hac : a * f - c * c = 0
    · by_cases hdf : d * f - e * e = 0
      · have hp :
          (a + 2 * b + d) * f - (c + e) * (c + e) ≠ 0 := by
          have hid :
              (a + 2 * b + d) * f - (c + e) * (c + e) =
                (2 : K) * (b * f - c * e) := by
            calc
              _ = (a * f - c * c) + (d * f - e * e) +
                  2 * (b * f - c * e) := by ring
              _ = (2 : K) * (b * f - c * e) := by
                    rw [hac, hdf]
                    ring
          rw [hid]
          exact mul_ne_zero (by norm_num) h
        exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      · exact Or.inl hdf
    · exact Or.inr (Or.inl hac)
  · by_cases had : a * d - b * b = 0
    · by_cases hdf : d * f - e * e = 0
      · have hp :
          (a + 2 * c + f) * d - (b + e) * (b + e) ≠ 0 := by
          have hid :
              (a + 2 * c + f) * d - (b + e) * (b + e) =
                (-2 : K) * (b * e - c * d) := by
            calc
              _ = (a * d - b * b) + (d * f - e * e) -
                  2 * (b * e - c * d) := by ring
              _ = (-2 : K) * (b * e - c * d) := by
                    rw [had, hdf]
                    ring
          rw [hid]
          exact mul_ne_zero (by norm_num) h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
      · exact Or.inl hdf
    · exact Or.inr (Or.inr (Or.inl had))
  · exact Or.inr (Or.inl h)
  · by_cases had : a * d - b * b = 0
    · by_cases hac : a * f - c * c = 0
      · have hp :
          (d + 2 * e + f) * a - (b + c) * (b + c) ≠ 0 := by
          have hid :
              (d + 2 * e + f) * a - (b + c) * (b + c) =
                (2 : K) * (a * e - b * c) := by
            calc
              _ = (a * d - b * b) + (a * f - c * c) +
                  2 * (a * e - b * c) := by ring
              _ = (2 : K) * (a * e - b * c) := by
                    rw [had, hac]
                    ring
          rw [hid]
          exact mul_ne_zero (by norm_num) h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))
      · exact Or.inr (Or.inl hac)
    · exact Or.inr (Or.inr (Or.inl had))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Turn the *actual* first-layer transverse origin-minor alternatives into
one of six explicit nonzero principal determinants. This is a principal
Schur-pivot certificate, not yet a polynomial endpoint producer. -/
theorem quadraticFirstLayer_fixedTransversePrincipalPivot
    (G : MvPolynomial (Fin 4) K)
    (hminor :
      let H := quadraticFamilyHessianMatrix G
      H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
      H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
      H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
      H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
      H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
      H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0) :
    let H := quadraticFamilyHessianMatrix G
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 ∨
    (H 1 1 + 2 * H 1 2 + H 2 2) * H 3 3 -
      (H 1 3 + H 2 3) * (H 1 3 + H 2 3) ≠ 0 ∨
    (H 1 1 + 2 * H 1 3 + H 3 3) * H 2 2 -
      (H 1 2 + H 2 3) * (H 1 2 + H 2 3) ≠ 0 ∨
    (H 2 2 + 2 * H 2 3 + H 3 3) * H 1 1 -
      (H 1 2 + H 1 3) * (H 1 2 + H 1 3) ≠ 0 := by
  dsimp only at hminor ⊢
  exact symmetricThreeBlock_sixMinors_fixedPrincipalPivots
    (quadraticFamilyHessianMatrix G 1 1)
    (quadraticFamilyHessianMatrix G 1 2)
    (quadraticFamilyHessianMatrix G 1 3)
    (quadraticFamilyHessianMatrix G 2 2)
    (quadraticFamilyHessianMatrix G 2 3)
    (quadraticFamilyHessianMatrix G 3 3) hminor

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable [IsAlgClosed K]
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- A *reachable*, source-honest finite principal Schur-pivot alternative
on the first actual quadratic layer. This retains the actual family
parameter order and does not make an auxiliary clock a terminal step. -/
theorem pureLongitudinal_quadraticFirstActualLayer_fixedPrincipalPivot
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let G := familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder
    let H := quadraticFamilyHessianMatrix G
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 ∨
    (H 1 1 + 2 * H 1 2 + H 2 2) * H 3 3 -
      (H 1 3 + H 2 3) * (H 1 3 + H 2 3) ≠ 0 ∨
    (H 1 1 + 2 * H 1 3 + H 3 3) * H 2 2 -
      (H 1 2 + H 2 3) * (H 1 2 + H 2 3) ≠ 0 ∨
    (H 2 2 + 2 * H 2 3 + H 3 3) * H 1 1 -
      (H 1 2 + H 1 3) * (H 1 2 + H 1 3) ≠ 0 := by
  have hminor :=
    P.pureLongitudinal_quadraticFirstActualLayer_transverseRankTwo
      coefficient_ne_zero topFace_eq hr
  exact quadraticFirstLayer_fixedTransversePrincipalPivot _ hminor

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
