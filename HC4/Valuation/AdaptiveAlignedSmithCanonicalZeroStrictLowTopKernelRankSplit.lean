import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoResolvedOpening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import Mathlib.Tactic

/-!
# A19.55 top-kernel Hessian-rank split

After the source-honest codimension-two first-opening analysis, the only
separate local branch is the case in which the actual maximal ordinary top
face already has a literal coordinate kernel.

That homogeneous top face admits an exact finite split:

* either one of its Hessian `2 x 2` minors is nonzero, giving rank-two geometry
  directly on the honest top face; or
* every Hessian `2 x 2` minor vanishes.  The existing four-variable
  homogeneous rank-one classification then forces the whole top face to be a
  scalar multiple of one linear form to the selected top degree.  The stored
  coordinate kernel forces the coefficient of that kernel coordinate in the
  linear form to vanish.

No lower layer, auxiliary Rees clock, or repair tag is used in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Concrete rank-two Hessian geometry directly on the actual A19 top face. -/
def TopFaceHessianRankTwoWitness
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop :=
  ∃ i j k l : Fin 4,
    HC4.Polynomial.hessian T.topFace.face i j *
          HC4.Polynomial.hessian T.topFace.face k l -
        HC4.Polynomial.hessian T.topFace.face i l *
          HC4.Polynomial.hessian T.topFace.face k j ≠ 0

/-- Exact rank-one homogeneous normal form retaining the actual coordinate
kernel of the A19 top face. -/
structure TopFaceLinearPowerKernelData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (kernelCoordinate : Fin 4) : Type (u + 1) where
  coefficient : K
  ratio : Fin 4 → K
  eq_power :
    T.topFace.face =
      MvPolynomial.C coefficient *
        (gradientRatioLinearForm ratio) ^ T.topFace.degree
  kernel_ratio_zero : ratio kernelCoordinate = 0

/-- **A19.55 top-kernel rank split.**

A literal coordinate kernel on the honest maximal top face either coexists
with a nonzero Hessian `2 x 2` minor, or the complete top face is a linear
power whose linear form omits that kernel coordinate. -/
theorem topKernel_rankTwo_or_linearPower
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (kernelCoordinate : Fin 4)
    (hkernel :
      MvPolynomial.pderiv kernelCoordinate T.topFace.face = 0) :
    T.TopFaceHessianRankTwoWitness ∨
      Nonempty (T.TopFaceLinearPowerKernelData kernelCoordinate) := by
  by_cases htwo : T.TopFaceHessianRankTwoWitness
  · exact Or.inl htwo
  · right
    have hall :
        ∀ i j k l : Fin 4,
          HC4.Polynomial.hessian T.topFace.face i j *
                HC4.Polynomial.hessian T.topFace.face k l -
              HC4.Polynomial.hessian T.topFace.face i l *
                HC4.Polynomial.hessian T.topFace.face k j = 0 := by
      intro i j k l
      by_contra hne
      exact htwo ⟨i, j, k, l, hne⟩
    rcases rankOneHomogeneousLogGradientData_of_allMinors
        T.topFace.face
        T.topFace.degree
        T.topFace.face_isHomogeneous
        T.topFace.face_ne_zero
        (by omega : 2 ≤ T.topFace.degree)
        hall with ⟨G⟩
    rcases rankOneHomogeneousLogGradientData_four_global G with ⟨c, hc⟩
    rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
        T.topFace.degree
        T.topFace.face
        T.topFace.face_isHomogeneous
        (by omega : 0 < T.topFace.degree)
        G.pivot G.pivot_ne_zero c hc with ⟨a, ha⟩

    have ha_ne : a ≠ 0 := by
      intro ha0
      apply T.topFace.face_ne_zero
      rw [ha, ha0]
      simp
    have hL_ne : gradientRatioLinearForm c ≠ 0 := by
      intro hL0
      apply T.topFace.face_ne_zero
      rw [ha, hL0]
      simp [show 0 < T.topFace.degree by omega]
    have hmK : (T.topFace.degree : K) ≠ 0 := by
      exact_mod_cast (show T.topFace.degree ≠ 0 by omega)
    have hpow :
        (gradientRatioLinearForm c) ^ (T.topFace.degree - 1) ≠ 0 :=
      pow_ne_zero _ hL_ne
    have hscalarZero :
        (T.topFace.degree : K) * c kernelCoordinate = 0 := by
      have hderiv :
          MvPolynomial.C a *
              MvPolynomial.C
                ((T.topFace.degree : K) * c kernelCoordinate) *
              (gradientRatioLinearForm c) ^ (T.topFace.degree - 1) = 0 := by
        calc
          MvPolynomial.C a *
                MvPolynomial.C
                  ((T.topFace.degree : K) * c kernelCoordinate) *
                (gradientRatioLinearForm c) ^ (T.topFace.degree - 1) =
              MvPolynomial.pderiv kernelCoordinate
                (MvPolynomial.C a *
                  (gradientRatioLinearForm c) ^ T.topFace.degree) := by
                    rw [MvPolynomial.pderiv_C_mul]
                    have hmrepr :
                        T.topFace.degree =
                          (T.topFace.degree - 1) + 1 := by omega
                    conv_rhs =>
                      rhs
                      rw [hmrepr]
                    rw [pderiv_gradientRatioLinearForm_pow_succ]
                    congr 2
                    push_cast
                    ring
          _ = MvPolynomial.pderiv kernelCoordinate T.topFace.face := by
                rw [ha]
          _ = 0 := hkernel
      have hCa : (MvPolynomial.C a : MvPolynomial (Fin 4) K) ≠ 0 := by
        simpa using ha_ne
      have hrest :
          MvPolynomial.C
                ((T.topFace.degree : K) * c kernelCoordinate) *
              (gradientRatioLinearForm c) ^ (T.topFace.degree - 1) = 0 :=
        (mul_eq_zero.mp hderiv).resolve_left hCa
      have hCscalar :
          MvPolynomial.C
              ((T.topFace.degree : K) * c kernelCoordinate) = 0 :=
        (mul_eq_zero.mp hrest).resolve_right hpow
      simpa using hCscalar
    have hck : c kernelCoordinate = 0 :=
      (mul_eq_zero.mp hscalarZero).resolve_left hmK
    exact ⟨{
      coefficient := a
      ratio := c
      eq_power := ha
      kernel_ratio_zero := hck
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
