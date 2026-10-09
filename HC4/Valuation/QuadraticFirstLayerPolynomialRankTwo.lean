import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureQuadraticFirstLayerRankTwo
import Mathlib.Tactic

/-!
# Promote a rank-two origin-Hessian minor to honest polynomial rank-two geometry

The existing quadratic reverse-Rees argument supplies a nonzero transverse
origin-Hessian 2x2 minor on the actual first marked-axis layer.  Since taking
the source constant coefficient is a ring homomorphism, the corresponding
2x2 minor of the full polynomial-valued Hessian cannot vanish identically.

This is the exact Hessian-polynomial witness expected by the mature rank-two
frontier: it is neither a repair label nor a pointwise substitute.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A nonzero source-origin Hessian minor yields a nonzero polynomial Hessian
minor with exactly the same four indices. -/
theorem polynomialHessianMinor_ne_zero_of_originMinor_ne_zero
    (G : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4)
    (hminor :
      quadraticFamilyHessianMatrix G i j *
          quadraticFamilyHessianMatrix G k l -
        quadraticFamilyHessianMatrix G i l *
          quadraticFamilyHessianMatrix G k j ≠ 0) :
    HC4.Polynomial.hessian G i j *
          HC4.Polynomial.hessian G k l -
        HC4.Polynomial.hessian G i l *
          HC4.Polynomial.hessian G k j ≠ 0 := by
  intro hzero
  have hconst :=
    congrArg
      (fun q : MvPolynomial (Fin 4) K =>
        MvPolynomial.constantCoeff q) hzero
  simp only [map_sub, map_mul, map_zero] at hconst
  change
    quadraticFamilyHessianMatrix G i j *
        quadraticFamilyHessianMatrix G k l -
      quadraticFamilyHessianMatrix G i l *
        quadraticFamilyHessianMatrix G k j = 0 at hconst
  exact hminor hconst

/-- The six independent transverse origin minors give an actual nonzero
polynomial 2x2 Hessian minor, with an explicitly witnessed index quadruple. -/
theorem exists_polynomialHessianRankTwo_of_transverseOriginRankTwo
    (G : MvPolynomial (Fin 4) K)
    (hminor :
      let H := quadraticFamilyHessianMatrix G
      H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
      H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
      H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
      H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
      H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
      H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0) :
    ∃ i j k l : Fin 4,
      HC4.Polynomial.hessian G i j *
          HC4.Polynomial.hessian G k l -
        HC4.Polynomial.hessian G i l *
          HC4.Polynomial.hessian G k j ≠ 0 := by
  let H := quadraticFamilyHessianMatrix G
  have hsym : ∀ i j : Fin 4, H i j = H j i := by
    intro i j
    change
      MvPolynomial.constantCoeff
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i G)) =
        MvPolynomial.constantCoeff
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j G))
    rw [pderiv_comm_commRing]
  dsimp only at hminor
  rcases hminor with h | h | h | h | h | h
  · refine ⟨2, 2, 3, 3, ?_⟩
    apply polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G
    simpa only [hsym 3 2] using h
  · refine ⟨1, 2, 3, 3, ?_⟩
    apply polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G
    simpa only [hsym 3 2] using h
  · refine ⟨1, 2, 2, 3, ?_⟩
    exact polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G _ _ _ _ h
  · refine ⟨1, 1, 3, 3, ?_⟩
    apply polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G
    simpa only [hsym 3 1] using h
  · refine ⟨1, 1, 2, 3, ?_⟩
    apply polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G
    simpa only [hsym 2 1] using h
  · refine ⟨1, 1, 2, 2, ?_⟩
    apply polynomialHessianMinor_ne_zero_of_originMinor_ne_zero G
    simpa only [hsym 2 1] using h

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable [IsAlgClosed K]
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **The actual quadratic first-actual face carries a polynomial Hessian
rank-two witness.**  This can feed the existing homogeneous rank/kernal
opening logic without a new abstract extractor hypothesis. -/
theorem pureLongitudinal_quadraticFirstActualLayer_polynomialRankTwo
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
    ∃ i j k l : Fin 4,
      HC4.Polynomial.hessian G i j *
          HC4.Polynomial.hessian G k l -
        HC4.Polynomial.hessian G i l *
          HC4.Polynomial.hessian G k j ≠ 0 := by
  let G := familyParameterLayer
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstActualLayerOrder
  have hminor :=
    P.pureLongitudinal_quadraticFirstActualLayer_transverseRankTwo
      coefficient_ne_zero topFace_eq hr
  exact exists_polynomialHessianRankTwo_of_transverseOriginRankTwo G hminor

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
