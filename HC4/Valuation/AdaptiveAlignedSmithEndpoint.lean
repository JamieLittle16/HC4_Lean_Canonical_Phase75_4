import HC4.Valuation.ZeroLeftDepartureFrontier
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Mixed-degree adaptive aligned-Smith endpoint

The older high-level aligned-Smith dispatcher was packaged for a globally
homogeneous source.  The lower-level first-stop and primitive-endpoint
machinery is more general: it only needs the actual polynomial family,
its zero-left exact collision, and its Hessian clock.

This file packages that lower-level machinery in the form needed by the
adaptive mixed-degree programme.

Starting from

    0 ~ b(tau),

one finite aligned-Smith macro-step produces exactly one of:

* a symmetric-minimal transformed family whose exact collision is still
  literally zero-left and whose right special point is still `e0`; or
* a genuine right-section boundary, together with the actual transformed
  family, exact Hessian clock, nonlinear degree cap, and exact collision.

No ordinary source homogeneity assumption is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Degree-cap transport -/

/-- Common parameter-factor extraction introduces no new source monomials,
so it preserves every nonlinear source-degree ceiling. -/
theorem nonlinearDegreeBound_commonParameterFactor
    (degreeCap n : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound degreeCap P)
    (hdiv : HasCommonParameterFactor n P) :
    NonlinearDegreeBound degreeCap
      (commonParameterFactorFamily n P hdiv) := by
  apply nonlinearDegreeBound_of_support_subset hP
  exact support_commonParameterFactorFamily_subset n P hdiv

/-- The genuine aligned first-wall family preserves the nonlinear
source-degree ceiling. -/
theorem nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b)
    (hP : NonlinearDegreeBound degreeCap P) :
    NonlinearDegreeBound degreeCap
      (alignedSmithGenuineFirstWallFamily
        (K := K) P a b hwall) := by
  let N := alignedSmithGenuineFirstWall P a b hwall
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  have hram :
      NonlinearDegreeBound degreeCap Pram := by
    dsimp [Pram]
    exact
      nonlinearDegreeBound_parameterRamification
        degreeCap alignedSmithRamificationIndex P hP
  have hsmith :
      NonlinearDegreeBound degreeCap
        (integralSmithConformalFamily
          (2 * N) (2 * N) Pram
          (alignedSmithGenuineFirstWall_integralCoefficients
            P a b hwall)) := by
    exact
      nonlinearDegreeBound_integralSmithConformal
        degreeCap (2 * N) (2 * N) Pram hram
        (alignedSmithGenuineFirstWall_integralCoefficients
          P a b hwall)
  simpa [alignedSmithGenuineFirstWallFamily, N, Pram] using hsmith

/-- The no-wall primitive aligned-Smith family preserves the nonlinear
source-degree ceiling. -/
theorem nonlinearDegreeBound_noWallPrimitiveSmithFamily
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall P a b)
    (hP : NonlinearDegreeBound degreeCap P) :
    NonlinearDegreeBound degreeCap
      (noWallPrimitiveSmithFamily
        P a b Delta hdef hnone) := by
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P a b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let N := noWallPrimitiveSmithStep m
  let hlegal :
      ∀ d ∈ P.support,
        0 ≤
          alignedSmithCoefficientValue
            (smithFamilyCoefficientOrder P d)
            N
            (smithSeparatorDelta 1 1
              (smithAxisProjection d)) :=
    fun d hd =>
      noWallPrimitiveSmithStep_coefficient_nonnegative
        P a b hnone m hd
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let hsmith :=
    alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) P N hlegal
  let Q :=
    integralSmithConformalFamily
      (2 * N) (2 * N) Pram hsmith
  let hcommon :=
    noWallPrimitiveSmithStep_commonFactor
      P a b Delta hdef hnone hne
  have hPram :
      NonlinearDegreeBound degreeCap Pram := by
    dsimp [Pram]
    exact
      nonlinearDegreeBound_parameterRamification
        degreeCap alignedSmithRamificationIndex P hP
  have hQ :
      NonlinearDegreeBound degreeCap Q := by
    dsimp [Q]
    exact
      nonlinearDegreeBound_integralSmithConformal
        degreeCap (2 * N) (2 * N) Pram hPram hsmith
  have hout :
      NonlinearDegreeBound degreeCap
        (commonParameterFactorFamily
          (alignedSmithRamificationIndex * m)
          Q hcommon) :=
    nonlinearDegreeBound_commonParameterFactor
      degreeCap (alignedSmithRamificationIndex * m)
      Q hQ hcommon
  simpa [noWallPrimitiveSmithFamily,
    hne, m, N, hlegal, Pram, hsmith, Q, hcommon] using hout

/-! ## Dispatcher-facing endpoint data -/

/-- A mixed-degree aligned-Smith endpoint at which the transformed special
fibre is already symmetric-minimal, while the collision remains literally
`0 ~ e0` at the special parameter. -/
structure AdaptiveAlignedSmithMinimalEndpoint
    (degreeCap : ℕ) where
  defect : ℕ
  family : MvPolynomial (Fin 4) (Polynomial K)
  movingSection : Fin 4 → Polynomial K
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) family defect
  nonlinearDegreeBound :
    NonlinearDegreeBound degreeCap family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (zeroPolynomialSection (K := K)) movingSection
  sectionSpecial :
    polynomialSectionSpecialPoint movingSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  symmetricMinimal :
    IsSymmetricSmithPoleMinimal
      (smithProjectedSupport
        (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber family))
      0
      (fun _ => (0 : ℤ))

/-- A genuine aligned section boundary retaining the actual transformed
family, clock, degree cap, and zero-left exact collision.

The right marked section is intentionally not required to remain at `e0`:
the point of this branch is precisely that a transverse special coordinate
has become nonzero. -/
structure AdaptiveAlignedSmithSectionBoundaryEndpoint
    (degreeCap Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) where
  hwall :
    HasAlignedSmithGenuineWall
      P (zeroPolynomialSection (K := K)) b
  boundary :
    HasAlignedSmithSectionBoundary
      P (zeroPolynomialSection (K := K)) b hwall
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (alignedSmithGenuineFirstWallFamily
        P (zeroPolynomialSection (K := K)) b hwall)
      (alignedSmithRamificationIndex * Delta)
  nonlinearDegreeBound :
    NonlinearDegreeBound degreeCap
      (alignedSmithGenuineFirstWallFamily
        P (zeroPolynomialSection (K := K)) b hwall)
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      (alignedSmithGenuineFirstWallFamily
        P (zeroPolynomialSection (K := K)) b hwall)
      (zeroPolynomialSection (K := K))
      (alignedSmithGenuineFirstWallSectionRight
        P (zeroPolynomialSection (K := K)) b hwall)

/-! ## Mixed-degree aligned endpoint theorem -/

/-- **One-shot mixed-degree aligned-Smith endpoint.**

No ordinary source homogeneity is assumed.

From an exact zero-left collision with canonical right special point, the
finite aligned Smith search either:

* reaches a symmetric-minimal transformed family retaining the canonical
  zero-left collision; or
* reaches an actual right-section boundary, retaining the transformed
  family, exact clock, degree cap, and collision.

Thus the nonminimal Smith direction is consumed as one finite macro-step
rather than recursively re-ramifying by the fixed strict-Smith step. -/
theorem adaptiveAlignedSmithEndpoint_zeroLeft
    [CharZero K]
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hdegree :
      NonlinearDegreeBound degreeCap P)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    Nonempty
        (AdaptiveAlignedSmithMinimalEndpoint
          (K := K) degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K) degreeCap Delta P b) := by
  classical
  by_cases hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b
  · let N :=
      alignedSmithGenuineFirstWall
        P (zeroPolynomialSection (K := K)) b hwall
    by_cases hB : N ∈ alignedSmithSectionWalls b
    · right
      have hcoord :=
        genuineRightSectionWall_exposes_nonzero_specialCoordinate
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hB)
      have hboundary :
          HasAlignedSmithSectionBoundary
            P (zeroPolynomialSection (K := K)) b hwall := by
        right
        rcases hcoord with ⟨i, hi0, hne⟩
        exact
          ⟨i, hi0, by simpa [N] using hB, hne⟩
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b
          hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K)
              P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      exact
        ⟨{
          hwall := hwall
          boundary := hboundary
          hessianDefect := hwallDef
          nonlinearDegreeBound := hwallDegree
          exactCollision := hwallColl
        }⟩
    · left
      have hcases :=
        alignedSmithGenuineFirstWall_cases
          P (zeroPolynomialSection (K := K)) b hwall
      have hcoeff :
          N ∈ alignedSmithCoefficientWalls P := by
        rcases hcases with hcoeff | hA | hBright
        · simpa [N] using hcoeff
        · have hnotA :
              N ∉
                alignedSmithSectionWalls
                  (zeroPolynomialSection (K := K)) :=
            not_mem_alignedSmithSectionWalls_zeroPolynomialSection
              (K := K) N
          exact False.elim (hnotA (by simpa [N] using hA))
        · exact False.elim (hB (by simpa [N] using hBright))
      have hnotA :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls
              (zeroPolynomialSection (K := K)) := by
        exact
          not_mem_alignedSmithSectionWalls_zeroPolynomialSection
            (K := K)
            (alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall)
      have hnotB :
          alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) b hwall ∉
            alignedSmithSectionWalls b := by
        simpa [N] using hB
      have ha :
          polynomialSectionSpecialPoint
              (zeroPolynomialSection (K := K)) =
            (fun _ => (0 : K)) :=
        polynomialSectionSpecialPoint_zeroPolynomialSection
      have hpoints :=
        pureCoefficientWall_specialPoints_canonical
          P (zeroPolynomialSection (K := K)) b
          hwall hnotA hnotB ha hb
      have hwallDef :
          HasPolynomialFamilyHessianDefect
            (K := K)
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (alignedSmithRamificationIndex * Delta) :=
        alignedSmithGenuineFirstWall_preservesHessianDefect
          P (zeroPolynomialSection (K := K)) b
          hwall Delta hdef
      have hwallDegree :
          NonlinearDegreeBound degreeCap
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall) :=
        nonlinearDegreeBound_alignedSmithGenuineFirstWallFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b hwall hdegree
      have hwallCollRaw :=
        alignedSmithGenuineFirstWall_preservesExactCollision
          P (zeroPolynomialSection (K := K)) b hwall hcoll
      have hleft :
          alignedSmithGenuineFirstWallSectionLeft
              (K := K)
              P (zeroPolynomialSection (K := K)) b hwall =
            zeroPolynomialSection (K := K) :=
        alignedSmithGenuineFirstWallSectionLeft_zero
          (K := K) P b hwall
      have hwallColl :
          HasPolynomialFamilyExactGradientCollision
            (alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall)
            (zeroPolynomialSection (K := K))
            (alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall) := by
        simpa only [hleft] using hwallCollRaw
      have hminimal :
          IsSymmetricSmithPoleMinimal
            (smithProjectedSupport
              (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber
                (alignedSmithGenuineFirstWallFamily
                  P (zeroPolynomialSection (K := K)) b hwall)))
            0
            (fun _ => (0 : ℤ)) :=
        genuineCoefficientWall_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b hwall
          (by simpa [N] using hcoeff)
      exact
        ⟨{
          defect := alignedSmithRamificationIndex * Delta
          family :=
            alignedSmithGenuineFirstWallFamily
              P (zeroPolynomialSection (K := K)) b hwall
          movingSection :=
            alignedSmithGenuineFirstWallSectionRight
              P (zeroPolynomialSection (K := K)) b hwall
          hessianDefect := hwallDef
          nonlinearDegreeBound := hwallDegree
          exactCollision := hwallColl
          sectionSpecial := hpoints.2
          symmetricMinimal := hminimal
        }⟩
  · left
    rcases
        noWallPrimitiveSmithFamily_zeroLeft_canonicalCollision
          P b Delta hdef hwall hcoll hb with
      ⟨b', hcoll', hb'⟩
    let Q :=
      noWallPrimitiveSmithFamily
        P (zeroPolynomialSection (K := K)) b
        Delta hdef hwall
    let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b
        Delta hdef hwall
    let m := minimalZeroSmithParameterOrder P hne
    let Delta' :=
      alignedSmithRamificationIndex * Delta -
        4 * (alignedSmithRamificationIndex * m)
    have hQdef :
        HasPolynomialFamilyHessianDefect
          (K := K) Q Delta' := by
      dsimp [Q, Delta', hne, m]
      exact
        noWallPrimitiveSmithFamily_hasHessianDefect
          P (zeroPolynomialSection (K := K)) b
          Delta hdef hwall
    have hQdegree :
        NonlinearDegreeBound degreeCap Q := by
      dsimp [Q]
      exact
        nonlinearDegreeBound_noWallPrimitiveSmithFamily
          (K := K) degreeCap P
          (zeroPolynomialSection (K := K)) b
          Delta hdef hwall hdegree
    have hminimal :
        IsSymmetricSmithPoleMinimal
          (smithProjectedSupport
            (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber Q))
          0
          (fun _ => (0 : ℤ)) := by
      dsimp [Q]
      exact
        noWallPrimitiveSmithFamily_specialFiber_symmetricMinimal
          P (zeroPolynomialSection (K := K)) b
          Delta hdef hwall
    exact
      ⟨{
        defect := Delta'
        family := Q
        movingSection := b'
        hessianDefect := hQdef
        nonlinearDegreeBound := hQdegree
        exactCollision := hcoll'
        sectionSpecial := hb'
        symmetricMinimal := hminimal
      }⟩

end

end HC4.Valuation
