import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisAlignedFreshSquare
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisCanonicalSquareLattice
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisCanonicalSquareGapImpossible
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisPreclosingSourceWitness
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureFirstLayerCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureReverseReesRelevel
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureAuxiliaryMacroStep
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureDegreeCapObstruction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureQuadraticRelevel
import HC4.Valuation.QuadraticAxisReverseReesOriginRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureQuadraticFirstLayerRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRelativeSourceRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureLongitudinalFirstContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution
import HC4.Valuation.CommonParameterFactorRestart
import HC4.Valuation.StrictSmithPostTransformFace
import HC4.Valuation.PrimitiveSmithEndpoint
import HC4.Valuation.StrictSmithFirstContactGeometry

/-!
# E3: exact final-resolution obligations for the top-kernel linear-power seam

The marked-axis E1/E2 analysis and the source-honest C/D analysis have now
been completely compressed.  Every retained linear-power top-kernel packet
reaches exactly one of two represented-source rank-three Hessian events:

* an evaluated nonzero source 3x3 Hessian minor; or
* a nonzero constant 3x3 Hessian minor on an honest exact-active source chart.

Neither event is, by itself, a terminal contradiction.  The only remaining
mathematics is to turn each event into one of the already-permitted
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution`
constructors.

This file records precisely those two extraction obligations and proves the
mechanical E1/E2/E3 assembly around them.  No new final-resolution constructor,
repair label, or terminal endpoint is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The exact two polynomial-level extraction obligations left after the
linear-power E3 source-rank-three collapse. -/
structure TopKernelLinearPowerE3FinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourcePoint :
    P.PositiveTailRepresentedSourceThreeByThreePointGeometry →
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- **Single-obligation E3 extractor.**

At the actual zero-strict-low represented state the raw Hessian clock is
already zero.  Hence the represented state has an exact-active Hessian chart
independently of which branch of the C/D source-rank-three analysis was used,
and every such chart has a nonzero constant 3x3 Hessian minor.

Consequently the evaluated source-point constructor does not create a second
terminal obligation: both E3 constructors may be routed through the same
exact-active constant-minor resolver. -/
structure TopKernelLinearPowerE3ConstantFinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- The single constant-minor resolver supplies the older two-field E3
interface.  In the source-point branch we deliberately do not reconstruct a
second active chart from the evaluated 3x3 minor: raw defect zero already
provides an honest exact-active chart on this same represented source. -/
noncomputable def
    TopKernelLinearPowerE3ConstantFinalResolutionExtractor.toE3Extractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    P.TopKernelLinearPowerE3FinalResolutionExtractor where
  sourcePoint := by
    intro _Q
    rcases
        T.terminal.blocker.presented.zeroDefect_exactActiveFourBlock
          T.presented_zero with
      ⟨A⟩
    rcases P.exactActive_threeByThree_of_presentedZero A with ⟨Q⟩
    exact X.sourceConstant A Q
  sourceConstant := by
    intro A Q
    exact X.sourceConstant A Q

/-- Lossless E3 packet for the pure-longitudinal marked-axis branch.

The earlier marked-aware interface retained only a generic codimension-two
source exponent.  That discarded the rigid geometry which actually creates
this branch.  We now keep the pure top-face identity, the nonzero transverse
kernel direction, the represented codimension-two source exponent, and the
exact physical order of the distinguished pure top coefficient in the
marked-axis first-contact family. -/
structure PureLongitudinalMarkedE3Data
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  coefficient : K
  coefficient_ne_zero : coefficient ≠ 0
  topFace_eq :
    T.topFace.face =
      MvPolynomial.C coefficient *
        (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree
  kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4)
  sourceExponent : Fin 4 →₀ ℕ
  source_mem : sourceExponent ∈ T.representedSpecialFiber.support
  source_boundary : MvExponentOnCodimensionTwoBoundary sourceExponent
  topCoefficientOrder_eq :
    smithFamilyCoefficientOrder
        T.topKernelMarkedAxisFirstContactFamily
        (Finsupp.single (0 : Fin 4) T.topFace.degree) =
      T.topFace.degree
  topCoefficientOrder_pos_lt_defect :
    0 <
        smithFamilyCoefficientOrder
          T.topKernelMarkedAxisFirstContactFamily
          (Finsupp.single (0 : Fin 4) T.topFace.degree) ∧
      smithFamilyCoefficientOrder
          T.topKernelMarkedAxisFirstContactFamily
          (Finsupp.single (0 : Fin 4) T.topFace.degree) <
        4 * T.topFace.degree - 6

/-- Reachable pure-longitudinal E3 geometry includes a concrete
represented-source monomial strictly below maximal ordinary degree.  Its
transverse degree is at least two and its longitudinal exponent is bounded
by the true first positive marked-axis order.  This is the source-level
degree-drop witness; it is not yet a complete restart or terminal proof. -/
theorem PureLongitudinalMarkedE3Data.lowerSourceDegreeWitness
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    ∃ d ∈ T.representedSpecialFiber.support,
      HC4.Polynomial.ordinaryDegree4 d < T.topFace.degree ∧
        2 ≤ d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) ∧
        d (0 : Fin 4) ≤ T.topKernelMarkedAxisFirstActualLayerOrder :=
  P.pureLongitudinal_firstActual_exists_lowerSourceDegree
    D.coefficient_ne_zero D.topFace_eq

/-- Pure-longitudinal E3 retains the *entire* lower singular collision,
not merely the lower source exponent.  The first actual potential is nonzero,
Hessian-singular, strictly below maximal source degree, and carries the same
distinct marked gradient collision at 0 and e₀. -/
theorem PureLongitudinalMarkedE3Data.lowerSingularCollisionPacket
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    let L := familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder
    L ≠ 0 ∧
      HC4.Polynomial.hessianDeterminant L = 0 ∧
      HasExactGradientCollision L
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
      (∀ d ∈ L.support,
        HC4.Polynomial.ordinaryDegree4 d < T.topFace.degree) :=
  P.pureLongitudinal_firstActualLayer_singularCollisionPacket
    D.coefficient_ne_zero D.topFace_eq

/-- The marked-aware pure E3 branch admits a strict **potential-family**
Hessian-clock descent while preserving its marked collision.  With
`r = topFace.degree - firstActualLayerOrder`, the quotient has determinant
`τ^(4r-6)` and retains the exact collision at `0` and `e₀`.
This is a concrete descent packet, not yet an ambient-state restart. -/
theorem PureLongitudinalMarkedE3Data.reducedClockCollisionFamily
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    let j := T.topKernelMarkedAxisFirstActualLayerOrder
    let r := T.topFace.degree - j
    let Q := firstActualDeformationFamily
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    HasPolynomialFamilyHessianDefect (K := K) Q (4 * r - 6) ∧
      HasPolynomialFamilyExactGradientCollision Q
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))) ∧
      0 < 4 * r - 6 ∧
      4 * r - 6 < 4 * T.topFace.degree - 6 := by
  dsimp
  rcases P.pureLongitudinal_firstActualQuotient_reducedClock
      D.coefficient_ne_zero D.topFace_eq with
    ⟨hdef, hpos, hlt⟩
  exact ⟨hdef,
    P.pureLongitudinal_firstActualQuotient_exactCollision
      D.coefficient_ne_zero D.topFace_eq,
    hpos, hlt⟩

/-- On the reached pure E3 branch the first-actual quotient is
the honest lower-level reverse-Rees family of the *same represented source*,
at weight cap `D-j`.  In particular it is not merely an unspecified
lower-degree collision polynomial. -/
theorem PureLongitudinalMarkedE3Data.relevelledReverseRees
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    let j := T.topKernelMarkedAxisFirstActualLayerOrder
    let r := T.topFace.degree - j
    let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight
      r T.topKernelReesSource :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq
    firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer =
      reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        r T.topKernelReesSource hbound :=
  P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
    D.coefficient_ne_zero D.topFace_eq

/-- The reached pure E3 packet constructs two honest A18 scale-aware
auxiliary states with the same represented source and the same marked
collision.  The strict clock descent between them is certified by the
existing global macro order.  It is deliberately NOT an edge from the
zero-clock represented source itself. -/
theorem PureLongitudinalMarkedE3Data.auxiliaryMacroStep
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    ∃ s t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      s.family = T.topKernelMarkedAxisFirstContactFamily ∧
      t.family =
        firstActualDeformationFamily T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer ∧
      s.degreeCap = T.topFace.degree ∧
      t.degreeCap = T.topFace.degree ∧
      s.scale = T.terminal.blocker.presented.scale ∧
      t.scale = s.scale ∧
      t.repair = s.repair ∧
      t.rawDefect < s.rawDefect ∧
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress t s :=
  P.pureLongitudinal_exists_auxiliaryMacroStep
    D.coefficient_ne_zero D.topFace_eq

/-- Exact **degree-cap separation** at the reachable E3 pure packet.

The normalized first-actual special fibre admits a strict nonlinear
ordinary-degree cap D-1, but the whole collision-bearing quotient cannot
admit that cap, because the original c*X₀^D survives at parameter order
D-j.  This rules out claiming a full-family degree-drop restart here. -/
theorem PureLongitudinalMarkedE3Data.quotientDegreeCapSeparation
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    NonlinearDegreeBound (T.topFace.degree - 1)
      (polynomialFamilySpecialFiber
        (firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer)) ∧
      ¬ NonlinearDegreeBound (T.topFace.degree - 1)
        (firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer) :=
  ⟨P.pureLongitudinal_firstActualQuotient_specialFiber_lowerDegree
      D.coefficient_ne_zero D.topFace_eq,
    P.pureLongitudinal_firstActualQuotient_not_lowerDegreeBound
      D.coefficient_ne_zero D.topFace_eq⟩

/-- **Finite quadratic alternative of the reachable pure E3 packet.**

If the first nonzero marked-axis face has transverse degree two, the ENTIRE
relevelled Hessian family has only parameter orders 0, 1, 2.  Each order is
exactly the corresponding transverse-weight source component, and the whole
family retains its tau² determinant and exact marked collision.  This is the
complete source-honest finite quadratic input for the endpoint calculation. -/
theorem PureLongitudinalMarkedE3Data.quadraticThreeLayerFamily
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
        T.topKernelReesSource :=
      by
        simpa [hr] using
          P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
            D.coefficient_ne_zero D.topFace_eq
    let Q :=
      reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        2 T.topKernelReesSource hbound
    (∀ n : ℕ, 2 < n → familyParameterLayer Q n = 0) ∧
      familyParameterLayer Q 0 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (2 : ℤ) T.topKernelReesSource ∧
      familyParameterLayer Q 1 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (1 : ℤ) T.topKernelReesSource ∧
      familyParameterLayer Q 2 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (0 : ℤ) T.topKernelReesSource ∧
      HasPolynomialFamilyHessianDefect (K := K) Q 2 ∧
      HasPolynomialFamilyExactGradientCollision Q
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))) :=
  P.pureLongitudinal_quadraticRelevel_threeLayers
    D.coefficient_ne_zero D.topFace_eq hr

/-- **Actual represented-source rank-two conclusion in the quadratic E3
branch.** The literal cap-two reverse-Rees family has determinant tau², so
its origin Hessian transverse 3x3 block has a genuine nonzero 2x2 minor.
The conclusion is about the original represented determinant-one source,
not an auxiliary source or an inferred repair step. -/
theorem PureLongitudinalMarkedE3Data.quadratic_sourceTransverseRankTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let H := quadraticFamilyHessianMatrix T.topKernelReesSource
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 := by
  have hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
      T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq
  exact quadraticAxisReverseRees_sourceTransverseRankTwo
    T.topKernelReesSource hbound
    T.topKernelReesSource_hessianDeterminant_eq_one

/-- **New first-actual-face rank-two geometry at the reachable
quadratic E3 terminal.**

This is stronger and more useful than the earlier represented-source rank
witness: the Hessian-singular first nonzero marked-axis face itself has a
nonzero transverse origin Hessian 2x2 minor.  It is therefore not a
rank-one/quadratic-square lower-face packet. -/
theorem PureLongitudinalMarkedE3Data.quadratic_firstActualLayerRankTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let G := familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder
    let H := quadraticFamilyHessianMatrix G
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 :=
  P.pureLongitudinal_quadraticFirstActualLayer_transverseRankTwo
    D.coefficient_ne_zero D.topFace_eq hr

/-- Exact coefficient order of every represented-source monomial in the
marked-axis reverse-Rees family.

The parameter order is precisely the gap from the top level to the monomial's
total transverse degree.  This is the key identity relating maximal common
parameter extraction to maximal attained transverse degree. -/
theorem PureLongitudinalMarkedE3Data.markedAxis_sourceCoefficientOrder
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ T.topKernelReesSource.support) :
    smithFamilyCoefficientOrder
        T.topKernelMarkedAxisFirstContactFamily d =
      T.topFace.degree - (d 1 + d 2 + d 3) := by
  let q := T.topFace.degree - (d 1 + d 2 + d 3)
  have hsource :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcoeff :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily =
        Polynomial.X ^ q *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees,
      reverseWeightedReesFamily_coeff, if_pos hd]
    have he :
        T.topFace.degree -
            Finsupp.weight topKernelMarkedAxisNatWeight d =
          q := by
      dsimp [q]
      rw [weight_topKernelMarkedAxisNatWeight d]
    exact congrArg
      (fun n : ℕ =>
        Polynomial.X ^ n *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource))
      he
  have hcoeffNe :
      MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero
      (pow_ne_zero q Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr hsource)
  have hdFamily :
      d ∈ T.topKernelMarkedAxisFirstContactFamily.support :=
    MvPolynomial.mem_support_iff.mpr hcoeffNe
  rw [smithFamilyCoefficientOrder_eq
    T.topKernelMarkedAxisFirstContactFamily hdFamily]
  unfold smithFamilyCoefficientParameterOrder
  have hprimitive :
      Polynomial.constantCoeff
          (Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource)) ≠ 0 := by
    simpa using hsource
  have horder :=
    polynomialParameterOrder_eq_of_exact_X_power_factorisation
      (K := K)
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily)
      hcoeffNe q
      (Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource))
      hprimitive hcoeff
  simpa [q] using horder

/-- The lossless pure E3 packet still exposes the canonical positive-transverse
Rees low layer, now with the exact physical order retained alongside it. -/
theorem PureLongitudinalMarkedE3Data.positiveTransverseLowLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    Nonempty
      (CanonicalPositiveTransverseReesLowLayer
        (4 * T.topFace.degree - 6)
        T.topKernelMarkedAxisFirstContactFamily) :=
  P.pureLongitudinal_markedAxis_positiveTransverseLowLayer
    D.coefficient_ne_zero D.topFace_eq

/-- In the pure-longitudinal E3 branch the collision-bearing marked-axis
special fibre is literally zero.  Indeed its support is exactly the
zero-longitudinal slice of the ordinary top face, while that top face consists
only of the nonzero monomial `X₀^D` with `D ≥ 3`. -/
theorem PureLongitudinalMarkedE3Data.markedAxisSpecialFiber_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily = 0 := by
  apply MvPolynomial.ext
  intro d
  by_contra hcoeff
  have hd :
      d ∈ (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  rcases
      (T.topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero d).1 hd with
    ⟨htop, hzero⟩
  have htopCoeff : MvPolynomial.coeff d T.topFace.face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp htop
  rw [D.topFace_eq, MvPolynomial.coeff_C_mul] at htopCoeff
  have hpow :
      MvPolynomial.coeff d
          (((MvPolynomial.X (0 : Fin 4) :
              MvPolynomial (Fin 4) K)) ^ T.topFace.degree) ≠ 0 := by
    intro hz
    apply htopCoeff
    simp [hz]
  have hdEqRev :
      Finsupp.single (0 : Fin 4) T.topFace.degree = d := by
    rw [MvPolynomial.coeff_X_pow] at hpow
    simpa using hpow
  have hdEq :
      d = Finsupp.single (0 : Fin 4) T.topFace.degree :=
    hdEqRev.symm
  have hDzero : T.topFace.degree = 0 := by
    simpa [hdEq] using hzero
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  omega

/-- The zero special fibre yields an honest common-factor quotient family.

Removing one parameter factor preserves the literal constant marked collision
and lowers the pure Hessian defect by exactly four.  Since the top degree is at
least three, the residual defect is still positive. -/
theorem PureLongitudinalMarkedE3Data.commonFactorQuotient
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    ∃ hdiv :
        HasCommonParameterFactor 1 T.topKernelMarkedAxisFirstContactFamily,
      HasPolynomialFamilyHessianDefect
        (K := K)
        (commonParameterFactorFamily
          1 T.topKernelMarkedAxisFirstContactFamily hdiv)
        ((4 * T.topFace.degree - 6) - 4) ∧
      HasPolynomialFamilyExactGradientCollision
        (commonParameterFactorFamily
          1 T.topKernelMarkedAxisFirstContactFamily hdiv)
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))) ∧
      0 < (4 * T.topFace.degree - 6) - 4 := by
  let hdiv :
      HasCommonParameterFactor 1 T.topKernelMarkedAxisFirstContactFamily :=
    hasCommonParameterFactor_one_of_specialFiber_eq_zero
      T.topKernelMarkedAxisFirstContactFamily
      (D.markedAxisSpecialFiber_eq_zero P)
  refine ⟨hdiv, ?_, ?_, ?_⟩
  · exact
      commonParameterFactor_one_hasHessianDefect_sub_four
        T.topKernelMarkedAxisFirstContactFamily
        hdiv
        (4 * T.topFace.degree - 6)
        T.topKernelMarkedAxisFirstContact_hasHessianDefect
  · exact
      polynomialFamilyExactGradientCollision_commonParameterFactor
        1 T.topKernelMarkedAxisFirstContactFamily hdiv
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4)))
        T.topKernelMarkedAxisFirstContact_exactGradientCollision
  · have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
    omega

/-- Strip the entire common parameter factor of the pure marked-axis family
in one finite step.

The extracted order is strictly positive because the original special fibre is
zero.  The maximal quotient has nonzero special fibre by construction, and the
literal marked collision survives the factor cancellation. -/
theorem PureLongitudinalMarkedE3Data.maximalCommonFactorQuotient
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    ∃ hne : T.topKernelMarkedAxisFirstContactFamily.support.Nonempty,
      let m :=
        minimalAdaptiveFamilyParameterOrder
          T.topKernelMarkedAxisFirstContactFamily hne
      let hdiv :=
        minimalAdaptiveFamilyParameterOrder_commonFactor
          T.topKernelMarkedAxisFirstContactFamily hne
      0 < m ∧
        HasPolynomialFamilyHessianDefect
          (K := K)
          (commonParameterFactorFamily
            m T.topKernelMarkedAxisFirstContactFamily hdiv)
          ((4 * T.topFace.degree - 6) - 4 * m) ∧
        0 < (4 * T.topFace.degree - 6) - 4 * m ∧
        polynomialFamilySpecialFiber
            (commonParameterFactorFamily
              m T.topKernelMarkedAxisFirstContactFamily hdiv) ≠ 0 ∧
        HasPolynomialFamilyExactGradientCollision
          (commonParameterFactorFamily
            m T.topKernelMarkedAxisFirstContactFamily hdiv)
          (zeroPolynomialSection (K := K))
          (polynomialConstantSection
            (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
  rcases D.positiveTransverseLowLayer P with ⟨L⟩
  let hne : T.topKernelMarkedAxisFirstContactFamily.support.Nonempty :=
    ⟨L.exponent, L.mem⟩
  let m :=
    minimalAdaptiveFamilyParameterOrder
      T.topKernelMarkedAxisFirstContactFamily hne
  let hdiv :=
    minimalAdaptiveFamilyParameterOrder_commonFactor
      T.topKernelMarkedAxisFirstContactFamily hne
  have hmpos : 0 < m :=
    minimalAdaptiveFamilyParameterOrder_pos_of_specialFiber_eq_zero
      T.topKernelMarkedAxisFirstContactFamily hne
      (D.markedAxisSpecialFiber_eq_zero P)
  have hdef :
      HasPolynomialFamilyHessianDefect
        (K := K)
        (commonParameterFactorFamily
          m T.topKernelMarkedAxisFirstContactFamily hdiv)
        ((4 * T.topFace.degree - 6) - 4 * m) :=
    commonParameterFactor_hasHessianDefect_sub_four_mul
      m T.topKernelMarkedAxisFirstContactFamily hdiv
      (4 * T.topFace.degree - 6)
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
  have hle :
      4 * m ≤ 4 * T.topFace.degree - 6 :=
    alignedSmith_four_mul_le_defect_of_commonParameterFactor
      m T.topKernelMarkedAxisFirstContactFamily hdiv
      (4 * T.topFace.degree - 6)
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
  have hrespos :
      0 < (4 * T.topFace.degree - 6) - 4 * m := by
    have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
    omega
  refine ⟨hne, hmpos, hdef, hrespos, ?_, ?_⟩
  · exact
      polynomialFamilySpecialFiber_maximalCommonParameterFactor_ne_zero
        T.topKernelMarkedAxisFirstContactFamily hne
  · exact
      polynomialFamilyExactGradientCollision_commonParameterFactor
        m T.topKernelMarkedAxisFirstContactFamily hdiv
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4)))
        T.topKernelMarkedAxisFirstContact_exactGradientCollision

/-- **Marked-aware E3 frontier.**

Unlike the older source-rank-three compression, this interface consumes the
pure-longitudinal marked-axis constructor *before* entering the generic C/D
fallback.  The pure branch is now retained losslessly: besides its honest
represented-source codimension-two exponent it keeps the pure top-face
identity and the exact preclosing marked-axis coefficient order.  All other
E2 constructors retain the terminal-aware C/D timing frontier. -/
inductive TopKernelLinearPowerE3MarkedAwareFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | pureLongitudinal
      (data : P.PureLongitudinalMarkedE3Data)
  | sourcePointThreeByThree
      (geometry : P.PositiveTailRepresentedSourceThreeByThreePointGeometry)
  | sourceConstantThreeByThree
      (active :
        AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented)
      (geometry :
        AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry active)
  | exactClosing
      (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer)
      (relative_pos : 0 < tail.relativeOrder)
      (binary : P.PositiveTailExplicitBinaryClockData clock)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (geometry : P.PositiveTailRankOneClosingSourcePointGeometry rankOne)

/-- The terminal-aware C/D frontier embeds into the marked-aware E3 frontier
without losing its exact-closing timing. -/
theorem TopKernelLinearPowerE3TerminalAwareFrontier.toMarkedAware
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (G : P.TopKernelLinearPowerE3TerminalAwareFrontier) :
    Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
  cases G with
  | sourcePointThreeByThree Q =>
      exact ⟨.sourcePointThreeByThree Q⟩
  | sourceConstantThreeByThree A Q =>
      exact ⟨.sourceConstantThreeByThree A Q⟩
  | exactClosing layer clock tangent tail hpos binary rankOne geometry =>
      exact ⟨.exactClosing layer clock tangent tail hpos binary rankOne geometry⟩

/-- **E2 -> marked-aware E3 refinement.**

The pure-longitudinal marked-axis branch is now removed from the generic
source-3x3 collapse.  Every other E2 constructor continues through the
terminal-aware C/D classifier. -/
theorem topKernelLinearPowerE3MarkedAwareFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
  have hfallback :
      ∀ E : P.TopKernelLinearPowerE2Frontier,
        Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
    intro E
    rcases E.toE3TerminalAwareFrontier with ⟨G⟩
    exact G.toMarkedAware P

  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  cases E with
  | pureLongitudinal coefficient hcoeff hface hk cd =>
      rcases P.pureLongitudinalFirstContactFrontier_nonempty
          hcoeff hface with ⟨Q⟩
      rcases Q.toCodimensionTwoSourceData P with ⟨R⟩
      exact ⟨.pureLongitudinal {
        coefficient := coefficient
        coefficient_ne_zero := hcoeff
        topFace_eq := hface
        kernel_ne_zero := hk
        sourceExponent := R.exponent
        source_mem := R.mem_source
        source_boundary := R.boundary
        topCoefficientOrder_eq :=
          P.pureLongitudinal_markedAxis_topCoefficientOrder_eq hcoeff hface
        topCoefficientOrder_pos_lt_defect :=
          P.pureLongitudinal_markedAxis_topCoefficientOrder_pos_lt_defect
            hcoeff hface
      }⟩
  | fullFacetCodimensionTwo hfacet hboundary cd =>
      exact hfallback
        (.fullFacetCodimensionTwo hfacet hboundary cd)
  | fullFacetActualRankTwo hfacet geometry cd =>
      exact hfallback
        (.fullFacetActualRankTwo hfacet geometry cd)
  | crossFacetNear data hboundary cd =>
      exact hfallback
        (.crossFacetNear data hboundary cd)
  | crossFacetFar data hboundary cd =>
      exact hfallback
        (.crossFacetFar data hboundary cd)

/-- Canonical marked-aware E3 output. -/
noncomputable def topKernelLinearPowerE3MarkedAwareFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelLinearPowerE3MarkedAwareFrontier :=
  Classical.choice P.topKernelLinearPowerE3MarkedAwareFrontier_nonempty

/-- **Marked-aware single-obligation E3 assembly.**

The pure-longitudinal branch now retains its full rigid packet: pure top-face
identity, literal represented-source codimension-two support, and exact
preclosing marked-axis order.  The timing-rich exact closing remains explicit.
Raw defect zero still supplies the same canonical exact-active source chart
independently of which marked-aware constructor was reached.  Therefore, if one
is willing to forget the extra timing, the entire marked-aware frontier has
exactly the same single unresolved polynomial-level obligation as the older
source-rank-three compression: resolve one nonzero constant 3x3 source minor. -/
theorem exists_finalResolution_of_e3MarkedAwareConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  have hcanonical :
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
    rcases
        T.terminal.blocker.presented.zeroDefect_exactActiveFourBlock
          T.presented_zero with
      ⟨A⟩
    rcases P.exactActive_threeByThree_of_presentedZero A with ⟨Q⟩
    exact X.sourceConstant A Q
  rcases P.topKernelLinearPowerE3MarkedAwareFrontier_nonempty with ⟨G⟩
  cases G with
  | pureLongitudinal _data =>
      exact hcanonical
  | sourcePointThreeByThree _Q =>
      exact hcanonical
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q
  | exactClosing _layer _clock _tangent _tail _hpos _binary _rankOne _geometry =>
      exact hcanonical

/-- Lossless marked-aware final-resolution extractor.

Unlike the older constant-minor compression, this interface does not discard
the pure-longitudinal packet or the exact-closing timing.  The evaluated
source-point branch is the only constructor collapsed through the canonical
raw-zero constant chart. -/
structure TopKernelLinearPowerE3MarkedAwareFinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  pureLongitudinal :
    P.PureLongitudinalMarkedE3Data →
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  exactClosing :
    ∀ (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer),
      0 < tail.relativeOrder →
      ∀ (binary : P.PositiveTailExplicitBinaryClockData clock)
        (rankOne : P.PositiveTailExplicitRankOneClockData binary),
        P.PositiveTailRankOneClosingSourcePointGeometry rankOne →
          Nonempty
            (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- The lossless marked-aware frontier feeds the corresponding endpoint
extractor without forgetting the rigid pure branch. -/
theorem exists_finalResolution_of_e3MarkedAwareExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3MarkedAwareFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  have hcanonical :
      ∀ (_Q : P.PositiveTailRepresentedSourceThreeByThreePointGeometry),
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
    intro _Q
    rcases
        T.terminal.blocker.presented.zeroDefect_exactActiveFourBlock
          T.presented_zero with
      ⟨A⟩
    rcases P.exactActive_threeByThree_of_presentedZero A with ⟨Q⟩
    exact X.sourceConstant A Q
  rcases P.topKernelLinearPowerE3MarkedAwareFrontier_nonempty with ⟨G⟩
  cases G with
  | pureLongitudinal data =>
      exact X.pureLongitudinal data
  | sourcePointThreeByThree Q =>
      exact hcanonical Q
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q
  | exactClosing layer clock tangent tail hpos binary rankOne geometry =>
      exact X.exactClosing layer clock tangent tail hpos binary rankOne geometry

/-- **Timing-preserving E3 final-resolution extractor.**

The source-point and source-constant branches are retained exactly as in the
older E3 interface.  Crucially, the positive-relative rank-one exact-closing
branch is *not* collapsed to generic represented-source rank-three geometry:
its exact clock, tangent tail, binary/rank-one packets and whole-family
first-opening geometry remain available to the final endpoint producer. -/
structure TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourcePoint :
    P.PositiveTailRepresentedSourceThreeByThreePointGeometry →
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  exactClosing :
    ∀ (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer),
      0 < tail.relativeOrder →
      ∀ (binary : P.PositiveTailExplicitBinaryClockData clock)
        (rankOne : P.PositiveTailExplicitRankOneClockData binary),
        P.PositiveTailRankOneClosingSourcePointGeometry rankOne →
          Nonempty
            (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- The terminal-aware E3 frontier feeds the timing-preserving extractor
without discarding the exact-closing first-opening data. -/
theorem exists_finalResolution_of_e3TerminalAwareExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  rcases E.toE3TerminalAwareFrontier with ⟨G⟩
  cases G with
  | sourcePointThreeByThree Q =>
      exact X.sourcePoint Q
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q
  | exactClosing layer clock tangent tail hpos binary rankOne geometry =>
      exact X.exactClosing layer clock tangent tail hpos binary rankOne geometry

/-- At raw defect zero the evaluated source-point event can still be routed
through the canonical exact-active constant 3x3 chart.  Preserving exact
closing therefore leaves exactly *two* genuine endpoint obligations:
the constant source chart and the timing-rich exact-closing branch. -/
structure TopKernelLinearPowerE3TerminalAwareConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  exactClosing :
    ∀ (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer),
      0 < tail.relativeOrder →
      ∀ (binary : P.PositiveTailExplicitBinaryClockData clock)
        (rankOne : P.PositiveTailExplicitRankOneClockData binary),
        P.PositiveTailRankOneClosingSourcePointGeometry rankOne →
          Nonempty
            (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- Convert the two-obligation terminal-aware interface to the full
three-constructor timing-preserving extractor. -/
noncomputable def
    TopKernelLinearPowerE3TerminalAwareConstantExtractor.toTerminalAwareExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareConstantExtractor) :
    P.TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor where
  sourcePoint := by
    intro _Q
    rcases
        T.terminal.blocker.presented.zeroDefect_exactActiveFourBlock
          T.presented_zero with
      ⟨A⟩
    rcases P.exactActive_threeByThree_of_presentedZero A with ⟨Q⟩
    exact X.sourceConstant A Q
  sourceConstant := by
    intro A Q
    exact X.sourceConstant A Q
  exactClosing := by
    intro layer clock tangent tail hpos binary rankOne geometry
    exact X.exactClosing layer clock tangent tail hpos binary rankOne geometry

/-- Timing-preserving assembly with the evaluated source-point constructor
already absorbed into the zero-defect exact-active chart. -/
theorem exists_finalResolution_of_e3TerminalAwareConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareConstantExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  P.exists_finalResolution_of_e3TerminalAwareExtractor
    (X.toTerminalAwareExtractor P)

/-- **Top-kernel E1/E2/E3 assembly.**

Once the two genuine source-rank-three events can be converted to permitted
polynomial endpoints, every linear-power top-kernel packet has a sound final
resolution.  All marked-axis support cases, cross-facet/codimension-two
branches, projected Schur cases and relative-order cases have already been
consumed upstream. -/
theorem exists_finalResolution_of_e3Extractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3FinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  rcases E.toE3RankThreeFrontier with ⟨G⟩
  cases G with
  | sourcePointThreeByThree Q =>
      exact X.sourcePoint Q
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q

/-- Every linear-power top-kernel packet is therefore reduced to one genuine
polynomial-level extraction obligation if one deliberately forgets the
exact-closing timing.  The terminal-aware interface above is preferred for
new endpoint work. -/
theorem exists_finalResolution_of_e3ConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  P.exists_finalResolution_of_e3Extractor (X.toE3Extractor P)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
