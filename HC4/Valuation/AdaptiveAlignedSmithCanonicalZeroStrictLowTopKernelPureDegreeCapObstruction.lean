import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureAuxiliaryMacroStep
import Mathlib.Tactic

/-!
# The exact ordinary-degree obstruction after pure marked-axis relevel

For the reachable pure top-face branch, the entire first-actual quotient is
the strict reverse-Rees relevel of the original represented source.

Its special fibre has an honest smaller nonlinear ordinary-degree cap D-1.
Nevertheless, the FULL polynomial-parameter quotient contains the original
top monomial X₀^D: its coefficient is exactly tau^(D-j) * c, c ≠ 0.
Thus the quotient CANNOT satisfy nonlinear ordinary-degree cap D-1.

This identifies the remaining mathematical obstruction to interpreting the
auxiliary raw-clock decrease as an ordinary-degree decrease on the whole
family.  Neither a replacement source nor a degree-lowering restart is
postulated.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The pure top coefficient survives the *whole* first-actual quotient at
the precisely relevelled positive parameter order r=D-j. -/
theorem pureLongitudinal_firstActualQuotient_topCoefficient
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 4) T.topFace.degree)
        (firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer) =
      Polynomial.X ^
        (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder) *
          Polynomial.C coefficient := by
  let d : Fin 4 →₀ ℕ :=
    Finsupp.single (0 : Fin 4) T.topFace.degree
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    simp [d, HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  have hdTop : MvPolynomial.coeff d T.topFace.face = coefficient := by
    rw [topFace_eq, MvPolynomial.coeff_C_mul]
    simp [d, MvPolynomial.coeff_X_pow]
  have hdSource : MvPolynomial.coeff d T.topKernelReesSource = coefficient := by
    change
      MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) =
        coefficient
    rw [← T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
    exact hdTop
  have hdSourceNe :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 := by
    rw [hdSource]
    exact coefficient_ne_zero
  have hdMem : d ∈ T.topKernelReesSource.support :=
    MvPolynomial.mem_support_iff.mpr hdSourceNe
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight
      r T.topKernelReesSource :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      coefficient_ne_zero topFace_eq
  have heq :=
    P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
      coefficient_ne_zero topFace_eq
  change firstActualDeformationFamily
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer =
    reverseWeightedReesFamily topKernelMarkedAxisNatWeight
      r T.topKernelReesSource hbound at heq
  rw [heq, reverseWeightedReesFamily_coeff, if_pos hdMem]
  have hw : Finsupp.weight topKernelMarkedAxisNatWeight d = 0 := by
    rw [weight_topKernelMarkedAxisNatWeight]
    simp [d]
  rw [hw, hdSource]
  simp [r, d]

/-- The strict decrease from D to D-1 applies to the special fibre of the
first-actual quotient, not merely to an unrepresented formal layer. -/
theorem pureLongitudinal_firstActualQuotient_specialFiber_lowerDegree
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    NonlinearDegreeBound (T.topFace.degree - 1)
      (polynomialFamilySpecialFiber
        (firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer)) := by
  rw [firstActualDeformationFamily_specialFiber]
  exact P.pureLongitudinal_markedAxis_firstActualLayer_nonlinearDegreeBound
    coefficient_ne_zero topFace_eq

/-- The full quotient still genuinely attains degree D.  In particular,
using the strictly lower special-fibre cap as the whole-family A18 degree
cap would be unsound. -/
theorem pureLongitudinal_firstActualQuotient_not_lowerDegreeBound
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    ¬ NonlinearDegreeBound (T.topFace.degree - 1)
      (firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer) := by
  let d : Fin 4 →₀ ℕ :=
    Finsupp.single (0 : Fin 4) T.topFace.degree
  let Q := firstActualDeformationFamily
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  have hcoeff :
      MvPolynomial.coeff d Q ≠ 0 := by
    have htop :=
      P.pureLongitudinal_firstActualQuotient_topCoefficient
        coefficient_ne_zero topFace_eq
    change MvPolynomial.coeff d Q =
        Polynomial.X ^
          (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder) *
            Polynomial.C coefficient at htop
    rw [htop]
    exact mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero)
      (Polynomial.C_ne_zero.mpr coefficient_ne_zero)
  have hdMem : d ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hdeg : HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    simp [d, HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  intro hlower
  have hD : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
  have hineq := hlower d hdMem (by omega)
  omega

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
