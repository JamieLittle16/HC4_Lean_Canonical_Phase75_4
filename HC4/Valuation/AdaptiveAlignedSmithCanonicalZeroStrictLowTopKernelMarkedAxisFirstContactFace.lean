import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseReesCollision
import HC4.Newton.TerminalPermutedGradient
import Mathlib.Tactic

/-!
# The marked-axis first-contact family is an honest weighted face

The ordinary top-kernel reverse-Rees family assigns weight one to all four
source coordinates.  The marked-axis first-contact operation then inflates
coordinate zero by one further parameter factor.  Coefficientwise, for a source
exponent `d`, the total parameter order is therefore

    D - (d₀ + d₁ + d₂ + d₃) + d₀
      = D - (d₁ + d₂ + d₃).

Thus the whole first-contact family is itself exactly the bounded reverse-Rees
family of the represented source for weight `(0,1,1,1)`.  Its special fibre
is consequently the corresponding exact weighted initial form.

This file only identifies the honest polynomial carrier.  It does not call the
fibre a certified terminal endpoint and does not assert a Monge--Ampere
determinant for that fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural source weight of the marked-axis first-contact face:
coordinate zero is unweighted and the three transverse coordinates have
weight one. -/
def topKernelMarkedAxisNatWeight : Fin 4 → ℕ :=
  fun i => if i = 0 then 0 else 1

@[simp] theorem topKernelMarkedAxisNatWeight_zero :
    topKernelMarkedAxisNatWeight (0 : Fin 4) = 0 := by
  simp [topKernelMarkedAxisNatWeight]

@[simp] theorem topKernelMarkedAxisNatWeight_one :
    topKernelMarkedAxisNatWeight (1 : Fin 4) = 1 := by
  simp [topKernelMarkedAxisNatWeight]

@[simp] theorem topKernelMarkedAxisNatWeight_two :
    topKernelMarkedAxisNatWeight (2 : Fin 4) = 1 := by
  simp [topKernelMarkedAxisNatWeight]

@[simp] theorem topKernelMarkedAxisNatWeight_three :
    topKernelMarkedAxisNatWeight (3 : Fin 4) = 1 := by
  simp [topKernelMarkedAxisNatWeight]

/-- The marked-axis natural weight is exactly transverse ordinary degree. -/
theorem weight_topKernelMarkedAxisNatWeight
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight topKernelMarkedAxisNatWeight d =
      d 1 + d 2 + d 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [topKernelMarkedAxisNatWeight, Fin.sum_univ_four]
  · intro i
    simp

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state)

/-- The represented source is bounded by the marked-axis weight at the same
ordinary top-face level.  This is weaker than the already stored ordinary
weight bound. -/
theorem topKernelReesSource_hasMarkedAxisReverseWeightBound :
    HasReverseWeightBound topKernelMarkedAxisNatWeight T.topFace.degree
      T.topKernelReesSource := by
  intro d hd
  have hord :
      HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
    simpa only [weight_ordinaryTopNatWeight] using
      T.topKernelReesSource_hasReverseWeightBound d hd
  rw [weight_topKernelMarkedAxisNatWeight]
  unfold HC4.Polynomial.ordinaryDegree4 at hord
  omega

/-- **Whole-family marked-axis identity.**
The first-contact source inflation converts the ordinary reverse-Rees family
exactly into the bounded reverse-Rees family for weight `(0,1,1,1)`. -/
theorem topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees :
    T.topKernelMarkedAxisFirstContactFamily =
      reverseWeightedReesFamily
        topKernelMarkedAxisNatWeight T.topFace.degree T.topKernelReesSource
        T.topKernelReesSource_hasMarkedAxisReverseWeightBound := by
  apply MvPolynomial.ext
  intro d
  rw [topKernelMarkedAxisFirstContactFamily, coeff_kernelInflateHom,
    topKernelReverseReesFamily, reverseWeightedReesFamily_coeff,
    reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ T.topKernelReesSource.support
  · simp only [hd, if_true, pow_one]
    rw [weight_ordinaryTopNatWeight, weight_topKernelMarkedAxisNatWeight]
    have hord :
        HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
      simpa only [weight_ordinaryTopNatWeight] using
        T.topKernelReesSource_hasReverseWeightBound d hd
    have hexp :
        T.topFace.degree - HC4.Polynomial.ordinaryDegree4 d + d 0 =
          T.topFace.degree - (d 1 + d 2 + d 3) := by
      unfold HC4.Polynomial.ordinaryDegree4 at hord ⊢
      omega
    calc
      (Polynomial.X ^
            (T.topFace.degree - HC4.Polynomial.ordinaryDegree4 d) *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource)) *
          Polynomial.X ^ d 0 =
        (Polynomial.X ^
              (T.topFace.degree - HC4.Polynomial.ordinaryDegree4 d) *
            Polynomial.X ^ d 0) *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
            ring
      _ = Polynomial.X ^
            (T.topFace.degree - HC4.Polynomial.ordinaryDegree4 d + d 0) *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
            rw [← pow_add]
      _ = Polynomial.X ^
            (T.topFace.degree - (d 1 + d 2 + d 3)) *
          Polynomial.C (MvPolynomial.coeff d T.topKernelReesSource) := by
            rw [hexp]
  · simp [hd]

/-- The marked-axis first-contact special fibre is the exact
`(0,1,1,1)` weighted initial form of the represented source. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm :
    polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily =
      initialForm
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
        (T.topFace.degree : ℤ)
        T.topKernelReesSource := by
  rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees]
  exact
    polynomialFamilySpecialFiber_reverseWeightedReesFamily
      topKernelMarkedAxisNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasMarkedAxisReverseWeightBound

/-- The actual collision-bearing first-contact special fibre is weighted
homogeneous for the honest marked-axis weight. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_homogeneous :
    IsIntegralWeightedHomogeneous
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (T.topFace.degree : ℤ)
      (polynomialFamilySpecialFiber
        T.topKernelMarkedAxisFirstContactFamily) := by
  rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm]
  apply mathlibWeightedHomogeneous_to_integral
  exact
    initialForm_isWeightedHomogeneous
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (T.topFace.degree : ℤ)
      T.topKernelReesSource

/-- Polynomial-level packet retained at the E-stage boundary: an exact
weighted-homogeneous associated-graded fibre together with its literal distinct
marked collision. -/
structure TopKernelMarkedAxisFirstContactFaceData : Type (u + 1) where
  fibre : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily
  fibre_eq :
    fibre =
      initialForm
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
        (T.topFace.degree : ℤ)
        T.topKernelReesSource
  homogeneous :
    IsIntegralWeightedHomogeneous
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (T.topFace.degree : ℤ) fibre
  exactCollision :
    HasExactGradientCollision
      fibre
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  distinct :
    (fun _ : Fin 4 => (0 : K)) ≠
      coordinateAxisPoint (K := K) (0 : Fin 4)

/-- Canonical polynomial-level marked-axis first-contact packet. -/
noncomputable def topKernelMarkedAxisFirstContactFaceData :
    T.TopKernelMarkedAxisFirstContactFaceData where
  fibre :=
    polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily
  fibre_eq := T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm
  homogeneous := T.topKernelMarkedAxisFirstContact_specialFiber_homogeneous
  exactCollision := T.topKernelMarkedAxisFirstContact_specialFiber_exactCollision
  distinct := T.topKernelMarkedAxisFirstContact_specialFiber_collisionPoints_ne

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
