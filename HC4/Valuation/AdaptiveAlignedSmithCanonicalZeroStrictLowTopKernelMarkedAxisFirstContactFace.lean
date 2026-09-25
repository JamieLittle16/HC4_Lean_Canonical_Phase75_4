import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseReesCollision
import HC4.Polynomial.WeightedInitial
import HC4.Newton.TerminalPermutedGradient
import HC4.Newton.MixedDegreeAxisCollision
import HC4.Newton.TerminalTwoZeroSupport
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

/-- Integer-valued form of the same transverse-degree identity. -/
theorem weight_topKernelMarkedAxisIntWeight
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
      ((d 1 + d 2 + d 3 : ℕ) : ℤ) := by
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
      HC4.Polynomial.initialForm
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
    HC4.Polynomial.initialForm_isWeightedHomogeneous
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (T.topFace.degree : ℤ)
      T.topKernelReesSource

/-- The honest marked-axis first-contact family retains an exact pure Hessian
clock.  Its weight sum is three, so the determinant order is `4D - 6`. -/
theorem topKernelMarkedAxisFirstContact_hasHessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K)
      T.topKernelMarkedAxisFirstContactFamily
      (4 * T.topFace.degree - 6) := by
  have hdegree : 3 ≤ T.topFace.degree :=
    T.topFace.degree_ge_three
  have hnonneg :
      2 * ∑ i : Fin 4, topKernelMarkedAxisNatWeight i ≤
        4 * T.topFace.degree := by
    simp [topKernelMarkedAxisNatWeight, Fin.sum_univ_four]
    omega
  have hclock :=
    reverseWeightedReesFamily_hasHessianDefect
      topKernelMarkedAxisNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasMarkedAxisReverseWeightBound
      T.topKernelReesSource_hessianDeterminant_eq_one
      hnonneg
  rw [← T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees] at hclock
  simpa [topKernelMarkedAxisNatWeight, Fin.sum_univ_four] using hclock

/-- The marked-axis first-contact clock is genuinely positive. -/
theorem topKernelMarkedAxisFirstContact_defect_pos :
    0 < 4 * T.topFace.degree - 6 := by
  have hdegree : 3 ≤ T.topFace.degree :=
    T.topFace.degree_ge_three
  omega

/-- Every monomial surviving on the marked-axis first-contact fibre has
zero exponent in the marked coordinate.  The maximal ordinary-degree bound is
essential here: transverse marked weight already exhausts the full level. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_exponent_zero
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) ≠ 0) :
    d 0 = 0 := by
  have hweighted :=
    T.topKernelMarkedAxisFirstContact_specialFiber_homogeneous d hd
  have hw :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
        (T.topFace.degree : ℤ) := by
    rw [← integralWeightedDegree_eq_finsuppWeight]
    exact hweighted
  have htransZ :
      ((d 1 + d 2 + d 3 : ℕ) : ℤ) =
        (T.topFace.degree : ℤ) := by
    have hw' := hw
    rw [Finsupp.weight_apply, Finsupp.sum_fintype] at hw'
    · simpa [topKernelMarkedAxisNatWeight, Fin.sum_univ_four] using hw'
    · intro i
      simp
  have htrans :
      d 1 + d 2 + d 3 = T.topFace.degree := by
    exact_mod_cast htransZ
  have hsource :
      MvPolynomial.coeff d T.topKernelReesSource ≠ 0 := by
    have hinit := hd
    rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
      HC4.Polynomial.coeff_initialForm, if_pos hw] at hinit
    exact hinit
  have hmem : d ∈ T.topKernelReesSource.support :=
    MvPolynomial.mem_support_iff.mpr hsource
  have hord :
      HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
    simpa only [weight_ordinaryTopNatWeight] using
      T.topKernelReesSource_hasReverseWeightBound d hmem
  unfold HC4.Polynomial.ordinaryDegree4 at hord
  omega

/-- The marked-axis first-contact special fibre is independent of coordinate
zero. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_pderiv_zero :
    MvPolynomial.pderiv (0 : Fin 4)
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) = 0 := by
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hd
  exact T.topKernelMarkedAxisFirstContact_specialFiber_exponent_zero d hd

/-- Consequently the first-contact fibre is genuinely singular: its formal
Hessian has a zero row in the marked direction. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_hessianDeterminant_eq_zero :
    HC4.Polynomial.hessianDeterminant
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) = 0 := by
  unfold HC4.Polynomial.hessianDeterminant
  apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 4)
  intro j
  simp [HC4.Polynomial.hessian,
    T.topKernelMarkedAxisFirstContact_specialFiber_pderiv_zero]

/-- The marked-axis face is exactly the longitudinal-exponent-zero slice
of the singular maximal ordinary top face.  We state this through the native
`finSuccEquiv` decomposition: the outer coefficient at `X₀^0` is identical. -/
theorem topKernelMarkedAxisFirstContact_transverseSlice_eq_topFace :
    (MvPolynomial.finSuccEquiv K 3
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily)).coeff 0 =
      (MvPolynomial.finSuccEquiv K 3 T.topFace.face).coeff 0 := by
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.finSuccEquiv_coeff_coeff]
  let d : Fin 4 →₀ ℕ := m.cons 0
  change
    MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily) =
      MvPolynomial.coeff d T.topFace.face
  rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
    HC4.Polynomial.coeff_initialForm,
    T.topFace.coeff_face]
  have hw :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
        (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
    dsimp [d]
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp [topKernelMarkedAxisNatWeight,
        HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
    · intro i
      simp
  rw [hw]
  simp [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]

/-- Exact support description of the marked-axis face: it is precisely the
zero-longitudinal slice of the singular maximal ordinary top face. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_support_iff_topFace_zero
    (d : Fin 4 →₀ ℕ) :
    d ∈ (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support ↔
      d ∈ T.topFace.face.support ∧ d 0 = 0 := by
  constructor
  · intro hd
    have hcoeffSpecial :
        MvPolynomial.coeff d
            (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hzero :=
      T.topKernelMarkedAxisFirstContact_specialFiber_exponent_zero d hcoeffSpecial
    have hweighted :=
      T.topKernelMarkedAxisFirstContact_specialFiber_homogeneous d hcoeffSpecial
    have hweight :
        Finsupp.weight
            (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
          (T.topFace.degree : ℤ) := by
      rw [← integralWeightedDegree_eq_finsuppWeight]
      exact hweighted
    have hw := hweight
    rw [weight_topKernelMarkedAxisIntWeight] at hw
    have htrans :
        d 1 + d 2 + d 3 = T.topFace.degree := by
      exact_mod_cast hw
    have hdeg :
        HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
      unfold HC4.Polynomial.ordinaryDegree4
      omega
    have hsource : MvPolynomial.coeff d T.topKernelReesSource ≠ 0 := by
      have hcoeff := hcoeffSpecial
      rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
        HC4.Polynomial.coeff_initialForm, if_pos hweight] at hcoeff
      exact hcoeff
    have htopCoeff :
        MvPolynomial.coeff d T.topFace.face ≠ 0 := by
      rw [T.topFace.coeff_eq_source_of_ordinaryDegree_eq d hdeg]
      simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]
        using hsource
    exact ⟨MvPolynomial.mem_support_iff.mpr htopCoeff, hzero⟩
  · rintro ⟨htop, hzero⟩
    have hdeg := T.topFace.ordinaryDegree_eq_of_mem_support htop
    have hsourceMem := T.topFace.source_mem_of_face_mem htop
    have htrans :
        d 1 + d 2 + d 3 = T.topFace.degree := by
      unfold HC4.Polynomial.ordinaryDegree4 at hdeg
      omega
    have hw :
        Finsupp.weight
            (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) d =
          (T.topFace.degree : ℤ) := by
      rw [weight_topKernelMarkedAxisIntWeight]
      exact_mod_cast htrans
    apply MvPolynomial.mem_support_iff.mpr
    rw [T.topKernelMarkedAxisFirstContact_specialFiber_eq_initialForm,
      HC4.Polynomial.coeff_initialForm, if_pos hw]
    have hsourceCoeff :
        MvPolynomial.coeff d
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hsourceMem
    simpa [AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.topKernelReesSource]
      using hsourceCoeff

/-- Polynomial-level packet retained at the E-stage boundary: an exact
weighted-homogeneous associated-graded fibre together with its literal distinct
marked collision. -/
structure TopKernelMarkedAxisFirstContactFaceData : Type (u + 1) where
  fibre : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily
  fibre_eq :
    fibre =
      HC4.Polynomial.initialForm
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
        (T.topFace.degree : ℤ)
        T.topKernelReesSource
  homogeneous :
    IsIntegralWeightedHomogeneous
      (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
      (T.topFace.degree : ℤ) fibre
  markedIndependent :
    MvPolynomial.pderiv (0 : Fin 4) fibre = 0
  hessian_zero :
    HC4.Polynomial.hessianDeterminant fibre = 0
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
  markedIndependent := T.topKernelMarkedAxisFirstContact_specialFiber_pderiv_zero
  hessian_zero := T.topKernelMarkedAxisFirstContact_specialFiber_hessianDeterminant_eq_zero
  exactCollision := T.topKernelMarkedAxisFirstContact_specialFiber_exactCollision
  distinct := T.topKernelMarkedAxisFirstContact_specialFiber_collisionPoints_ne

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
