import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroLinearJetKernelOpening
import Mathlib.Tactic

/-!
# A18.4.90: saturated kernel opening has honest rank frontier

The historical complete first-contact wrapper promoted rank merely from the
existence of one new Hessian entry.  That is not a sufficient geometric
criterion: a symmetric Hessian can acquire a new nonzero entry while remaining
rank one.

A18.4.89 gives the correct replacement.  On the actual post-opening state,
either an honest active `2 x 2` Hessian chart exists, in which case A18.4.88
supplies complete rank-three geometry, or every `2 x 2` minor of the genuine
special-fibre Hessian vanishes.

The latter branch is strengthened here by retaining the first-contact Hessian
witness.  Therefore the special Hessian is nonzero as well as rank at most
one: it is a genuine rank-one rigidity endpoint which the next patch may
analyse projectively.  No repair-only rank promotion is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The all-minors-zero first-contact branch is genuinely rank one, not the
zero Hessian. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  firstContact : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source
  allTwoByTwo :
    (scaleAwareSpecialHessianFourBlock firstContact.opening).AllTwoByTwoMinorsZero
  specialHessian_ne_zero :
    HC4.Polynomial.hessian
      (polynomialFamilySpecialFiber firstContact.opening.family) ≠ 0

/-- Complete honest outcome of one zero-linear-jet saturated opening. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningRankFrontier
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | rankThree
      (firstContact : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source)
      (chart : AdaptiveAlignedSmithCanonicalExactActiveFourBlock firstContact.opening)
      (geometry : AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry chart complexity)
  | rankOne
      (geometry : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)

namespace AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry

/-- The retained diagonal/mixed first-contact witness makes the special Hessian
of the opening nonzero. -/
theorem specialHessian_ne_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source) :
    HC4.Polynomial.hessian
      (polynomialFamilySpecialFiber G.opening.family) ≠ 0 := by
  intro hzero
  cases G.hessianGeometry with
  | diagonal d hd hkernel hne =>
      apply hne
      have hentry := congrFun
        (congrFun hzero G.kernel) G.kernel
      simpa [HC4.Polynomial.hessian_apply] using hentry
  | mixed d hd j hjk hkernel hj hne =>
      apply hne
      have hentry := congrFun
        (congrFun hzero G.kernel) j
      simpa [HC4.Polynomial.hessian_apply] using hentry

/-- **Honest first-contact rank split.** -/
noncomputable def rankFrontier
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalKernelOpeningRankFrontier source complexity := by
  rcases scaleAwareHessian_exactActive_or_rankOne G.opening with hactive | hrankOne
  · rcases hactive with ⟨C⟩
    exact .rankThree G C (C.rankThreeGeometry complexity)
  · exact .rankOne {
      firstContact := G
      allTwoByTwo := hrankOne
      specialHessian_ne_zero := G.specialHessian_ne_zero
    }

end AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry

/-- Construct the complete first-contact geometry without attaching any repair
rank to it. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_completeGeometry_of_gradientAtZero
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source) := by
  let hq : 0 < saturatedKernelSlope kernel source.family hactive :=
    saturatedKernelSlope_pos kernel source.family hactive hfree
  let opening :=
    source.saturatedKernelOpeningState kernel hkernel hactive hq
  rcases specialFiber_saturatedKernelBlowup_active
      (K := K) kernel source.family hactive with ⟨d, hd, hdpos⟩
  have hdOpening :
      d ∈ (polynomialFamilySpecialFiber opening.family).support := by
    simpa [opening, hq,
      ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState] using hd
  have hlinearOpening :
      ∀ i : Fin 4,
        MvPolynomial.coeff (Finsupp.single i 1)
          (polynomialFamilySpecialFiber opening.family) = 0 := by
    intro i
    simpa [opening] using
      source.saturatedKernelOpeningState_specialFiber_linearCoeff_zero
        kernel hkernel hactive hq hgrad i
  let H := firstContactHessianGeometry_of_linearCoeff_zero
    (polynomialFamilySpecialFiber opening.family)
    hlinearOpening kernel d hdOpening hdpos
  exact ⟨{
    kernel := kernel
    kernel_ne := hkernel
    active := hactive
    source_free := hfree
    source_gradient_zero := hgrad
    slope_pos := hq
    opening := opening
    opening_eq := rfl
    exponent := d
    exponent_mem := hdOpening
    exponent_kernel_pos := hdpos
    hessianGeometry := H
  }⟩

/-- **Zero-gradient kernel-free opening: rank three or genuine rank one.**

This is the sound replacement for the old direct rank-two promotion theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_rankThree_or_rankOne_of_gradientAtZero
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningRankFrontier source complexity) := by
  rcases source.kernelFreeOpening_completeGeometry_of_gradientAtZero
      kernel hkernel hactive hfree hgrad with ⟨G⟩
  exact ⟨G.rankFrontier complexity⟩

end

end HC4.Valuation
