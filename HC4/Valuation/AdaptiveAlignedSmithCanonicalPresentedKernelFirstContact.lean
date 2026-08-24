import HC4.Valuation.AdaptiveAlignedSmithCanonicalConstantKernelFirstContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRationalNormalization
import Mathlib.Tactic

/-!
# A18.4.49: positive presented-blocker slopes retain first-contact geometry

The current presented-blocker rational normaliser of A18.4.33 starts from the
honest right-recentered family.  Its moving right section specialises to
`-e₀`, so that family is not itself a canonical scale-aware restart state.
A simultaneous source sign change fixes exactly this orientation without
changing the Hessian clock, degree bound, or collision geometry.

For a positive saturated slope, A18.4.41 first proves that the original
right-recentered special fibre is free of the chosen transverse coordinate.
That freeness is preserved by the sign pullback.  We may therefore invoke the
A18.4.46 first-contact mechanism on the signed, factor-one presented state.

The result is either honest same-scale progress at the already-presented scale
or a geometry-backed rank-two macro on the actual saturated-opening family.
No rational decrease is exported.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A nonlinear positive-kernel opening occurring after the signed
right-recentering of a presented blocker.  The local first-contact packet is
retained, and the final rank promotion is recorded as global progress from the
original pre-presentation source. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1) where
  signed : ScaleAwareAdaptiveGeometricRestartState (K := K)
  signedPresentation :
    CertifiedRamifiedEpisodeInternalMove signed D.presented
  signedFactorOne : signedPresentation.ramification = 1
  openingProgress :
    AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
      RR D.presented complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      openingProgress.openingProgress.target source

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- Simultaneous source sign change of the honest right-recentered blocker
family, recorded at the blocker's current absolute scale. -/
noncomputable def signedRightRecenteredState
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let E := D.blocker.aligned.endpoint
  let P := allSourceSignHom (R := Polynomial K) E.rightRecenteredFamily
  let b := polynomialSectionNegation (K := K) E.rightRecenteredRightSection
  have hdef : HasPolynomialFamilyHessianDefect (K := K) P E.defect := by
    dsimp [P]
    exact allSourceSignHom_preservesHessianDefect
      E.rightRecenteredFamily E.rightRecenteredFamily_hessianDefect
  have hdegree : NonlinearDegreeBound D.presented.degreeCap P := by
    dsimp [P]
    simpa using nonlinearDegreeBound_allSourceSignHom
      D.presented.degreeCap E.rightRecenteredFamily
      E.rightRecenteredFamily_nonlinearDegreeBound
  have hcollRaw :=
    polynomialFamilyExactGradientCollision_allSourceSign
      (K := K) E.rightRecenteredFamily
      (zeroPolynomialSection (K := K)) E.rightRecenteredRightSection
      E.rightRecenteredFamily_exactCollision
  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b := by
    simpa [P, b] using hcollRaw
  have hspecial0 := E.rightRecenteredRightSection_specialPoint
  have hspecial :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    have hi := congrFun hspecial0 i
    change Polynomial.constantCoeff (E.rightRecenteredRightSection i) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) i at hi
    change Polynomial.constantCoeff (-E.rightRecenteredRightSection i) =
      coordinateAxisPoint (K := K) (0 : Fin 4) i
    rw [map_neg, hi]
    simp
  exact {
    rawDefect := E.defect
    scale := D.presented.scale
    scale_pos := D.presented.scale_pos
    degreeCap := D.presented.degreeCap
    sourceComplexity := D.presented.sourceComplexity
    repair := D.presented.repair
    family := P
    movingSection := b
    hessianDefect := hdef
    nonlinearDegreeBound := hdegree
    exactCollision := hcoll
    sectionSpecial := hspecial
  }

/-- The signed right-recentered state is a factor-one presentation of the
already-presented blocker state. -/
noncomputable def signedRightRecenteredPresentation
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    CertifiedRamifiedEpisodeInternalMove D.signedRightRecenteredState D.presented where
  ramification := 1
  ramification_pos := by omega
  scale_eq := by simp [signedRightRecenteredState]
  raw_eq := by simpa [signedRightRecenteredState] using D.defect_eq
  degreeCap_eq := rfl
  sourceComplexity_eq := rfl
  repair_eq := rfl

/-- Kernel freeness of the original right-recentered special fibre survives
the simultaneous sign pullback. -/
theorem signedRightRecentered_specialFiber_free
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (kernel : Fin 4)
    (hfree :
      ∀ d ∈
          (polynomialFamilySpecialFiber
            D.blocker.aligned.endpoint.rightRecenteredFamily).support,
        d kernel = 0) :
    ∀ d ∈ (polynomialFamilySpecialFiber D.signedRightRecenteredState.family).support,
      d kernel = 0 := by
  let F := polynomialFamilySpecialFiber
    D.blocker.aligned.endpoint.rightRecenteredFamily
  have hp : MvPolynomial.pderiv kernel F = 0 := by
    apply pderiv_eq_zero_of_all_supported_exponents_zero
    intro d hd
    exact hfree d (MvPolynomial.mem_support_iff.mpr hd)
  have hsigned :
      MvPolynomial.pderiv kernel
        (polynomialFamilySpecialFiber D.signedRightRecenteredState.family) = 0 := by
    rw [show D.signedRightRecenteredState.family =
        allSourceSignHom (R := Polynomial K)
          D.blocker.aligned.endpoint.rightRecenteredFamily by rfl]
    rw [polynomialFamilySpecialFiber_allSourceSignHom]
    rw [pderiv_allSourceSignHom, hp]
    simp
  intro d hd
  exact exponent_eq_zero_of_pderiv_eq_zero
    kernel
    (polynomialFamilySpecialFiber D.signedRightRecenteredState.family)
    hsigned d (MvPolynomial.mem_support_iff.mp hd)

/-- **Positive rational slope on a presented blocker is first-contact
termination, not rational recursion.** -/
theorem positiveRecenteredSaturatedKernelSlope_sameScale_or_rankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily)
    (hq :
      0 < saturatedKernelSlope kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily hactive) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target D.presented) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankTwoProgress
          RR D complexity) := by
  let signed := D.signedRightRecenteredState
  let hmove := D.signedRightRecenteredPresentation
  have hfree0 :
      ∀ d ∈
          (polynomialFamilySpecialFiber
            D.blocker.aligned.endpoint.rightRecenteredFamily).support,
        d kernel = 0 :=
    specialFiber_free_of_saturatedKernelSlope_pos
      (K := K) kernel D.blocker.aligned.endpoint.rightRecenteredFamily hactive hq
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber signed.family).support,
        d kernel = 0 := by
    simpa [signed] using D.signedRightRecentered_specialFiber_free kernel hfree0
  have hactiveSigned : IsActiveKernelCoordinate kernel signed.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel signed.family signed.rawDefect signed.hessianDefect
  have hpresentedRepair : D.presented.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hpresent⟩
    rw [hpresent.repair_eq]
    exact hsrepair
  rcases D.presented.factorOneKernelFreePresentation_sameScale_or_rankTwoProgress
      RR D.presented signed complexity hpresentedRepair hmove rfl
      kernel hkernel hactiveSigned hfree with hstrict | hRankTwo
  · exact Or.inl hstrict
  · rcases hRankTwo with ⟨P⟩
    have hglobal :
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          P.openingProgress.target source := by
      unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
      apply Prod.Lex.left
      rw [P.openingProgress.target_eq]
      change RepairState.measure (rankTwoRepairState complexity) <
        RepairState.measure source.repair
      rw [hsrepair]
      exact repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)
    exact Or.inr ⟨{
      signed := signed
      signedPresentation := hmove
      signedFactorOne := rfl
      openingProgress := P
      globalProgress := hglobal
    }⟩

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
