import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyConstantKernelTransverse
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingTransverseAlignment
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingEarlierWallClock
import HC4.Valuation.AdaptiveAlignedSmithStationaryPointedFamilyReflection
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import Mathlib.Tactic

/-!
# Final assembly A17.1: transverse constant kernel gives an honest ramified spend

A16 recovers a literal nonzero constant Hessian-kernel direction of the honest
right-recentered special fibre and proves that this direction has a genuine
transverse component.  This file performs the source-honest restart which that
certificate was designed for.

For a transverse coordinate `ell` on which the kernel vector is nonzero, the
three already-green marked-axis-preserving transvections straighten the
constant directional derivative to the coordinate derivative `pderiv ell`.
Consequently the transformed special fibre is independent of `X_ell`.

We then use the saturated first-contact construction in that arbitrary
transverse coordinate.  The construction is recorded directly at the absolute
scale of the incoming scale-aware state, so the strict raw-clock loss composes
with the aligned-Smith ramified presentation.  No residual RS2 constructor is
left and no JC2 input occurs.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Special fibre of a constant source transvection -/

@[simp] theorem transverseSourceShearHomBase_C
    (k ell : Fin 4) (a c : K) :
    transverseSourceShearHomBase k ell a (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [transverseSourceShearHomBase]

@[simp] theorem transverseSourceShearHomBase_X
    (k ell : Fin 4) (a : K) (i : Fin 4) :
    transverseSourceShearHomBase k ell a (MvPolynomial.X i) =
      transverseSourceShearVariableBase k ell a i := by
  simp [transverseSourceShearHomBase]

/-- Taking the parameter-constant fibre commutes with a source transvection
whose coefficient is parameter-constant. -/
theorem polynomialFamilySpecialFiber_transverseSourceShearHom_constant
    (k ell : Fin 4) (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P) =
      transverseSourceShearHomBase k ell a
        (polynomialFamilySpecialFiber P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [polynomialFamilySpecialFiber, transverseSourceShearHomBase]
  · intro p q hp hq
    simpa [polynomialFamilySpecialFiber, map_add] using
      congrArg₂ (fun x y => x + y) hp hq
  · intro p i hp
    have hvar :
        polynomialFamilySpecialFiber
            (transverseSourceShearHom (K := K) k ell (Polynomial.C a)
              (MvPolynomial.X i)) =
          transverseSourceShearHomBase k ell a
            (polynomialFamilySpecialFiber (MvPolynomial.X i)) := by
      by_cases hi : i = k
      · subst i
        simp [polynomialFamilySpecialFiber, transverseSourceShearVariable,
          transverseSourceShearVariableBase]
      · simp [polynomialFamilySpecialFiber, transverseSourceShearVariable,
          transverseSourceShearVariableBase, hi]
    have hmul := congrArg₂ (fun x y => x * y) hp hvar
    simpa [polynomialFamilySpecialFiber, map_mul] using hmul

/-- The same commutation for the canonical three-transvection package. -/
theorem polynomialFamilySpecialFiber_tripleTransverseSourceShearFamily
    (k₁ k₂ k₃ ell : Fin 4) (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    polynomialFamilySpecialFiber
        (tripleTransverseSourceShearFamily
          k₁ k₂ k₃ ell a₁ a₂ a₃ P) =
      tripleTransverseSourceShearFamilyBase
        k₁ k₂ k₃ ell a₁ a₂ a₃
        (polynomialFamilySpecialFiber P) := by
  simp [tripleTransverseSourceShearFamily,
    tripleTransverseSourceShearFamilyBase,
    polynomialFamilySpecialFiber_transverseSourceShearHom_constant]

/-! ## Residue-field chain rule -/

/-- Away from the added direction, the residue-field transvection has the
identity chain rule. -/
theorem pderiv_transverseSourceShearHomBase_of_ne_source
    (k ell : Fin 4) (hkl : k ≠ ell) (a : K)
    (j : Fin 4) (hjl : j ≠ ell)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv j (transverseSourceShearHomBase k ell a P) =
      transverseSourceShearHomBase k ell a (MvPolynomial.pderiv j P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp only [map_mul, transverseSourceShearHomBase_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnk : n = k
    · subst n
      by_cases hkj : k = j
      · subst j
        simp [transverseSourceShearVariableBase, hkl] <;> ring
      · have hjk : j ≠ k := Ne.symm hkj
        simp [transverseSourceShearVariableBase,
          hkl, hkj, hjk, hjl] <;> ring
    · by_cases hnj : n = j
      · subst n
        have hjk : j ≠ k := by
          intro h
          exact hnk h
        simp [transverseSourceShearVariableBase, hnk, hjk, hjl] <;> ring
      · have hjn : j ≠ n := Ne.symm hnj
        simp [transverseSourceShearVariableBase,
          hnk, hnj, hjn, hjl] <;> ring

/-- In the added direction `ell`, one transvection adds the expected
`k`-directional derivative. -/
theorem pderiv_source_transverseSourceShearHomBase
    (k ell : Fin 4) (hkl : k ≠ ell) (a : K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv ell (transverseSourceShearHomBase k ell a P) =
      transverseSourceShearHomBase k ell a (MvPolynomial.pderiv ell P) +
        MvPolynomial.C a *
          transverseSourceShearHomBase k ell a (MvPolynomial.pderiv k P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp
  · intro p q hp hq
    simp [hp, hq, mul_add, add_mul] <;> ring
  · intro p n hp
    simp only [map_mul, transverseSourceShearHomBase_X,
      MvPolynomial.pderiv_mul, map_add, hp]
    by_cases hnl : n = ell
    · subst n
      have hlk : ell ≠ k := Ne.symm hkl
      simp [transverseSourceShearVariableBase, hkl, hlk]
      ring
    · by_cases hnk : n = k
      · subst n
        have hlk : ell ≠ k := Ne.symm hkl
        simp [transverseSourceShearVariableBase, hkl, hlk]
        ring
      · have hln : ell ≠ n := Ne.symm hnl
        simp [transverseSourceShearVariableBase, hnl, hln, hnk, hkl]
        ring

/-- Exact derivative formula for the canonical three transvections with a
common added direction. -/
theorem pderiv_source_tripleTransverseSourceShearFamilyBase
    (k₁ k₂ k₃ ell : Fin 4)
    (hk₁ : k₁ ≠ ell) (hk₂ : k₂ ≠ ell) (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv ell
        (tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃ P) =
      tripleTransverseSourceShearFamilyBase
        k₁ k₂ k₃ ell a₁ a₂ a₃
        (MvPolynomial.pderiv ell P +
          MvPolynomial.C a₁ * MvPolynomial.pderiv k₁ P +
          MvPolynomial.C a₂ * MvPolynomial.pderiv k₂ P +
          MvPolynomial.C a₃ * MvPolynomial.pderiv k₃ P) := by
  unfold tripleTransverseSourceShearFamilyBase
  rw [pderiv_source_transverseSourceShearHomBase k₃ ell hk₃]
  rw [pderiv_source_transverseSourceShearHomBase k₂ ell hk₂]
  rw [pderiv_source_transverseSourceShearHomBase k₁ ell hk₁]
  rw [pderiv_transverseSourceShearHomBase_of_ne_source
    k₁ ell hk₁ a₁ k₂ hk₂]
  rw [pderiv_transverseSourceShearHomBase_of_ne_source
    k₂ ell hk₂ a₂ k₃ hk₃]
  rw [pderiv_transverseSourceShearHomBase_of_ne_source
    k₁ ell hk₁ a₁ k₃ hk₃]
  simp only [map_add, map_mul, transverseSourceShearHomBase_C]

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Generic arbitrary-transverse kernel-free spend at absolute scale -/

/-- A scale-aware state whose special fibre is independent of an unmarked
coordinate has an honest ramified raw-defect spend in that same coordinate.
This is the coordinate-generic, absolute-scale version of
`AdaptiveKernelFreeFixedScaleProgress`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_certifiedRamifiedRawDefectSpend_of_specialFiber_free
    (a : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber a.family).support,
        d kernel = 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target a := by
  let hactive :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel a.family a.rawDefect a.hessianDefect
  let R := kernelSlopeDenominatorClearingRamification kernel a.family
  let q := saturatedKernelSlope kernel a.family hactive
  let Pram := parameterRamificationFamily (K := K) R a.family
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel a.family hactive
  let Pnext := integralKernelBlowupFamily kernel q Pram hdiv
  let bram := parameterRamificationSection (K := K) R a.movingSection
  let bnext := kernelBlowupSection kernel q bram

  have hRpos : 0 < R := by
    dsimp [R]
    exact kernelSlopeDenominatorClearingRamification_pos kernel a.family
  have hqpos : 0 < q := by
    dsimp [q]
    exact saturatedKernelSlope_pos kernel a.family hactive hfree

  have hcollisionRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K))) bram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      R a.family (zeroPolynomialSection (K := K)) a.movingSection
      a.exactCollision
  have hcollisionNextRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q Pram hdiv
      (parameterRamificationSection (K := K) R
        (zeroPolynomialSection (K := K))) bram hcollisionRam
  have hzeroSection :
      kernelBlowupSection kernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [kernelBlowupSection, parameterRamificationSection,
      parameterRamificationHom, zeroPolynomialSection]
  have hcollisionNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    rw [hzeroSection] at hcollisionNextRaw
    simpa [Pnext, bnext] using hcollisionNextRaw

  have hdefRam :
      HasPolynomialFamilyHessianDefect (K := K) Pram (R * a.rawDefect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R a.rawDefect a.family a.hessianDefect
  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (R * a.rawDefect - 2 * q) := by
    dsimp [Pnext]
    exact integralKernelBlowup_hasHessianDefect_sub
      kernel q (R * a.rawDefect) Pram hdiv hdefRam

  have hdegreeRam : NonlinearDegreeBound a.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      a.degreeCap R a.family a.nonlinearDegreeBound
  have hdegreeNext : NonlinearDegreeBound a.degreeCap Pnext := by
    dsimp [Pnext]
    exact nonlinearDegreeBound_integralKernelBlowup
      a.degreeCap q kernel Pram hdegreeRam hdiv

  have hspecialRam :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos a.movingSection]
    exact a.sectionSpecial
  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hqpos bram]
      simp [coordinateAxisPoint, hkernel]
    · rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q bram hi]
      exact congrFun hspecialRam i

  have hcost : 2 * q ≤ R * a.rawDefect := by
    exact two_mul_slope_le_of_integralKernelBlowup
      kernel q (R * a.rawDefect) Pram hdiv hdefRam
  have hraw : R * a.rawDefect - 2 * q < R * a.rawDefect := by
    omega

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * a.rawDefect - 2 * q
      scale := R * a.scale
      scale_pos := Nat.mul_pos hRpos a.scale_pos
      degreeCap := a.degreeCap
      sourceComplexity := a.sourceComplexity
      repair := a.repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefNext
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollisionNext
      sectionSpecial := hspecialNext }

  refine ⟨target, ?_⟩
  change Nonempty (CertifiedRamifiedRawDefectSpend target a)
  exact ⟨{
    ramification := R
    ramification_pos := hRpos
    scale_eq := rfl
    raw_lt := by simpa [target] using hraw
  }⟩

/-- Constant embedding respects cancellation of a nonzero scalar denominator. -/
private theorem mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

/-! ## A16 literal constant kernel -> A17 strict spend -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Helper: once the three source shears have made the special fibre
`ell`-independent, the resulting honest source presentation gives an absolute
ramified spend from the original pre-alignment state. -/
theorem exists_ramifiedSpend_of_tripleShear_pderiv_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
    (ell k₁ k₂ k₃ : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (hk₁ : k₁ ≠ ell) (hk₂ : k₂ ≠ ell) (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (hpderiv :
      MvPolynomial.pderiv ell
        (tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃
          (polynomialFamilySpecialFiber C.family)) = 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  let E := S.blocker.aligned.endpoint
  let Pshear := tripleTransverseSourceShearFamily
    k₁ k₂ k₃ ell a₁ a₂ a₃ C.family
  let bshear := tripleTransverseSourceUnshearSection
    k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredRightSection
  let Psign := allSourceSignHom (R := Polynomial K) Pshear
  let bsign := polynomialSectionNegation (K := K) bshear

  have hdefShear :
      HasPolynomialFamilyHessianDefect (K := K) Pshear E.defect := by
    dsimp [Pshear]
    exact tripleTransverseSourceShearFamily_preservesHessianDefect
      k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
      C.family C.family_hessianDefect
  have hdefSign :
      HasPolynomialFamilyHessianDefect (K := K) Psign E.defect := by
    dsimp [Psign]
    exact allSourceSignHom_preservesHessianDefect Pshear hdefShear

  have hdegree0 : NonlinearDegreeBound s.degreeCap C.family := by
    change NonlinearDegreeBound s.degreeCap E.rightRecenteredFamily
    exact E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegree1 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) C.family) :=
    nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₁ ell (Polynomial.C a₁) C.family hdegree0
  have hdegree2 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
          (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) C.family)) :=
    nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₂ ell (Polynomial.C a₂) _ hdegree1
  have hdegreeShear : NonlinearDegreeBound s.degreeCap Pshear := by
    dsimp [Pshear, tripleTransverseSourceShearFamily]
    exact nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₃ ell (Polynomial.C a₃) _ hdegree2
  have hdegreeSign : NonlinearDegreeBound s.degreeCap Psign := by
    dsimp [Psign]
    exact nonlinearDegreeBound_allSourceSignHom s.degreeCap Pshear hdegreeShear

  have hcollShear :
      HasPolynomialFamilyExactGradientCollision
        Pshear (zeroPolynomialSection (K := K)) bshear := by
    dsimp [Pshear, bshear]
    exact polynomialFamilyExactGradientCollision_tripleTransverseSourceShear
      k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
      C.family E.rightRecenteredRightSection C.family_exactCollision
  have hcollSignRaw :=
    polynomialFamilyExactGradientCollision_allSourceSign
      (K := K) Pshear (zeroPolynomialSection (K := K)) bshear hcollShear
  have hcollSign :
      HasPolynomialFamilyExactGradientCollision
        Psign (zeroPolynomialSection (K := K)) bsign := by
    simpa [Psign, bsign] using hcollSignRaw

  have hspecialShear :
      polynomialSectionSpecialPoint bshear =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    dsimp [bshear]
    exact polynomialSectionSpecialPoint_tripleTransverseUnshear_negAxis
      k₁ k₂ k₃ ell hell0 a₁ a₂ a₃ E.rightRecenteredRightSection
      E.rightRecenteredRightSection_specialPoint
  have hspecialSign :
      polynomialSectionSpecialPoint bsign =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    have hi := congrFun hspecialShear i
    change Polynomial.constantCoeff (bshear i) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) i at hi
    change Polynomial.constantCoeff (-bshear i) =
      coordinateAxisPoint (K := K) (0 : Fin 4) i
    rw [map_neg, hi]
    simp

  have hspecialFiberShear :
      polynomialFamilySpecialFiber Pshear =
        tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃
          (polynomialFamilySpecialFiber C.family) := by
    dsimp [Pshear]
    exact polynomialFamilySpecialFiber_tripleTransverseSourceShearFamily
      k₁ k₂ k₃ ell a₁ a₂ a₃ C.family
  have hpderivSign :
      MvPolynomial.pderiv ell (polynomialFamilySpecialFiber Psign) = 0 := by
    dsimp [Psign]
    rw [polynomialFamilySpecialFiber_allSourceSignHom]
    rw [pderiv_allSourceSignHom]
    rw [hspecialFiberShear, hpderiv]
    simp
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber Psign).support,
        d ell = 0 := by
    intro d hd
    exact exponent_eq_zero_of_pderiv_eq_zero
      ell (polynomialFamilySpecialFiber Psign) hpderivSign d
      (MvPolynomial.mem_support_iff.mp hd)

  let outer : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := E.defect
      scale := alignedSmithRamificationIndex * s.scale
      scale_pos := Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Psign
      movingSection := bsign
      hessianDefect := hdefSign
      nonlinearDegreeBound := hdegreeSign
      exactCollision := hcollSign
      sectionSpecial := hspecialSign }

  have hmove : HasCertifiedRamifiedEpisodeInternalMove outer s := by
    change Nonempty (CertifiedRamifiedEpisodeInternalMove outer s)
    exact ⟨{
      ramification := alignedSmithRamificationIndex
      ramification_pos := alignedSmithRamificationIndex_pos
      scale_eq := rfl
      raw_eq := by simpa [outer, E] using clock_eq
      degreeCap_eq := rfl
      sourceComplexity_eq := rfl
      repair_eq := rfl
    }⟩

  rcases outer.exists_certifiedRamifiedRawDefectSpend_of_specialFiber_free
      ell hell0 (by simpa [outer] using hfree) with ⟨target, hspend⟩
  exact ⟨target, hmove.then_spend hspend⟩

/-- **A17 RS2 elimination.**

A16's literal constant special-fibre kernel with a nonzero transverse
component always gives an honest absolute-scale ramified spend. -/
theorem AdaptiveAlignedSmithConstantRS2TransverseKernelData.exists_ramifiedSpend
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (D : AdaptiveAlignedSmithConstantRS2TransverseKernelData S) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases D.transverse with ⟨ell, hell0, hvell⟩
  let F := polynomialFamilySpecialFiber D.carrier.family
  have hdir := D.kernel.directionalDerivative_eq_zero
  change constantSourceDirectionalDerivative F D.kernel.direction = 0 at hdir

  fin_cases ell
  · exact False.elim (hell0 rfl)
  · let combo :=
      MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 1) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 1) *
          MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 1) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.kernel.direction (1 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.kernel.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 1) =
            MvPolynomial.C (D.kernel.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.kernel.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 1) =
            MvPolynomial.C (D.kernel.direction 2) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.kernel.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 1) =
            MvPolynomial.C (D.kernel.direction 3) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.kernel.direction (1 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.kernel.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.kernel.direction (1 : Fin 4)) *
                (MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 1) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 1) *
                    MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 1) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.kernel.direction 1) * MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.kernel.direction 1) *
                    MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 1)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.kernel.direction 1) *
                    MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 1)) *
                  MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.kernel.direction 1) *
                    MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 1)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.kernel.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.kernel.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.kernel.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.kernel.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h2C, h3C]
          _ = constantSourceDirectionalDerivative F D.kernel.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.kernel.direction (1 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (1 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
            (D.kernel.direction 0 / D.kernel.direction 1)
            (D.kernel.direction 2 / D.kernel.direction 1)
            (D.kernel.direction 3 / D.kernel.direction 1) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
          (D.kernel.direction 0 / D.kernel.direction 1)
          (D.kernel.direction 2 / D.kernel.direction 1)
          (D.kernel.direction 3 / D.kernel.direction 1)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq D.carrier
      (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.kernel.direction 0 / D.kernel.direction 1)
      (D.kernel.direction 2 / D.kernel.direction 1)
      (D.kernel.direction 3 / D.kernel.direction 1) hp
  · let combo :=
      MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 2) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 2) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 2) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.kernel.direction (2 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.kernel.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 2) =
            MvPolynomial.C (D.kernel.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.kernel.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 2) =
            MvPolynomial.C (D.kernel.direction 1) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.kernel.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 2) =
            MvPolynomial.C (D.kernel.direction 3) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.kernel.direction (2 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.kernel.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.kernel.direction (2 : Fin 4)) *
                (MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 2) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 2) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 2) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.kernel.direction 2) * MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.kernel.direction 2) *
                    MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 2)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.kernel.direction 2) *
                    MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 2)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.kernel.direction 2) *
                    MvPolynomial.C (D.kernel.direction 3 / D.kernel.direction 2)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.kernel.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.kernel.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.kernel.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.kernel.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h1C, h3C]
          _ = constantSourceDirectionalDerivative F D.kernel.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.kernel.direction (2 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (2 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
            (D.kernel.direction 0 / D.kernel.direction 2)
            (D.kernel.direction 1 / D.kernel.direction 2)
            (D.kernel.direction 3 / D.kernel.direction 2) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
          (D.kernel.direction 0 / D.kernel.direction 2)
          (D.kernel.direction 1 / D.kernel.direction 2)
          (D.kernel.direction 3 / D.kernel.direction 2)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq D.carrier
      (2 : Fin 4) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.kernel.direction 0 / D.kernel.direction 2)
      (D.kernel.direction 1 / D.kernel.direction 2)
      (D.kernel.direction 3 / D.kernel.direction 2) hp
  · let combo :=
      MvPolynomial.pderiv (3 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 3) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 3) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 3) *
          MvPolynomial.pderiv (2 : Fin 4) F
    have hv : D.kernel.direction (3 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.kernel.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 3) =
            MvPolynomial.C (D.kernel.direction 0) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.kernel.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 3) =
            MvPolynomial.C (D.kernel.direction 1) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.kernel.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 3) =
            MvPolynomial.C (D.kernel.direction 2) :=
        mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.kernel.direction (3 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.kernel.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.kernel.direction (3 : Fin 4)) *
                (MvPolynomial.pderiv (3 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 3) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 3) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 3) *
                    MvPolynomial.pderiv (2 : Fin 4) F) =
              MvPolynomial.C (D.kernel.direction 3) * MvPolynomial.pderiv 3 F +
                (MvPolynomial.C (D.kernel.direction 3) *
                    MvPolynomial.C (D.kernel.direction 0 / D.kernel.direction 3)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.kernel.direction 3) *
                    MvPolynomial.C (D.kernel.direction 1 / D.kernel.direction 3)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.kernel.direction 3) *
                    MvPolynomial.C (D.kernel.direction 2 / D.kernel.direction 3)) *
                  MvPolynomial.pderiv 2 F := by ring
          _ = MvPolynomial.C (D.kernel.direction 3) * MvPolynomial.pderiv 3 F +
                MvPolynomial.C (D.kernel.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.kernel.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.kernel.direction 2) * MvPolynomial.pderiv 2 F := by
              rw [h0C, h1C, h2C]
          _ = constantSourceDirectionalDerivative F D.kernel.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.kernel.direction (3 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (3 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
            (D.kernel.direction 0 / D.kernel.direction 3)
            (D.kernel.direction 1 / D.kernel.direction 3)
            (D.kernel.direction 2 / D.kernel.direction 3) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (D.kernel.direction 0 / D.kernel.direction 3)
          (D.kernel.direction 1 / D.kernel.direction 3)
          (D.kernel.direction 2 / D.kernel.direction 3)) hcombo
    exact exists_ramifiedSpend_of_tripleShear_pderiv_zero
      S clock_eq D.carrier
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.kernel.direction 0 / D.kernel.direction 3)
      (D.kernel.direction 1 / D.kernel.direction 3)
      (D.kernel.direction 2 / D.kernel.direction 3) hp

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- Outer-namespace wrapper used by the A17 frontier compression. -/
theorem AdaptiveAlignedSmithConstantRS2TransverseKernelData.exists_ramifiedSpend_absolute
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (D : AdaptiveAlignedSmithConstantRS2TransverseKernelData S) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s :=
  AdaptiveAlignedSmithRankOneClosingSourceCarrier.AdaptiveAlignedSmithConstantRS2TransverseKernelData.exists_ramifiedSpend
    S clock_eq D

end

end HC4.Valuation
