import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedZeroLinearJetKernelOpening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalCurrentScaleFirstContact
import Mathlib.Tactic

/-!
# A18.4.69: current-scale triple-shear first contact is directly rank two

A18.4.47 retained an unramified same-scale alternative after straightening a
literal transverse constant Hessian kernel by three determinant-one source
shears and a simultaneous sign change.  The straightened family is one of the
canonical zero-gradient sources covered by A18.4.65.

The repository already proves that the honest right-recentered blocker family
has zero source gradient at the origin and that each transverse source shear
preserves this property.  Simultaneous source negation preserves it as well.
Hence the final straightened family has zero full source-linear jet, and its
kernel-free saturated first contact is always diagonal-or-mixed Hessian
geometry.  This file changes only the endpoint of the A18.4.47 construction:
there is now direct geometry-backed rank-two progress, with no same-scale
recursive alternative.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Strong zero-linear-jet replacement for the final helper of A18.4.47. -/
theorem currentScaleCompleteRankTwo_of_rightRecentered_tripleShear_pderiv_zero
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (ell k₁ k₂ k₃ : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (hk₁ : k₁ ≠ ell) (hk₂ : k₂ ≠ ell) (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (hpderiv :
      MvPolynomial.pderiv ell
        (tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃
          (polynomialFamilySpecialFiber
            S.blocker.aligned.endpoint.rightRecenteredFamily)) = 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR s complexity) := by
  let E := S.blocker.aligned.endpoint
  let Pshear := tripleTransverseSourceShearFamily
    k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredFamily
  let bshear := tripleTransverseSourceUnshearSection
    k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredRightSection
  let Psign := allSourceSignHom (R := Polynomial K) Pshear
  let bsign := polynomialSectionNegation (K := K) bshear

  have hdefShear :
      HasPolynomialFamilyHessianDefect (K := K) Pshear E.defect := by
    dsimp [Pshear]
    exact tripleTransverseSourceShearFamily_preservesHessianDefect
      k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
      E.rightRecenteredFamily E.rightRecenteredFamily_hessianDefect
  have hdefSign :
      HasPolynomialFamilyHessianDefect (K := K) Psign E.defect := by
    dsimp [Psign]
    exact allSourceSignHom_preservesHessianDefect Pshear hdefShear

  have hdegree0 : NonlinearDegreeBound s.degreeCap E.rightRecenteredFamily :=
    E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegree1 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁)
          E.rightRecenteredFamily) :=
    nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₁ ell (Polynomial.C a₁) E.rightRecenteredFamily hdegree0
  have hdegree2 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
          (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁)
            E.rightRecenteredFamily)) :=
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
      E.rightRecenteredFamily E.rightRecenteredRightSection
        E.rightRecenteredFamily_exactCollision
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
          (polynomialFamilySpecialFiber E.rightRecenteredFamily) := by
    dsimp [Pshear]
    exact polynomialFamilySpecialFiber_tripleTransverseSourceShearFamily
      k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredFamily
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

  let presented : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := E.defect
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Psign
      movingSection := bsign
      hessianDefect := hdefSign
      nonlinearDegreeBound := hdegreeSign
      exactCollision := hcollSign
      sectionSpecial := hspecialSign }

  have hmove : CertifiedRamifiedEpisodeInternalMove presented s := {
    ramification := 1
    ramification_pos := by omega
    scale_eq := by simp [presented]
    raw_eq := by simpa [presented, E] using clock_eq
    degreeCap_eq := rfl
    sourceComplexity_eq := rfl
    repair_eq := rfl
  }
  have hactive : IsActiveKernelCoordinate ell presented.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) ell presented.family presented.rawDefect presented.hessianDefect

  have hbaseGrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i E.rightRecenteredFamily) = 0 :=
    S.blocker.rightRecenteredFamily_gradientAtZero
  have hshearGrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i Pshear) = 0 := by
    simpa [Pshear] using
      gradientAtZero_tripleTransverseSourceShear
        k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
        E.rightRecenteredFamily hbaseGrad
  have hsignGrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i Psign) = 0 := by
    simpa [Psign] using gradientAtZero_allSourceSignHom Pshear hshearGrad
  have hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i presented.family) = 0 := by
    simpa [presented] using hsignGrad

  exact s.presentedKernelFree_rankTwoProgress_of_gradientAtZero
    RR presented complexity hsrepair ⟨hmove⟩ ell hell0 hactive
    (by simpa [presented] using hfree) hgrad

end

end HC4.Valuation
