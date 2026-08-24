import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidMixedLayerCross
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTransverseKernelRestart
import Mathlib.Tactic

/-!
# Final assembly A17.3E: blocker-native right-recentered constant-kernel exit

The final rigid and zero-Schur branches both live on the same honest
right-recentered blocker source.  The older A17 constant-kernel exit was tied
to a rank-one closing carrier even though its actual source move only uses the
right-recentered family, its retained exact collision, the nonlinear degree
bound, and the zero source jet.

This file records that source-native interface once and for all.

* the retained zero source jet transports through the actual right recentering;
* hence the right-recentered special fibre has no linear source terms;
* any literal constant Hessian kernel therefore integrates to a zero
  directional derivative;
* a nonzero transverse component can be straightened by the existing three
  determinant-one source transvections;
* the resulting transverse-free special fibre gives the already-certified
  ramified raw-defect spend.

No new geometric alternative is introduced here.  This is the common exit
which the remaining rigid and zero-Schur kernel lifts can both consume.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## The blocker source really has zero right-recentered source jet -/

/-- The original zero source jet and the exact collision imply that the
right endpoint also has zero gradient.  Translating that endpoint to the
source origin therefore gives zero gradient at the origin of the honest
right-recentered family. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredFamily_gradientAtZero
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (i : Fin 4) :
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i B.aligned.endpoint.rightRecenteredFamily) = 0 := by
  let E := B.aligned.endpoint
  have horigin :
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i E.family) = 0 := by
    simpa [E] using B.aligned.zeroSourceJet.gradientAtZero i
  have hright :
      MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) = 0 := by
    calc
      MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) =
          MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i E.family) := by
              exact (E.exactCollision i).symm
      _ = 0 := horigin
  change
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i E.rightRecenteredFamily) = 0
  unfold AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily
  rw [pderiv_polynomialFamilyTranslationHom]
  calc
    MvPolynomial.eval
        (fun _ : Fin 4 => (0 : Polynomial K))
        (polynomialFamilyTranslationHom (K := K) E.movingSection
          (MvPolynomial.pderiv i E.family)) =
        MvPolynomial.eval E.movingSection
          (MvPolynomial.pderiv i E.family) := by
            simpa using
              (eval_polynomialFamilyTranslationHom_difference
                (K := K) E.movingSection E.movingSection
                (MvPolynomial.pderiv i E.family))
    _ = 0 := hright

/-- Consequently every source-linear coefficient of the honest
right-recentered special fibre vanishes. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredSpecialFiber_linearCoeff_zero
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (polynomialFamilySpecialFiber B.aligned.endpoint.rightRecenteredFamily) = 0 := by
  exact AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFiber_linearCoeff_zero_of_gradientAtZero
    B.aligned.endpoint.rightRecenteredFamily
    B.rightRecenteredFamily_gradientAtZero i

/-! ## Literal blocker-native constant kernel -/

/-- A literal constant kernel vector of the complete honest right-recentered
special-fibre Hessian, together with an actually nonzero transverse
coordinate. -/
structure AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Type _ where
  direction : Fin 4 → K
  direction_ne_zero : direction ≠ 0
  transverse : ∃ ell : Fin 4, ell ≠ (0 : Fin 4) ∧ direction ell ≠ 0
  kernel :
    (HC4.Polynomial.hessian
      (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily)).mulVec
      (fun i => MvPolynomial.C (direction i)) = 0

namespace AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-- The blocker-native literal Hessian kernel integrates once.  The only
possible integration constant is the linear source jet, which is zero by the
retained exact-collision provenance above. -/
theorem directionalDerivative_eq_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (D : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S) :
    constantSourceDirectionalDerivative
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily) D.direction = 0 := by
  let F := polynomialFamilySpecialFiber
    S.blocker.aligned.endpoint.rightRecenteredFamily
  let G := constantSourceDirectionalDerivative F D.direction

  have hp (r : Fin 4) : MvPolynomial.pderiv r G = 0 := by
    rw [show G = constantSourceDirectionalDerivative F D.direction by rfl]
    rw [pderiv_constantSourceDirectionalDerivative]
    exact congrFun D.kernel r

  have hconstant : G = MvPolynomial.C (MvPolynomial.coeff 0 G) := by
    exact finFour_eq_C_of_all_pderiv_eq_zero G
      (hp 0) (hp 1) (hp 2) (hp 3)

  have hlinear (i : Fin 4) :
      MvPolynomial.coeff 0 (MvPolynomial.pderiv i F) = 0 := by
    rw [coeff_pderiv_mixedDegree]
    simpa [F] using
      S.blocker.rightRecenteredSpecialFiber_linearCoeff_zero i

  have hA : MvPolynomial.coeff 0 (standardTwoZeroA F) = 0 := by
    change MvPolynomial.coeff 0 (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    exact hlinear (2 : Fin 4)
  have hC : MvPolynomial.coeff 0 (standardTwoZeroC F) = 0 := by
    change MvPolynomial.coeff 0 (MvPolynomial.pderiv (3 : Fin 4) F) = 0
    exact hlinear (3 : Fin 4)

  have hcoeff : MvPolynomial.coeff 0 G = 0 := by
    classical
    simp [G, constantSourceDirectionalDerivative, Fin.sum_univ_four,
      MvPolynomial.coeff_C_mul, hlinear, hA, hC]

  have hGzero : G = 0 := by
    rw [hconstant, hcoeff]
    simp
  simpa [G, F] using hGzero

end AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-! ## Honest source move after transverse straightening -/

/-- Constant embedding respects cancellation of a nonzero scalar
denominator. -/
private theorem rightRecentered_mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

/-- Once the three source shears make the right-recentered special fibre
`ell`-independent, the honest blocker source itself gives an absolute
ramified spend. -/
theorem exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
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
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
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

  have hdegree0 : NonlinearDegreeBound s.degreeCap E.rightRecenteredFamily := by
    exact E.rightRecenteredFamily_nonlinearDegreeBound
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

namespace AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-- **Blocker-native constant-kernel exit.**  A literal constant Hessian
kernel with a nonzero transverse coordinate always yields the certified
absolute ramified raw-defect spend. -/
theorem exists_ramifiedSpend
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (D : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases D.transverse with ⟨ell, hell0, hvell⟩
  let F := polynomialFamilySpecialFiber S.blocker.aligned.endpoint.rightRecenteredFamily
  have hdir := D.directionalDerivative_eq_zero
  change constantSourceDirectionalDerivative F D.direction = 0 at hdir

  fin_cases ell
  · exact False.elim (hell0 rfl)
  · let combo :=
      MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 1) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 1) *
          MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 1) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (1 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 1) =
            MvPolynomial.C (D.direction 0) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 1) =
            MvPolynomial.C (D.direction 2) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 1) =
            MvPolynomial.C (D.direction 3) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (1 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (1 : Fin 4)) *
                (MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 1) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 1) *
                    MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 1) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 0 / D.direction 1)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 2 / D.direction 1)) *
                  MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 3 / D.direction 1)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h2C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (1 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (1 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
            (D.direction 0 / D.direction 1)
            (D.direction 2 / D.direction 1)
            (D.direction 3 / D.direction 1) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
          (D.direction 0 / D.direction 1)
          (D.direction 2 / D.direction 1)
          (D.direction 3 / D.direction 1)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero
      S clock_eq
      (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 1)
      (D.direction 2 / D.direction 1)
      (D.direction 3 / D.direction 1) hp
  · let combo :=
      MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 2) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 2) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 2) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (2 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 2) =
            MvPolynomial.C (D.direction 0) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 2) =
            MvPolynomial.C (D.direction 1) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 2) =
            MvPolynomial.C (D.direction 3) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (2 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (2 : Fin 4)) *
                (MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 2) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 2) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 2) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 0 / D.direction 2)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 1 / D.direction 2)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 3 / D.direction 2)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h1C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (2 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (2 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
            (D.direction 0 / D.direction 2)
            (D.direction 1 / D.direction 2)
            (D.direction 3 / D.direction 2) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
          (D.direction 0 / D.direction 2)
          (D.direction 1 / D.direction 2)
          (D.direction 3 / D.direction 2)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero
      S clock_eq
      (2 : Fin 4) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 2)
      (D.direction 1 / D.direction 2)
      (D.direction 3 / D.direction 2) hp
  · let combo :=
      MvPolynomial.pderiv (3 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 3) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 3) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 3) *
          MvPolynomial.pderiv (2 : Fin 4) F
    have hv : D.direction (3 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 3) =
            MvPolynomial.C (D.direction 0) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 3) =
            MvPolynomial.C (D.direction 1) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 3) =
            MvPolynomial.C (D.direction 2) :=
        rightRecentered_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (3 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (3 : Fin 4)) *
                (MvPolynomial.pderiv (3 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 3) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 3) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 3) *
                    MvPolynomial.pderiv (2 : Fin 4) F) =
              MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 0 / D.direction 3)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 1 / D.direction 3)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 2 / D.direction 3)) *
                  MvPolynomial.pderiv 2 F := by ring
          _ = MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F := by
              rw [h0C, h1C, h2C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (3 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (3 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
            (D.direction 0 / D.direction 3)
            (D.direction 1 / D.direction 3)
            (D.direction 2 / D.direction 3) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (D.direction 0 / D.direction 3)
          (D.direction 1 / D.direction 3)
          (D.direction 2 / D.direction 3)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero
      S clock_eq
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 3)
      (D.direction 1 / D.direction 3)
      (D.direction 2 / D.direction 3) hp

end AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

end

end HC4.Valuation
