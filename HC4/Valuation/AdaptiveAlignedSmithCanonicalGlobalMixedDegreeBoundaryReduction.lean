import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalResidualOriginSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectReentry
import HC4.Valuation.SeparatedRightWallScaleDescent
import Mathlib.Tactic

/-!
# A18.4.16: mixed-degree aligned-boundary geometric reduction

A18.4.15 exposes the literal origin of every residual repeated-boundary and
boundary-then-legacy presentation.  The aligned-boundary origin must now be
consumed without reintroducing the obsolete global-homogeneity hypothesis.

The separated-right-wall descent developed earlier is geometric: after an
integral Smith move it extracts a common parameter factor and lowers the
Hessian determinant clock by `4` in the ten-aligned case or by `2` in the
odd-`w` case.  Ordinary homogeneity was used there only to show that the
constructed successor stayed in the old homogeneous state space.

For the current adaptive state space the required invariant is instead
`NonlinearDegreeBound`.  Every operation used by that descent already has a
degree-cap preservation theorem.  This file therefore repeats only the final
packaging with the correct mixed-degree invariant.

Consequently every actual aligned section boundary has the source-honest
trichotomy

* primitive zero Smith source;
* a genuine same-scale strict raw-defect exit;
* a coupled coefficient/right-section wall.

No coupled-wall impossibility theorem is used here: the old theorem assumes
global homogeneity, so the coupled mixed-degree case is retained explicitly
for the next closure step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Mixed-degree separated-wall descent -/

/-- Ten-aligned separated right wall gives the same geometric drop
`Delta -> Delta - 4` while preserving only the adaptive nonlinear degree cap.
No ordinary source homogeneity is required. -/
theorem tenAlignedSeparatedRightWall_strictAdaptiveRestart
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdegree : NonlinearDegreeBound degreeCap P)
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (m : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        10 * m) :
    ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
      ∃ b' : Fin 4 → Polynomial K,
        HasPolynomialFamilyHessianDefect (K := K) P' (Delta - 4) ∧
        NonlinearDegreeBound degreeCap P' ∧
        HasPolynomialFamilyExactGradientCollision
          P' (zeroPolynomialSection (K := K)) b' ∧
        polynomialSectionSpecialPoint b' =
          coordinateAxisPoint (K := K) (0 : Fin 4) ∧
        Delta - 4 < Delta := by
  let hPdiv :=
    tenAlignedSeparatedRightWall_unramifiedCoefficientDivisibility
      P b hwall hnotCoeff hnoPrimitive hsection hb m hN
  let haDiv :=
    zeroPolynomialSection_smithDivisibility
      (K := K) m
  let hbDiv :=
    tenAlignedSeparatedRightWall_unramifiedSectionDivisibility
      P b hwall m hN
  let Q := integralSmithConformalFamily m m P hPdiv
  let aQ :=
    integralSmithConformalSection
      m m (zeroPolynomialSection (K := K)) haDiv
  let bQ := integralSmithConformalSection m m b hbDiv
  have hQdegree : NonlinearDegreeBound degreeCap Q := by
    dsimp [Q]
    exact nonlinearDegreeBound_integralSmithConformal
      degreeCap m m P hdegree hPdiv
  have hQdef :
      HasPolynomialFamilyHessianDefect (K := K) Q Delta :=
    integralSmithConformalFamily_preservesHessianDefect
      m m Delta P hPdiv hdef
  have hQcollRaw :
      HasPolynomialFamilyExactGradientCollision Q aQ bQ :=
    polynomialFamilyExactGradientCollision_integralSmithConformal
      m m P hPdiv
      (zeroPolynomialSection (K := K)) b
      haDiv hbDiv hcoll
  have haQ : aQ = zeroPolynomialSection (K := K) := by
    dsimp [aQ]
    exact integralSmithConformalSection_zeroPolynomialSection m haDiv
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q (zeroPolynomialSection (K := K)) bQ := by
    rw [← haQ]
    exact hQcollRaw
  have hbQ0 : polynomialSectionSpecialPoint bQ 0 = 1 := by
    have hzero :=
      integralSmithConformalSection_zeroCoordinate
        (K := K) m b hbDiv
    have hb0 := congrFun hb (0 : Fin 4)
    have hb0' : Polynomial.constantCoeff (b 0) = 1 := by
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hb0
    change
      Polynomial.constantCoeff
        (integralSmithConformalSection m m b hbDiv 0) = 1
    rw [hzero]
    exact hb0'
  let hcommon :=
    tenAlignedSeparatedRightWall_unramifiedCommonFactor_one
      P b hwall hnotCoeff hnoPrimitive hsection hb
      m hN hPdiv
  let R := commonParameterFactorFamily 1 Q hcommon
  have hRdegree : NonlinearDegreeBound degreeCap R := by
    dsimp [R]
    exact nonlinearDegreeBound_commonParameterFactor
      degreeCap 1 Q hQdegree hcommon
  have hRdef :
      HasPolynomialFamilyHessianDefect (K := K) R (Delta - 4) :=
    commonParameterFactor_one_hasHessianDefect_sub_four
      Q hcommon Delta hQdef
  have hRcoll :
      HasPolynomialFamilyExactGradientCollision
        R (zeroPolynomialSection (K := K)) bQ :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      1 Q hcommon
      (zeroPolynomialSection (K := K)) bQ hQcoll
  have hbudget : 4 ≤ Delta :=
    four_le_defect_of_commonParameterFactor_one
      Q hcommon Delta hQdef
  let R' := pointedShearNormalisedFamily R bQ
  let b' := pointedShearNormalisedSection bQ
  refine ⟨R', b', ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R']
    exact pointedShearNormalisedFamily_preservesHessianDefect
      R bQ hRdef
  · dsimp [R']
    exact nonlinearDegreeBound_pointedShearNormalisedFamily
      degreeCap R bQ hRdegree
  · dsimp [R', b']
    exact pointedShearNormalisedFamily_preservesExactCollision
      R bQ hRcoll
  · dsimp [b']
    exact pointedShearNormalisedSection_specialPoint bQ hbQ0
  · omega

/-- Odd-`w` separated right wall gives the same geometric drop
`Delta -> Delta - 2` while preserving only the adaptive nonlinear degree cap.
No ordinary source homogeneity is required. -/
theorem oddWSeparatedRightWall_strictAdaptiveRestart
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdegree : NonlinearDegreeBound degreeCap P)
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hnotCoeff :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∉
        alignedSmithCoefficientWalls P)
    (hnoPrimitive :
      ¬ HasPrimitiveZeroSmithSource P)
    (hsection :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall ∈
        alignedSmithSectionWalls b)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (l : ℕ)
    (hN :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall =
        5 * (2 * l + 1))
    (hwstep :
      alignedSmithSectionWallStep (3 : Fin 4) (b 3) =
        alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) b hwall) :
    ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
      ∃ b' : Fin 4 → Polynomial K,
        HasPolynomialFamilyHessianDefect (K := K) P' (Delta - 2) ∧
        NonlinearDegreeBound degreeCap P' ∧
        HasPolynomialFamilyExactGradientCollision
          P' (zeroPolynomialSection (K := K)) b' ∧
        polynomialSectionSpecialPoint b' =
          coordinateAxisPoint (K := K) (0 : Fin 4) ∧
        Delta - 2 < Delta := by
  let hPdiv :=
    oddWSeparatedRightWall_smallSmithCoefficientDivisibility
      P b hwall hnotCoeff hnoPrimitive hsection hb l hN
  let haDiv :=
    zeroPolynomialSection_smithDivisibility
      (K := K) l
  let hbDiv :=
    oddWSeparatedRightWall_smallSmithSectionDivisibility
      P b hwall l hN
  let S := integralSmithConformalFamily l l P hPdiv
  let aS :=
    integralSmithConformalSection
      l l (zeroPolynomialSection (K := K)) haDiv
  let bS := integralSmithConformalSection l l b hbDiv
  have hSdegree : NonlinearDegreeBound degreeCap S := by
    dsimp [S]
    exact nonlinearDegreeBound_integralSmithConformal
      degreeCap l l P hdegree hPdiv
  have hSdef :
      HasPolynomialFamilyHessianDefect (K := K) S Delta :=
    integralSmithConformalFamily_preservesHessianDefect
      l l Delta P hPdiv hdef
  have hScollRaw :
      HasPolynomialFamilyExactGradientCollision S aS bS :=
    polynomialFamilyExactGradientCollision_integralSmithConformal
      l l P hPdiv
      (zeroPolynomialSection (K := K)) b
      haDiv hbDiv hcoll
  have haS : aS = zeroPolynomialSection (K := K) := by
    dsimp [aS]
    exact integralSmithConformalSection_zeroPolynomialSection l haDiv
  have hScoll :
      HasPolynomialFamilyExactGradientCollision
        S (zeroPolynomialSection (K := K)) bS := by
    rw [← haS]
    exact hScollRaw
  have hbS0 : polynomialSectionSpecialPoint bS 0 = 1 := by
    have hzero :=
      integralSmithConformalSection_zeroCoordinate
        (K := K) l b hbDiv
    have hb0 := congrFun hb (0 : Fin 4)
    have hb0' : Polynomial.constantCoeff (b 0) = 1 := by
      simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hb0
    change
      Polynomial.constantCoeff
        (integralSmithConformalSection l l b hbDiv 0) = 1
    rw [hzero]
    exact hb0'
  have hbSX :
      ∀ i : Fin 4, i ≠ 0 → Polynomial.X ∣ bS i := by
    dsimp [bS]
    exact oddWSeparatedRightWall_smallSmith_transverse_X_dvd
      P b hwall l hN hwstep hbDiv
  have ha1 :
      HasUnitKernelSectionDivisibility
        (K := K) 1 (zeroPolynomialSection (K := K)) := by
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb1 : HasUnitKernelSectionDivisibility (K := K) 1 bS :=
    hbSX 1 (by decide)
  let a1 :=
    unitKernelDeflateSection
      (K := K) 1 (zeroPolynomialSection (K := K)) ha1
  let b1 := unitKernelDeflateSection (K := K) 1 bS hb1
  have ha1zero : a1 = zeroPolynomialSection (K := K) := by
    dsimp [a1]
    exact unitKernelDeflateSection_zero 1 ha1
  have ha2 : HasUnitKernelSectionDivisibility (K := K) 2 a1 := by
    rw [ha1zero]
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb2 : HasUnitKernelSectionDivisibility (K := K) 2 b1 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 bS hb1 (i := (2 : Fin 4)) (by decide)]
    exact hbSX 2 (by decide)
  let a2 := unitKernelDeflateSection (K := K) 2 a1 ha2
  let b2 := unitKernelDeflateSection (K := K) 2 b1 hb2
  have ha2zero : a2 = zeroPolynomialSection (K := K) := by
    dsimp [a2]
    exact unitKernelDeflateSection_eq_zero_of_eq_zero
      2 a1 ha2 ha1zero
  have ha3 : HasUnitKernelSectionDivisibility (K := K) 3 a2 := by
    rw [ha2zero]
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb3 : HasUnitKernelSectionDivisibility (K := K) 3 b2 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b2]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 2 b1 hb2 (i := (3 : Fin 4)) (by decide)]
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 bS hb1 (i := (3 : Fin 4)) (by decide)]
    exact hbSX 3 (by decide)
  let aT :=
    unitTransverseDeflateSection
      (K := K) (zeroPolynomialSection (K := K)) ha1 ha2 ha3
  let bT := unitTransverseDeflateSection (K := K) bS hb1 hb2 hb3
  let I := unitTransverseInflateFamily S
  have hIdegree : NonlinearDegreeBound degreeCap I := by
    dsimp [I]
    exact nonlinearDegreeBound_unitTransverseInflateFamily
      degreeCap S hSdegree
  have hIdef :
      HasPolynomialFamilyHessianDefect (K := K) I (Delta + 6) := by
    dsimp [I]
    exact unitTransverseInflateFamily_hasHessianDefect_add_six S hSdef
  have hIcollRaw : HasPolynomialFamilyExactGradientCollision I aT bT := by
    dsimp [I, aT, bT]
    exact polynomialFamilyExactGradientCollision_unitTransverseInflate
      S (zeroPolynomialSection (K := K)) bS
      ha1 hb1 ha2 hb2 ha3 hb3 hScoll
  have haT : aT = zeroPolynomialSection (K := K) := by
    dsimp [aT, unitTransverseDeflateSection]
    exact unitKernelDeflateSection_eq_zero_of_eq_zero
      3 a2 ha3 ha2zero
  have hIcoll :
      HasPolynomialFamilyExactGradientCollision
        I (zeroPolynomialSection (K := K)) bT := by
    rw [← haT]
    exact hIcollRaw
  have hbT0 : polynomialSectionSpecialPoint bT 0 = 1 := by
    have hzero : bT 0 = bS 0 := by
      dsimp [bT]
      exact unitTransverseDeflateSection_zeroCoordinate bS hb1 hb2 hb3
    simpa [polynomialSectionSpecialPoint, hzero] using hbS0
  let hcommon :=
    oddWSeparatedRightWall_transverseInflate_commonFactor_two
      P b hwall hnotCoeff hnoPrimitive hsection hb
      l hN hPdiv
  let R := commonParameterFactorFamily 2 I hcommon
  have hRdegree : NonlinearDegreeBound degreeCap R := by
    dsimp [R]
    exact nonlinearDegreeBound_commonParameterFactor
      degreeCap 2 I hIdegree hcommon
  have hbudget : 4 * 2 ≤ Delta + 6 :=
    four_mul_le_defect_of_commonParameterFactor
      (K := K) 2 I hcommon (Delta + 6) hIdef
  have hDelta : 2 ≤ Delta := by omega
  have hRdefRaw :=
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (K := K) 2 I hcommon (Delta + 6) hIdef
  have hsub : Delta + 6 - 4 * 2 = Delta - 2 := by omega
  have hRdef :
      HasPolynomialFamilyHessianDefect (K := K) R (Delta - 2) := by
    dsimp [R]
    rw [hsub] at hRdefRaw
    exact hRdefRaw
  have hRcoll :
      HasPolynomialFamilyExactGradientCollision
        R (zeroPolynomialSection (K := K)) bT :=
    polynomialFamilyExactGradientCollision_commonParameterFactor
      2 I hcommon (zeroPolynomialSection (K := K)) bT hIcoll
  let R' := pointedShearNormalisedFamily R bT
  let b' := pointedShearNormalisedSection bT
  refine ⟨R', b', ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R']
    exact pointedShearNormalisedFamily_preservesHessianDefect R bT hRdef
  · dsimp [R']
    exact nonlinearDegreeBound_pointedShearNormalisedFamily
      degreeCap R bT hRdegree
  · dsimp [R', b']
    exact pointedShearNormalisedFamily_preservesExactCollision R bT hRcoll
  · dsimp [b']
    exact pointedShearNormalisedSection_specialPoint bT hbT0
  · omega

/-- Every separated right wall on a mixed-degree family has a genuine
adaptive restart with strictly smaller raw determinant defect. -/
theorem separatedRightSmithWall_strictAdaptiveGeometricRestart
    (degreeCap : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdegree : NonlinearDegreeBound degreeCap P)
    (b : Fin 4 → Polynomial K)
    (hsep : HasSeparatedRightSmithSectionWall P b)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    ∃ Delta' : ℕ,
      Delta' < Delta ∧
      ∃ P' : MvPolynomial (Fin 4) (Polynomial K),
        ∃ b' : Fin 4 → Polynomial K,
          HasPolynomialFamilyHessianDefect (K := K) P' Delta' ∧
          NonlinearDegreeBound degreeCap P' ∧
          HasPolynomialFamilyExactGradientCollision
            P' (zeroPolynomialSection (K := K)) b' ∧
          polynomialSectionSpecialPoint b' =
            coordinateAxisPoint (K := K) (0 : Fin 4) := by
  classical
  let hwall := Classical.choose hsep
  have hdata := Classical.choose_spec hsep
  have hnoPrimitive := hdata.1
  have hnotCoeff := hdata.2.1
  have hsection := hdata.2.2
  rcases separatedRightWall_tenAligned_or_oddW P b hsep with hten | hodd
  · rcases hten with ⟨m, hN⟩
    rcases tenAlignedSeparatedRightWall_strictAdaptiveRestart
        degreeCap P hdegree b hwall hnotCoeff hnoPrimitive
        hsection hdef hcoll hb m (by simpa [hwall] using hN) with
      ⟨P', b', hP'def, hP'degree, hP'coll, hb', hlt⟩
    exact ⟨Delta - 4, hlt, P', b', hP'def, hP'degree, hP'coll, hb'⟩
  · rcases hodd with ⟨l, hN, hwstep⟩
    rcases oddWSeparatedRightWall_strictAdaptiveRestart
        degreeCap P hdegree b hwall hnotCoeff hnoPrimitive
        hsection hdef hcoll hb l
        (by simpa [hwall] using hN)
        (by simpa [hwall] using hwstep) with
      ⟨P', b', hP'def, hP'degree, hP'coll, hb', hlt⟩
    exact ⟨Delta - 2, hlt, P', b', hP'def, hP'degree, hP'coll, hb'⟩

/-! ## Package the mixed-degree descent as a genuine global strict macro -/

/-- A separated right wall on the normalized family of a scale-aware state
produces a genuine strict same-scale successor, hence a sound global strict
macro with the identity presentation as its outer stage. -/
theorem ScaleAwareAdaptiveGeometricRestartState.globalRamifiedStrictMacro_of_separatedRightWall
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hsep :
      HasSeparatedRightSmithSectionWall
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s := by
  rcases separatedRightSmithWall_strictAdaptiveGeometricRestart
      s.degreeCap
      (zeroJetNormalizedFamily s.family)
      s.normalized_nonlinearDegreeBound
      s.movingSection hsep
      s.normalized_hessianDefect
      s.normalized_exactCollision
      s.sectionSpecial with
    ⟨Delta', hlt, P', b', hP'def, hP'degree, hP'coll, hb'⟩

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := Delta'
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P'
      movingSection := b'
      hessianDefect := hP'def
      nonlinearDegreeBound := hP'degree
      exactCollision := by
        simpa [zeroPolynomialSection] using hP'coll
      sectionSpecial := hb' }

  have hsame : SameEpisodeScale target s := by rfl
  have hprogress : CertifiedSameScaleEpisodeProgress RR target s := by
    apply certifiedSameScaleEpisodeProgress_of_rawDefect_lt RR hsame
    exact hlt

  exact .mk s target
    (HasCertifiedRamifiedEpisodeInternalMove.identity s)
    hprogress

/-! ## Every aligned boundary is primitive, strict, or genuinely coupled -/

/-- Geometric classification of one actual aligned section-boundary endpoint.
The strict constructor already contains the global recursive exit; the other
two constructors retain the exact first-wall witness for the remaining local
closure. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryGeometricOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | primitive
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)
      (hprimitive :
        HasPrimitiveZeroSmithSource
          (zeroJetNormalizedFamily s.family))

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | coupled
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)
      (hcoupled :
        HasCoupledAlignedSmithWall
          (zeroJetNormalizedFamily s.family)
          (zeroPolynomialSection (K := K))
          s.movingSection)

/-- **Mixed-degree aligned-boundary reduction.**

Because the left section is literally zero, every section-boundary endpoint
is a right-section wall.  Splitting on primitive source and coefficient-wall
membership gives exactly:

* primitive source;
* nonprimitive, non-coefficient = separated right wall, hence strict descent;
* nonprimitive coefficient+right-section = coupled wall.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryGeometricReduction
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
      (K := K) s.degreeCap s.rawDefect
      (zeroJetNormalizedFamily s.family) s.movingSection) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryGeometricOutcome RR s := by
  let P := zeroJetNormalizedFamily s.family
  have hright :
      alignedSmithGenuineFirstWall
          P (zeroPolynomialSection (K := K)) s.movingSection B.hwall ∈
        alignedSmithSectionWalls s.movingSection := by
    rcases B.boundary with hleft | hright
    · rcases hleft with ⟨i, hi0, hmem, hne⟩
      exact False.elim
        ((not_mem_alignedSmithSectionWalls_zeroPolynomialSection
            (K := K)
            (alignedSmithGenuineFirstWall
              P (zeroPolynomialSection (K := K)) s.movingSection B.hwall))
          hmem)
    · rcases hright with ⟨i, hi0, hmem, hne⟩
      exact hmem

  by_cases hprimitive : HasPrimitiveZeroSmithSource P
  · exact .primitive B hprimitive
  · by_cases hcoeff :
        alignedSmithGenuineFirstWall
            P (zeroPolynomialSection (K := K)) s.movingSection B.hwall ∈
          alignedSmithCoefficientWalls P
    · exact .coupled B ⟨B.hwall, hcoeff, Or.inr hright⟩
    · have hsep : HasSeparatedRightSmithSectionWall P s.movingSection :=
        ⟨B.hwall, hprimitive, hcoeff, hright⟩
      exact .strictMacro
        (s.globalRamifiedStrictMacro_of_separatedRightWall RR hsep)

/-! ## Strip an aligned-boundary head trace to the same trichotomy -/

/-- After arbitrary pure-presentation suffixes, an aligned-boundary head is
still classified by its literal first boundary.  A separated first boundary
already yields strict progress from the original source, so the suffix is
irrelevant to recursion. -/
inductive AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadGeometricOutcome
    (RR : RepairRanking)
    (source target : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | primitive
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B))
      (hprimitive :
        HasPrimitiveZeroSmithSource
          (zeroJetNormalizedFamily source.family))

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)

  | coupled
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection)
      (htail : HasCertifiedRamifiedEpisodeInternalMove target
        (source.alignedBoundaryScaleAwareReentry B))
      (hcoupled :
        HasCoupledAlignedSmithWall
          (zeroJetNormalizedFamily source.family)
          (zeroPolynomialSection (K := K))
          source.movingSection)

/-- Typed aligned-boundary traces inherit the mixed-degree first-head
classification. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.geometricReduction
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadGeometricOutcome
      RR source target := by
  rcases trace.exists_head_boundary with ⟨B, htail⟩
  cases source.alignedBoundaryGeometricReduction RR B with
  | primitive B hprimitive =>
      exact .primitive B htail hprimitive
  | strictMacro D =>
      exact .strictMacro D
  | coupled B hcoupled =>
      exact .coupled B htail hcoupled

end

end HC4.Valuation
