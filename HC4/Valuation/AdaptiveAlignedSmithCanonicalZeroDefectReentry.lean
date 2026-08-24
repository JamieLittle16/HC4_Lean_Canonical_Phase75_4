import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamificationTermination
import HC4.Valuation.SeparatedRightWallScaleDescent
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# A17.8: zero-defect transverse Rees re-entry

A17.7 leaves one genuine global endpoint: `rawDefect = 0`.  This endpoint
must not be declared contradictory: it still carries the determinant-one
family and the exact pointed gradient collision.

The older separated-wall descent already contains the right way to leave this
endpoint without assuming HC4.  Inflate each of the three transverse source
coordinates once,

    x₁ ↦ τ x₁,  x₂ ↦ τ x₂,  x₃ ↦ τ x₃.

The Hessian determinant clock increases by exactly six.  Because the retained
moving section specializes to `e₀`, all three transverse section coordinates
are divisible by `τ`; hence the exact collision transports through the inverse
section maps.  A determinant-one pointed shear then restores the canonical
special pair `0,e₀` without changing the new clock.

The construction preserves the source-degree ceiling, the ambient scale,
source complexity, and repair metadata.  Thus a literal zero-defect endpoint
is converted into a genuine positive-clock scale-aware state rather than
being treated as a terminal contradiction.

Combining this with A17.7 removes `zeroDefect` from the global-facing frontier:
the only alternatives are certified same-scale progress or a canonical
positive-clock re-entry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Unit inflation of one source coordinate preserves the nonlinear ordinary
source-degree ceiling. -/
theorem nonlinearDegreeBound_kernelInflateHom_unit
    (m : ℕ)
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (kernelInflateHom (K := K) kernel 1 P) := by
  apply nonlinearDegreeBound_map_of_monomial_homogeneous
    (kernelInflateHom (K := K) kernel 1) P m hP
  intro n r
  have hhom :
      (MvPolynomial.monomial n r).IsHomogeneous n.degree :=
    MvPolynomial.isHomogeneous_monomial r rfl
  exact kernelInflateHom_isHomogeneous kernel
    (MvPolynomial.monomial n r) hhom

/-- The three transverse unit inflations preserve the nonlinear source-degree
ceiling. -/
theorem nonlinearDegreeBound_unitTransverseInflateFamily
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (unitTransverseInflateFamily (K := K) P) := by
  unfold unitTransverseInflateFamily
  apply nonlinearDegreeBound_kernelInflateHom_unit
  apply nonlinearDegreeBound_kernelInflateHom_unit
  apply nonlinearDegreeBound_kernelInflateHom_unit
  exact hP

/-- The three determinant-one pointed shears preserve the nonlinear
source-degree ceiling. -/
theorem nonlinearDegreeBound_pointedShearNormalisedFamily
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hP : NonlinearDegreeBound m P) :
    NonlinearDegreeBound m (pointedShearNormalisedFamily P b) := by
  unfold pointedShearNormalisedFamily
  apply nonlinearDegreeBound_elementaryShear
  unfold pointedShearFamilyTwo
  apply nonlinearDegreeBound_elementaryShear
  unfold pointedShearFamilyOne
  exact nonlinearDegreeBound_elementaryShear
    m (1 : Fin 4) (pointedShearCoeffOne b) P hP

/-- Every transverse coordinate of the retained moving section is divisible
by the parameter, because its special point is exactly `e₀`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.movingSection_X_dvd_of_ne_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (i : Fin 4)
    (hi : i ≠ (0 : Fin 4)) :
    Polynomial.X ∣ s.movingSection i := by
  rw [Polynomial.X_dvd_iff]
  have hspecial := congrFun s.sectionSpecial i
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint, hi] using hspecial

/-- **Zero-defect transverse Rees re-entry.**

A scale-aware determinant-one collision state canonically gives another
scale-aware state at the same literal scale with raw defect exactly six.
No terminal contradiction, JC2 assumption, or old homogeneous entry interface
is used. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_zeroDefectTransverseReentry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    ∃ t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      t.rawDefect = 6 ∧
      t.scale = s.scale ∧
      t.degreeCap = s.degreeCap ∧
      t.sourceComplexity = s.sourceComplexity ∧
      t.repair = s.repair ∧
      0 < t.rawDefect := by
  have ha1 :
      HasUnitKernelSectionDivisibility
        (K := K) 1 (zeroPolynomialSection (K := K)) := by
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb1 :
      HasUnitKernelSectionDivisibility (K := K) 1 s.movingSection :=
    s.movingSection_X_dvd_of_ne_zero 1 (by decide)

  let a1 := unitKernelDeflateSection
    (K := K) 1 (zeroPolynomialSection (K := K)) ha1
  let b1 := unitKernelDeflateSection (K := K) 1 s.movingSection hb1

  have ha1zero : a1 = zeroPolynomialSection (K := K) := by
    dsimp [a1]
    exact unitKernelDeflateSection_zero 1 ha1

  have ha2 :
      HasUnitKernelSectionDivisibility (K := K) 2 a1 := by
    rw [ha1zero]
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb2 : HasUnitKernelSectionDivisibility (K := K) 2 b1 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 s.movingSection hb1 (i := (2 : Fin 4)) (by decide)]
    exact s.movingSection_X_dvd_of_ne_zero 2 (by decide)

  let a2 := unitKernelDeflateSection (K := K) 2 a1 ha2
  let b2 := unitKernelDeflateSection (K := K) 2 b1 hb2

  have ha2zero : a2 = zeroPolynomialSection (K := K) := by
    dsimp [a2]
    exact unitKernelDeflateSection_eq_zero_of_eq_zero 2 a1 ha2 ha1zero

  have ha3 :
      HasUnitKernelSectionDivisibility (K := K) 3 a2 := by
    rw [ha2zero]
    simp [HasUnitKernelSectionDivisibility, zeroPolynomialSection]
  have hb3 : HasUnitKernelSectionDivisibility (K := K) 3 b2 := by
    unfold HasUnitKernelSectionDivisibility
    dsimp [b2]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 2 b1 hb2 (i := (3 : Fin 4)) (by decide)]
    dsimp [b1]
    rw [unitKernelDeflateSection_of_ne
      (K := K) 1 s.movingSection hb1 (i := (3 : Fin 4)) (by decide)]
    exact s.movingSection_X_dvd_of_ne_zero 3 (by decide)

  let aT := unitTransverseDeflateSection
    (K := K) (zeroPolynomialSection (K := K)) ha1 ha2 ha3
  let bT := unitTransverseDeflateSection
    (K := K) s.movingSection hb1 hb2 hb3
  let I := unitTransverseInflateFamily (K := K) s.family

  have haT : aT = zeroPolynomialSection (K := K) := by
    dsimp [aT, unitTransverseDeflateSection]
    exact unitKernelDeflateSection_eq_zero_of_eq_zero 3 a2 ha3 ha2zero

  have hIdefRaw :
      HasPolynomialFamilyHessianDefect (K := K) I (s.rawDefect + 6) := by
    dsimp [I]
    exact unitTransverseInflateFamily_hasHessianDefect_add_six
      s.family s.hessianDefect
  have hIdef : HasPolynomialFamilyHessianDefect (K := K) I 6 := by
    simpa [hzero] using hIdefRaw

  have hIdegree : NonlinearDegreeBound s.degreeCap I := by
    dsimp [I]
    exact nonlinearDegreeBound_unitTransverseInflateFamily
      s.degreeCap s.family s.nonlinearDegreeBound

  have hIcollRaw :
      HasPolynomialFamilyExactGradientCollision I aT bT := by
    dsimp [I, aT, bT]
    exact polynomialFamilyExactGradientCollision_unitTransverseInflate
      s.family
      (zeroPolynomialSection (K := K))
      s.movingSection
      ha1 hb1 ha2 hb2 ha3 hb3
      (by simpa [zeroPolynomialSection] using s.exactCollision)

  have hIcoll :
      HasPolynomialFamilyExactGradientCollision
        I (zeroPolynomialSection (K := K)) bT := by
    rw [← haT]
    exact hIcollRaw

  have hb0 :
      polynomialSectionSpecialPoint s.movingSection (0 : Fin 4) = 1 := by
    have h := congrFun s.sectionSpecial (0 : Fin 4)
    simpa [coordinateAxisPoint] using h
  have hbT0 : polynomialSectionSpecialPoint bT (0 : Fin 4) = 1 := by
    have hcoord : bT 0 = s.movingSection 0 := by
      dsimp [bT]
      exact unitTransverseDeflateSection_zeroCoordinate
        s.movingSection hb1 hb2 hb3
    simpa [polynomialSectionSpecialPoint, hcoord] using hb0

  let Q := pointedShearNormalisedFamily I bT
  let bQ := pointedShearNormalisedSection bT

  have hQdef : HasPolynomialFamilyHessianDefect (K := K) Q 6 := by
    dsimp [Q]
    exact pointedShearNormalisedFamily_preservesHessianDefect I bT hIdef
  have hQdegree : NonlinearDegreeBound s.degreeCap Q := by
    dsimp [Q]
    exact nonlinearDegreeBound_pointedShearNormalisedFamily
      s.degreeCap I bT hIdegree
  have hQcoll :
      HasPolynomialFamilyExactGradientCollision
        Q (zeroPolynomialSection (K := K)) bQ := by
    dsimp [Q, bQ]
    exact pointedShearNormalisedFamily_preservesExactCollision I bT hIcoll
  have hQspecial :
      polynomialSectionSpecialPoint bQ =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bQ]
    exact pointedShearNormalisedSection_specialPoint bT hbT0

  let t : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := 6
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Q
      movingSection := bQ
      hessianDefect := hQdef
      nonlinearDegreeBound := hQdegree
      exactCollision := by
        simpa [zeroPolynomialSection] using hQcoll
      sectionSpecial := hQspecial }

  refine ⟨t, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change 0 < 6
  decide

/-- Global-facing outcome after consuming the literal zero-defect endpoint of
A17.7.  `positiveReentry` is not claimed to be recursive progress; it is an
explicit canonical presentation of the same counterexample geometry at a
positive determinant clock. -/
inductive AdaptiveAlignedSmithCanonicalZeroDefectReentryOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | strictProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hprogress : CertifiedSameScaleEpisodeProgress RR target s)
  | positiveReentry
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hraw : target.rawDefect = 6)
      (hscale : target.scale = s.scale)
      (hdegreeCap : target.degreeCap = s.degreeCap)
      (hsourceComplexity : target.sourceComplexity = s.sourceComplexity)
      (hrepair : target.repair = rankOneRepairState complexity)
      (hpositive : 0 < target.rawDefect)

/-- **A17.8 zero-endpoint bridge.**

Run A17.7.  Genuine same-scale progress is retained.  Its sole terminal
constructor is converted, by the transverse Rees construction above, into a
positive-clock state at the same scale and at the same rank-one repair stage.
Thus the global assembly never has to assert that determinant one plus a
collision is already contradictory. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalZeroDefectReentryFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalZeroDefectReentryOutcome RR s complexity := by
  cases s.alignedSmithCanonicalRamificationTerminatedFrontier
      RR complexity hsrepair with
  | strictProgress target hprogress =>
      exact .strictProgress target hprogress
  | zeroDefect hzero =>
      rcases s.exists_zeroDefectTransverseReentry hzero with
        ⟨target, hraw, hscale, hdegreeCap, hsourceComplexity,
          hrepair, hpositive⟩
      exact .positiveReentry target hraw hscale hdegreeCap hsourceComplexity
        (hrepair.trans hsrepair) hpositive

end

end HC4.Valuation
