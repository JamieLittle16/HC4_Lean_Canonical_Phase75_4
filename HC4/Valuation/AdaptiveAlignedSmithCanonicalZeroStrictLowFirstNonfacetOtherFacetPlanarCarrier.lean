import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetNeutralSkew
import HC4.Newton.FiniteSupportRayPlanarRefinement
import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import HC4.MongeAmpere.PolynomialInitial
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A19 source-honest defect-neutral planar carrier

This file closes the finite-support existence gap left by the paper handoff.

Starting from the exact positive-defect source exposure of the locked `qs` ray:

1. pair degree gives the first strict nonlinear superface;
2. every new point on that first wall has pair degree strictly bigger than one;
3. the endpoint-native neutral skew and the finite maximal-ratio theorem select
   a second wall containing the whole ray and at least one nonlinear point;
4. the second wall weight is an explicit integer linear combination of pair
   degree and skew, hence is Hessian-clock neutral;
5. positive finite exposed-face refinement absorbs that signed wall into one
   exact positive source exposure;
6. the positive determinant clock of that exact source exposure forces the
   final carrier Hessian determinant to vanish.

The resulting support lies simultaneously on the first-wall affine hyperplane
and on an independent neutral wall.  This is the precise planar carrier needed
before taking fixed pair-degree line slices.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Exact source-facing output of the two neutral refinements.  `firstWeight`
and `wallWeight` are retained explicitly so later fixed-pair slices can use the
two affine equations rather than reconstructing the normal-fan argument. -/
structure QsOtherFacetPlanarCarrierPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet) where
  firstWeight : Fin 4 → ℤ
  firstLevel : ℤ
  wallWeight : Fin 4 → ℤ
  wallLevel : ℤ
  pairGap : ℤ
  skewGap : ℤ
  pairGap_pos : 0 < pairGap
  wallWeight_eq :
    wallWeight = fun i =>
      pairGap * qsOtherFacetSkewWeight C next i -
        skewGap * qsOtherFacetPairWeight next i
  wallLevel_eq :
    wallLevel =
      pairGap * qsOtherFacetSkewLevel C next - skewGap
  finalWeight : Fin 4 → ℤ
  finalLevel : ℤ
  carrier : MvPolynomial (Fin 4) K
  carrier_eq_initialForm :
    carrier = HC4.Polynomial.initialForm finalWeight finalLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  source_bound : HC4.Polynomial.IsWeightLE finalWeight finalLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  finalWeight_pos : ∀ i : Fin 4, 0 < finalWeight i
  finalLevel_pos : 0 < finalLevel
  hessianClock_pos :
    0 < 4 * finalLevel - 2 * ∑ i : Fin 4, finalWeight i
  ray_support_subset :
    (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
      (↑carrier.support : Set (Fin 4 →₀ ℕ))
  nonlinear_point :
    ∃ e, e ∈ carrier.support ∧ e ∉ C.ray.face.support ∧
      1 < qsOtherFacetPairDegree next e
  support_first_level :
    ∀ {e}, e ∈ carrier.support →
      Finsupp.weight firstWeight e = firstLevel
  support_wall_level :
    ∀ {e}, e ∈ carrier.support →
      Finsupp.weight wallWeight e = wallLevel
  hessian_zero : HC4.Polynomial.hessianDeterminant carrier = 0

private theorem weight_scalar_mul_fin4
    (a : ℤ) (w : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => a * w i) e =
      a * Finsupp.weight w e := by
  have h := HC4.Newton.finsupp_weight_fin4_linear_combination
    a w (fun _ => 0) e
  have hz : Finsupp.weight (fun _ : Fin 4 => (0 : ℤ)) e = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp
    · intro i
      simp
  simpa [hz] using h

private theorem weight_sub_scalar_mul_fin4
    (a b : ℤ) (w v : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => a * w i - b * v i) e =
      a * Finsupp.weight w e - b * Finsupp.weight v e := by
  have h := HC4.Newton.finsupp_weight_fin4_linear_combination
    a w (fun i => (-b) * v i) e
  rw [weight_scalar_mul_fin4] at h
  simpa [sub_eq_add_neg, neg_mul] using h

/-- Linearise the ratio wall into an honest `Fin 4` source weight. -/
private theorem ratioWallWeight_eq_finsuppWeight_sub_level
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet)
    (a e : Fin 4 →₀ ℕ) :
    let p : (Fin 4 →₀ ℕ) → ℤ := fun d =>
      qsOtherFacetPairDegree next d
    let s : (Fin 4 →₀ ℕ) → ℤ := fun d =>
      Finsupp.weight (qsOtherFacetSkewWeight C next) d
    let pGap := p a - 1
    let sGap := s a - qsOtherFacetSkewLevel C next
    let theta : Fin 4 → ℤ := fun i =>
      pGap * qsOtherFacetSkewWeight C next i -
        sGap * qsOtherFacetPairWeight next i
    let thetaLevel :=
      pGap * qsOtherFacetSkewLevel C next - sGap
    HC4.Newton.ratioWallWeight p s 1
        (qsOtherFacetSkewLevel C next) a e =
      Finsupp.weight theta e - thetaLevel := by
  dsimp
  rw [weight_sub_scalar_mul_fin4]
  rw [finsupp_weight_qsOtherFacetPairWeight]
  simp [HC4.Newton.ratioWallWeight]
  ring

/-- **A19 planar source carrier.**  The two defect-neutral refinements can be
performed exactly on the represented source, producing a positive-defect
singular carrier which contains the full locked ray and a nonlinear point and
satisfies two retained affine support equations. -/
theorem qs_ray_otherFacet_planarCarrier_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPlanarCarrierPackage C next) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  rcases C.qs_ray_otherFacet_rayReverseRees_package hthree hne houtThree with
    ⟨R⟩
  let w : Fin 4 → ℤ := fun i => (R.weight i : ℤ)
  let c : ℤ := (R.level : ℤ)
  let pair : Fin 4 → ℤ := qsOtherFacetPairWeight next
  let pairDegree : (Fin 4 →₀ ℕ) → ℤ := fun e =>
    qsOtherFacetPairDegree next e
  let skew : Fin 4 → ℤ := qsOtherFacetSkewWeight C next
  let skewDegree : (Fin 4 →₀ ℕ) → ℤ := fun e =>
    Finsupp.weight skew e
  let skewLevel : ℤ := qsOtherFacetSkewLevel C next
  let v : (Fin 4 →₀ ℕ) → ℤ := fun e => -pairDegree e
  let d : ℤ := -1

  have hsourceBound : HC4.Polynomial.IsWeightLE w c F := by
    intro e he
    have hnat := R.bound e he
    have hcast :
        Finsupp.weight w e = (Finsupp.weight R.weight e : ℤ) := by
      dsimp [w]
      rw [Finsupp.weight_apply, Finsupp.weight_apply]
      push_cast
      rfl
    rw [hcast]
    change (Finsupp.weight R.weight e : ℤ) ≤ (R.level : ℤ)
    exact_mod_cast hnat

  have hinit : HC4.Polynomial.initialForm w c F = C.ray.face := by
    simpa [w, c, F] using R.initialForm_eq_ray
  have hRay :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight w e) c := by
    have h := HC4.Newton.initialForm_support_isExposedFace w c F hsourceBound
    rw [hinit] at h
    exact h

  have hvRay :
      ∀ e ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)), v e = d := by
    intro e he
    have hp := C.qs_ray_otherFacet_pairDegree_eq_one_of_mem
      hthree hne houtThree (by simpa using he)
    simp [v, pairDegree, d, hp]

  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨exit, hexitSource, _hexitDegree, hexit0, _hexitCodim⟩
  have hexitPair : 1 < pairDegree exit := by
    dsimp [pairDegree]
    exact one_lt_qsOtherFacetPairDegree_of_two_le_zeroCoordinate
      next hne exit hexit0
  have hexitNotRay : exit ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) := by
    intro hmem
    have hp := C.qs_ray_otherFacet_pairDegree_eq_one_of_mem
      hthree hne houtThree (by simpa using hmem)
    dsimp [pairDegree] at hexitPair
    omega
  have hexitV : v exit < d := by
    dsimp [v, d]
    omega
  have hexit : ∃ e ∈ F.support,
      e ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ∧ v e < d :=
    ⟨exit, hexitSource, hexitNotRay, hexitV⟩

  rcases HC4.Newton.exists_first_exposed_superface
      F.support hRay hvRay hexit with
    ⟨A, B, G1, hA, hB, hG1raw, hRayG1, hnew⟩

  let W1 : Fin 4 → ℤ := fun i => A * w i + B * pair i
  let L1 : ℤ := A * c + B
  have hweight1 :
      (fun e : Fin 4 →₀ ℕ => Finsupp.weight W1 e) =
        (fun e => A * Finsupp.weight w e - B * v e) := by
    funext e
    have hlin := HC4.Newton.finsupp_weight_fin4_linear_combination
      A w (fun i => B * pair i) e
    rw [hlin, weight_scalar_mul_fin4]
    rw [show Finsupp.weight pair e = pairDegree e by
      simpa [pair, pairDegree] using
        (finsupp_weight_qsOtherFacetPairWeight next e)]
    simp [v]
  have hG1 :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ)) G1
        (fun e => Finsupp.weight W1 e) L1 := by
    rw [hweight1]
    simpa [L1, d] using hG1raw
  have hW1Bound : HC4.Polynomial.IsWeightLE W1 L1 F := by
    intro e he
    exact hG1.weight_le (by simpa using he)

  let carrier1 : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.initialForm W1 L1 F
  have hCarrier1Face :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑carrier1.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W1 e) L1 := by
    simpa [carrier1] using
      (HC4.Newton.initialForm_support_isExposedFace W1 L1 F hW1Bound)
  have hsupport1 :
      (↑carrier1.support : Set (Fin 4 →₀ ℕ)) = G1 := by
    ext e
    constructor
    · intro he
      exact hG1.mem_iff.mpr (hCarrier1Face.mem_iff.mp he)
    · intro he
      exact hCarrier1Face.mem_iff.mpr (hG1.mem_iff.mp he)

  have hRayCarrier1 :
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
        (↑carrier1.support : Set (Fin 4 →₀ ℕ)) := by
    intro e he
    rw [hsupport1]
    exact hRayG1 he

  have hoffPair :
      ∀ e ∈ carrier1.support,
        e ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) →
        1 < pairDegree e := by
    intro e heCarrier heNotRay
    have heG1 : e ∈ G1 := by
      rw [← hsupport1]
      simpa using heCarrier
    have heSource : e ∈ (↑F.support : Set (Fin 4 →₀ ℕ)) :=
      hG1.subset heG1
    have hwLe : Finsupp.weight w e ≤ c := hRay.weight_le heSource
    have hwNe : Finsupp.weight w e ≠ c := by
      intro heq
      apply heNotRay
      exact hRay.mem_iff.mpr ⟨heSource, heq⟩
    have hwLt : Finsupp.weight w e < c := by omega
    have hcomb := hG1raw.weight_eq heG1
    dsimp [v, d] at hcomb
    nlinarith

  have hpRay :
      ∀ e ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)),
        pairDegree e = 1 := by
    intro e he
    dsimp [pairDegree]
    exact C.qs_ray_otherFacet_pairDegree_eq_one_of_mem
      hthree hne houtThree (by simpa using he)
  have hsRay :
      ∀ e ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)),
        skewDegree e = skewLevel := by
    intro e he
    dsimp [skewDegree, skew, skewLevel]
    exact C.qsOtherFacetSkewWeight_eq_level_of_ray_mem
      hthree hne houtThree (by simpa using he)

  have hexitCarrier1 :
      ∃ e ∈ carrier1.support,
        e ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) := by
    rcases hnew with ⟨e, heG1, heNotRay⟩
    refine ⟨e, ?_, heNotRay⟩
    have : e ∈ (↑carrier1.support : Set (Fin 4 →₀ ℕ)) := by
      rw [hsupport1]
      exact heG1
    simpa using this

  rcases HC4.Newton.exists_exposed_ratio_wall
      carrier1.support
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ))
      pairDegree skewDegree 1 skewLevel
      hRayCarrier1 hpRay hsRay hoffPair hexitCarrier1 with
    ⟨a, haCarrier1, haNotRay, hWallRaw, hRayWall, haWall⟩

  let G2 : Set (Fin 4 →₀ ℕ) :=
    {e | e ∈ (↑carrier1.support : Set (Fin 4 →₀ ℕ)) ∧
      HC4.Newton.ratioWallWeight
        pairDegree skewDegree 1 skewLevel a e = 0}
  have hWall :
      HC4.Newton.IsExposedFace
        (↑carrier1.support : Set (Fin 4 →₀ ℕ)) G2
        (HC4.Newton.ratioWallWeight
          pairDegree skewDegree 1 skewLevel a) 0 := by
    simpa [G2] using hWallRaw
  have hRayG2 :
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆ G2 := by
    simpa [G2] using hRayWall
  have haG2 : a ∈ G2 := by simpa [G2] using haWall

  let pGap : ℤ := pairDegree a - 1
  let sGap : ℤ := skewDegree a - skewLevel
  have hpGap : 0 < pGap := by
    dsimp [pGap]
    exact sub_pos.mpr (hoffPair a haCarrier1 haNotRay)
  let theta : Fin 4 → ℤ := fun i =>
    pGap * skew i - sGap * pair i
  let thetaLevel : ℤ := pGap * skewLevel - sGap

  have hWallLinear : ∀ e : Fin 4 →₀ ℕ,
      HC4.Newton.ratioWallWeight
          pairDegree skewDegree 1 skewLevel a e =
        Finsupp.weight theta e - thetaLevel := by
    intro e
    simpa [pairDegree, skewDegree, skew, skewLevel,
      pGap, sGap, theta, thetaLevel] using
      (ratioWallWeight_eq_finsuppWeight_sub_level
        (C := C) next a e)

  have hTheta :
      HC4.Newton.IsExposedFace
        (↑carrier1.support : Set (Fin 4 →₀ ℕ)) G2
        (fun e => Finsupp.weight theta e) thetaLevel := by
    constructor
    · ext e
      constructor
      · intro heG
        have hm := hWall.mem_iff.mp heG
        refine ⟨hm.1, ?_⟩
        have hz := hm.2
        rw [hWallLinear e] at hz
        linarith
      · rintro ⟨heS, heq⟩
        apply hWall.mem_iff.mpr
        refine ⟨heS, ?_⟩
        rw [hWallLinear e]
        linarith
    · intro e heS
      have hle := hWall.weight_le heS
      rw [hWallLinear e] at hle
      linarith

  have hThetaG1 :
      HC4.Newton.IsExposedFace G1 G2
        (fun e => Finsupp.weight theta e) thetaLevel := by
    rw [← hsupport1]
    exact hTheta

  have hW1pos : ∀ i : Fin 4, 0 < W1 i := by
    intro i
    have hwz : (0 : ℤ) < w i := by
      dsimp [w]
      exact_mod_cast R.weight_pos i
    have hpairNonneg : (0 : ℤ) ≤ pair i := by
      dsimp [pair]
      cases next <;> fin_cases i <;>
        norm_num [qsOtherFacetPairWeight]
    dsimp [W1]
    have hAw : 0 < A * w i := mul_pos hA hwz
    have hBp : 0 ≤ B * pair i := mul_nonneg hB.le hpairNonneg
    linarith
  have hcpos : (0 : ℤ) < c := by
    dsimp [c]
    exact_mod_cast R.level_pos
  have hL1pos : 0 < L1 := by
    dsimp [L1]
    have hAc : 0 < A * c := mul_pos hA hcpos
    linarith
  have hsumPair : ∑ i : Fin 4, pair i = 2 := by
    simpa [pair] using sum_qsOtherFacetPairWeight_eq_two next hne
  have hsumW1 :
      ∑ i : Fin 4, W1 i =
        A * (∑ i : Fin 4, w i) + B * 2 := by
    simp only [Fin.sum_univ_four] at hsumPair ⊢
    dsimp [W1]
    nlinarith [hsumPair]
  have hbaseLtNat :
      2 * ∑ i : Fin 4, R.weight i < 4 * R.level :=
    Nat.sub_pos_iff_lt.mp R.defect_pos
  have hbaseLt :
      (2 : ℤ) * ∑ i : Fin 4, w i < 4 * c := by
    dsimp [w, c]
    rw [Fin.sum_univ_four] at hbaseLtNat ⊢
    exact_mod_cast hbaseLtNat
  have hbaseClock : 0 < 4 * c - 2 * ∑ i : Fin 4, w i := by omega
  have hclock1Eq :
      4 * L1 - 2 * ∑ i : Fin 4, W1 i =
        A * (4 * c - 2 * ∑ i : Fin 4, w i) := by
    rw [hsumW1]
    dsimp [L1]
    ring
  have hclock1 : 0 < 4 * L1 - 2 * ∑ i : Fin 4, W1 i := by
    rw [hclock1Eq]
    exact mul_pos hA hbaseClock

  have hFNonempty : F.support.Nonempty := by
    refine ⟨C.ray.facetExponent, ?_⟩
    have : C.ray.facetExponent ∈
        (↑F.support : Set (Fin 4 →₀ ℕ)) :=
      hRay.subset (by simpa using C.ray.facet_mem_face)
    simpa using this

  rcases HC4.Newton.exists_nat_refine_exposed_face_fin4_positive_clock
      F.support hFNonempty hG1 hThetaG1 hW1pos hL1pos hclock1 with
    ⟨M, hM, hFinalRaw, hFinalPosRaw, hFinalLevelRaw, hFinalClockRaw⟩

  let finalWeight : Fin 4 → ℤ := fun i => (M : ℤ) * W1 i + theta i
  let finalLevel : ℤ := (M : ℤ) * L1 + thetaLevel
  have hFinal :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ)) G2
        (fun e => Finsupp.weight finalWeight e) finalLevel := by
    simpa [finalWeight, finalLevel] using hFinalRaw
  have hFinalPos : ∀ i : Fin 4, 0 < finalWeight i := by
    simpa [finalWeight] using hFinalPosRaw
  have hFinalLevel : 0 < finalLevel := by
    simpa [finalLevel] using hFinalLevelRaw
  have hFinalClock :
      0 < 4 * finalLevel - 2 * ∑ i : Fin 4, finalWeight i := by
    simpa [finalWeight, finalLevel] using hFinalClockRaw
  have hFinalBound : HC4.Polynomial.IsWeightLE finalWeight finalLevel F := by
    intro e he
    exact hFinal.weight_le (by simpa using he)

  let carrier : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.initialForm finalWeight finalLevel F
  have hCarrierFace :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑carrier.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight finalWeight e) finalLevel := by
    simpa [carrier] using
      (HC4.Newton.initialForm_support_isExposedFace
        finalWeight finalLevel F hFinalBound)
  have hsupport :
      (↑carrier.support : Set (Fin 4 →₀ ℕ)) = G2 := by
    ext e
    constructor
    · intro he
      exact hFinal.mem_iff.mpr (hCarrierFace.mem_iff.mp he)
    · intro he
      exact hCarrierFace.mem_iff.mpr (hFinal.mem_iff.mp he)

  have hRayCarrier :
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
        (↑carrier.support : Set (Fin 4 →₀ ℕ)) := by
    intro e he
    rw [hsupport]
    exact hRayG2 he
  have haCarrier : a ∈ carrier.support := by
    have : a ∈ (↑carrier.support : Set (Fin 4 →₀ ℕ)) := by
      rw [hsupport]
      exact haG2
    simpa using this
  have haPair : 1 < qsOtherFacetPairDegree next a := by
    dsimp [pGap, pairDegree] at hpGap
    omega

  have hFirstLevel :
      ∀ {e}, e ∈ carrier.support → Finsupp.weight W1 e = L1 := by
    intro e he
    have heG2 : e ∈ G2 := by
      rw [← hsupport]
      simpa using he
    have heCarrier1 : e ∈ (↑carrier1.support : Set (Fin 4 →₀ ℕ)) :=
      hTheta.subset heG2
    exact hCarrier1Face.weight_eq heCarrier1
  have hWallLevel :
      ∀ {e}, e ∈ carrier.support → Finsupp.weight theta e = thetaLevel := by
    intro e he
    have heG2 : e ∈ G2 := by
      rw [← hsupport]
      simpa using he
    exact hTheta.weight_eq heG2

  have hdetF : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := hdetF
  have hdetComponent :
      HC4.Polynomial.initialForm finalWeight
        (4 * finalLevel - 2 * ∑ i : Fin 4, finalWeight i)
        (HC4.Polynomial.hessianDeterminant F) = 0 := by
    exact HC4.MongeAmpere.initialForm_hessianDeterminant_eq_zero
      hMA (ne_of_gt hFinalClock)
  have hcarrierZero : HC4.Polynomial.hessianDeterminant carrier = 0 := by
    have hcompat :=
      HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
        finalWeight finalLevel F hFinalBound
    rw [← hcompat]
    simpa using hdetComponent

  refine ⟨{
    firstWeight := W1
    firstLevel := L1
    wallWeight := theta
    wallLevel := thetaLevel
    pairGap := pGap
    skewGap := sGap
    pairGap_pos := hpGap
    wallWeight_eq := by rfl
    wallLevel_eq := by rfl
    finalWeight := finalWeight
    finalLevel := finalLevel
    carrier := carrier
    carrier_eq_initialForm := by rfl
    source_bound := hFinalBound
    finalWeight_pos := hFinalPos
    finalLevel_pos := hFinalLevel
    hessianClock_pos := hFinalClock
    ray_support_subset := hRayCarrier
    nonlinear_point := ⟨a, haCarrier, haNotRay, haPair⟩
    support_first_level := hFirstLevel
    support_wall_level := hWallLevel
    hessian_zero := hcarrierZero
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
