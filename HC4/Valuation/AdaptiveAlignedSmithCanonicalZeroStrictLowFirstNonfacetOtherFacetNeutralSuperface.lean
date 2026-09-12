import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOnePencil
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetDirectionLock
import HC4.Newton.FiniteSupportExposedSuperface
import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import HC4.MongeAmpere.PolynomialInitial
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A19 source-honest defect-neutral first superface

The surviving rank-three lower `qs` ray has pair degree one: coordinate `0`
plus the coordinate omitted by the different outside facet is identically one
on the whole degree-one ray.  The strict-low represented source still contains
a monomial with coordinate `0 >= 2`, so the negative pair degree gives a
secondary weight which is constant on the ray and strictly lower somewhere in
the source support.

Starting from the positive ray exposure supplied by the honest reverse-Rees
package, the finite first-superface theorem therefore produces a strict source
superface.  Adding the pair weight is Hessian-clock neutral in four variables:
its level increases by one and the sum of source weights increases by two.
Consequently the new source initial form has the same positive determinant
clock, up to the positive primary scaling factor.  Since the represented source
has Hessian determinant one, the new carrier is genuinely Hessian singular.

This file is deliberately source-facing.  Singularity is proved from the
represented determinant-one source; it is not inherited from the smaller ray.
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

/-- Pair weight used by the other-facet planar refinement.  For a lower `qs`
ray and a different outside facet it counts coordinate `0` together with the
coordinate omitted by that outside facet. -/
def qsOtherFacetPairWeight : ToricFacet → Fin 4 → ℤ
  | .qs => ![1, 0, 0, 0]
  | .pr => ![1, 1, 0, 0]
  | .sp => ![1, 0, 1, 0]
  | .rq => ![1, 0, 0, 1]

/-- Literal pair degree corresponding to `qsOtherFacetPairWeight`. -/
def qsOtherFacetPairDegree (next : ToricFacet) (e : Fin 4 →₀ ℕ) : ℤ :=
  match next with
  | .qs => (e 0 : ℤ)
  | .pr => (e 0 : ℤ) + (e 1 : ℤ)
  | .sp => (e 0 : ℤ) + (e 2 : ℤ)
  | .rq => (e 0 : ℤ) + (e 3 : ℤ)

@[simp]
theorem finsupp_weight_qsOtherFacetPairWeight
    (next : ToricFacet) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (qsOtherFacetPairWeight next) e =
      qsOtherFacetPairDegree next e := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    cases next <;>
      simp [qsOtherFacetPairWeight, qsOtherFacetPairDegree]
  · intro i
    simp

/-- The neutral pair weight has coordinate sum exactly two on every genuine
other-facet branch. -/
theorem sum_qsOtherFacetPairWeight_eq_two
    (next : ToricFacet) (hne : next ≠ .qs) :
    ∑ i : Fin 4, qsOtherFacetPairWeight next i = 2 := by
  cases next <;> simp_all [qsOtherFacetPairWeight, Fin.sum_univ_four]

/-- A strict-low source exponent with coordinate `0 >= 2` lies strictly above
pair degree one for every genuine other-facet choice. -/
theorem one_lt_qsOtherFacetPairDegree_of_two_le_zeroCoordinate
    (next : ToricFacet) (hne : next ≠ .qs)
    (e : Fin 4 →₀ ℕ) (he0 : 2 ≤ e (0 : Fin 4)) :
    1 < qsOtherFacetPairDegree next e := by
  have he0z : (2 : ℤ) ≤ (e (0 : Fin 4) : ℤ) := by
    exact_mod_cast he0
  cases next
  · exact (hne rfl).elim
  · have hnonneg : (0 : ℤ) ≤ (e (1 : Fin 4) : ℤ) := by positivity
    simp [qsOtherFacetPairDegree]
    omega
  · have hnonneg : (0 : ℤ) ≤ (e (2 : Fin 4) : ℤ) := by positivity
    simp [qsOtherFacetPairDegree]
    omega
  · have hnonneg : (0 : ℤ) ≤ (e (3 : Fin 4) : ℤ) := by positivity
    simp [qsOtherFacetPairDegree]
    omega

/-- On the actual degree-one lower ray the other-facet pair degree is exactly
one.  This is the arithmetic reason the subsequent perturbation is
Hessian-clock neutral. -/
theorem qs_ray_otherFacet_pairDegree_eq_one_of_mem
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ C.ray.face.support) :
    qsOtherFacetPairDegree next e = 1 := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree

  have hfacetPair : qsOtherFacetPairDegree next C.ray.facetExponent = 1 := by
    cases next
    · exact (hne rfl).elim
    · have hbase := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
      simp [qsOtherFacetPairDegree, hfacet0, hbase.1]
    · have hbase := C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree
      simp [qsOtherFacetPairDegree, hfacet0, hbase.1]
    · have hbase := C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree
      simp [qsOtherFacetPairDegree, hfacet0, hbase.1]

  have houtPair : qsOtherFacetPairDegree next C.ray.outsideExponent = 1 := by
    cases next
    · exact (hne rfl).elim
    · have hout := (HC4.Newton.mvRankThreeOnFacet_iff .pr
          C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout1, _hout0, _hout2, _hout3⟩
      simp [qsOtherFacetPairDegree, hout0, hout1]
    · have hout := (HC4.Newton.mvRankThreeOnFacet_iff .sp
          C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout2, _hout0, _hout1, _hout3⟩
      simp [qsOtherFacetPairDegree, hout0, hout2]
    · have hout := (HC4.Newton.mvRankThreeOnFacet_iff .rq
          C.ray.outsideExponent).1 houtThree
      rcases hout with ⟨hout3, _hout0, _hout1, _hout2⟩
      simp [qsOtherFacetPairDegree, hout0, hout3]

  have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hidx : e (0 : Fin 4) ∈ C.ray.zeroCoefficientPolynomial.support :=
    C.ray.zeroCoefficientPolynomial_mem_of_face_mem he
  have hle : e (0 : Fin 4) ≤ 1 := by
    rw [← hdeg]
    exact Polynomial.le_natDegree_of_mem_supp _ hidx
  rcases Nat.eq_zero_or_pos (e (0 : Fin 4)) with he0 | hepos
  · have heq : e = C.ray.facetExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq he C.ray.facet_mem_face
        (he0.trans hfacet0.symm)
    rw [heq]
    exact hfacetPair
  · have he1 : e (0 : Fin 4) = 1 := by omega
    have heq : e = C.ray.outsideExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq he C.ray.outside_mem_face
        (by simpa [he1, hout0])
    rw [heq]
    exact houtPair

/-- Linearisation of the combined primary/pair weight on finite exponents. -/
theorem finsupp_weight_qsOtherFacetPair_combination
    (A B : ℤ) (w : Fin 4 → ℤ) (next : ToricFacet)
    (e : Fin 4 →₀ ℕ) :
    Finsupp.weight
        (fun i => A * w i + B * qsOtherFacetPairWeight next i) e =
      A * Finsupp.weight w e + B * qsOtherFacetPairDegree next e := by
  calc
    Finsupp.weight
        (fun i => A * w i + B * qsOtherFacetPairWeight next i) e =
      A * Finsupp.weight w e +
        Finsupp.weight (fun i => B * qsOtherFacetPairWeight next i) e := by
          exact HC4.Newton.finsupp_weight_fin4_linear_combination
            A w (fun i => B * qsOtherFacetPairWeight next i) e
    _ = A * Finsupp.weight w e +
        B * Finsupp.weight (qsOtherFacetPairWeight next) e := by
          have h := HC4.Newton.finsupp_weight_fin4_linear_combination
            B (qsOtherFacetPairWeight next) (fun _ => 0) e
          have hzero :
              Finsupp.weight (fun _ : Fin 4 => (0 : ℤ)) e = 0 := by
            simp [Finsupp.weight_apply]
          simpa [hzero] using h
    _ = _ := by rw [finsupp_weight_qsOtherFacetPairWeight]

/-- The exact source-facing carrier produced by the neutral first-superface
construction. -/
structure QsOtherFacetNeutralSuperfacePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet) where
  weight : Fin 4 → ℤ
  level : ℤ
  carrier : MvPolynomial (Fin 4) K
  carrier_eq_initialForm :
    carrier = HC4.Polynomial.initialForm weight level
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  source_bound : HC4.Polynomial.IsWeightLE weight level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  ray_support_subset :
    (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
      (↑carrier.support : Set (Fin 4 →₀ ℕ))
  strict_superface :
    ∃ e, e ∈ carrier.support ∧ e ∉ C.ray.face.support
  nonlinear_pair_exit :
    ∃ e, e ∈ carrier.support ∧ 1 < qsOtherFacetPairDegree next e
  hessianClock_pos :
    0 < 4 * level - 2 * ∑ i : Fin 4, weight i
  hessian_zero : HC4.Polynomial.hessianDeterminant carrier = 0

/-- **A19 source-honest neutral-superface theorem.**  Every surviving
rank-three other-facet lower ray sits strictly inside a larger exact source
initial form.  The larger carrier contains a pair-degree `> 1` monomial and is
Hessian singular for the honest determinant-one source reason. -/
theorem qs_ray_otherFacet_neutralSuperface_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    Nonempty (QsOtherFacetNeutralSuperfacePackage C next) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  rcases C.qs_ray_otherFacet_rayReverseRees_package hthree hne houtThree with
    ⟨R⟩
  let w : Fin 4 → ℤ := fun i => (R.weight i : ℤ)
  let c : ℤ := (R.level : ℤ)
  let pair : Fin 4 → ℤ := qsOtherFacetPairWeight next
  let v : (Fin 4 →₀ ℕ) → ℤ := fun e => -qsOtherFacetPairDegree next e
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
    omega

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
    simp [v, d, hp]

  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨exit, hexitSource, _hexitDegree, hexit0, _hexitCodim⟩
  have hexitPair : 1 < qsOtherFacetPairDegree next exit :=
    one_lt_qsOtherFacetPairDegree_of_two_le_zeroCoordinate
      next hne exit hexit0
  have hexitNotRay : exit ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) := by
    intro hmem
    have hp := C.qs_ray_otherFacet_pairDegree_eq_one_of_mem
      hthree hne houtThree (by simpa using hmem)
    omega
  have hexitV : v exit < d := by
    simp [v, d]
    omega
  have hexit : ∃ e ∈ F.support,
      e ∉ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ∧ v e < d := by
    exact ⟨exit, hexitSource, hexitNotRay, hexitV⟩

  rcases HC4.Newton.exists_first_exposed_superface
      F.support hRay hvRay hexit with
    ⟨A, B, G, hA, hB, hG, hRayG, hnew⟩

  let W : Fin 4 → ℤ :=
    fun i => A * w i + B * pair i
  let L : ℤ := A * c + B

  have hweightFunction :
      (fun e : Fin 4 →₀ ℕ => Finsupp.weight W e) =
        (fun e => A * Finsupp.weight w e - B * v e) := by
    funext e
    rw [show Finsupp.weight W e =
        A * Finsupp.weight w e +
          B * qsOtherFacetPairDegree next e by
      simpa [W, pair] using
        (finsupp_weight_qsOtherFacetPair_combination A B w next e)]
    simp [v]

  have hG' :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ)) G
        (fun e => Finsupp.weight W e) L := by
    rw [hweightFunction]
    simpa [L, d] using hG

  have hWBound : HC4.Polynomial.IsWeightLE W L F := by
    intro e he
    exact hG'.weight_le (by simpa using he)

  let carrier : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.initialForm W L F
  have hCarrierFace :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑carrier.support : Set (Fin 4 →₀ ℕ))
        (fun e => Finsupp.weight W e) L := by
    simpa [carrier] using
      (HC4.Newton.initialForm_support_isExposedFace W L F hWBound)
  have hsupport :
      (↑carrier.support : Set (Fin 4 →₀ ℕ)) = G := by
    ext e
    constructor
    · intro he
      exact hG'.mem_iff.mpr (hCarrierFace.mem_iff.mp he)
    · intro he
      exact hCarrierFace.mem_iff.mpr (hG'.mem_iff.mp he)

  have hRayCarrier :
      (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) ⊆
        (↑carrier.support : Set (Fin 4 →₀ ℕ)) := by
    intro e he
    rw [hsupport]
    exact hRayG he

  rcases hnew with ⟨eNew, heNewG, heNewNotRay⟩
  have heNewSource : eNew ∈ (↑F.support : Set (Fin 4 →₀ ℕ)) :=
    hG'.subset heNewG
  have heNewPrimaryLe : Finsupp.weight w eNew ≤ c :=
    hRay.weight_le heNewSource
  have heNewPrimaryNe : Finsupp.weight w eNew ≠ c := by
    intro heq
    apply heNewNotRay
    exact hRay.mem_iff.mpr ⟨heNewSource, heq⟩
  have heNewPrimaryLt : Finsupp.weight w eNew < c := by omega
  have heNewCombined := hG.weight_eq heNewG
  have heNewPair : 1 < qsOtherFacetPairDegree next eNew := by
    dsimp [v, d] at heNewCombined
    nlinarith
  have heNewCarrier : eNew ∈ carrier.support := by
    have : eNew ∈ (↑carrier.support : Set (Fin 4 →₀ ℕ)) := by
      rw [hsupport]
      exact heNewG
    simpa using this

  have hsumPair : ∑ i : Fin 4, pair i = 2 := by
    simpa [pair] using sum_qsOtherFacetPairWeight_eq_two next hne
  have hsumW :
      ∑ i : Fin 4, W i =
        A * (∑ i : Fin 4, w i) + B * 2 := by
    dsimp [W]
    rw [Fin.sum_univ_four] at hsumPair
    rw [Fin.sum_univ_four]
    rw [Fin.sum_univ_four]
    ring_nf at hsumPair ⊢
    nlinarith

  have hbaseLtNat :
      2 * ∑ i : Fin 4, R.weight i < 4 * R.level :=
    Nat.sub_pos_iff_lt.mp R.defect_pos
  have hbaseLt :
      (2 : ℤ) * ∑ i : Fin 4, w i < 4 * c := by
    dsimp [w, c]
    rw [Fin.sum_univ_four] at hbaseLtNat ⊢
    exact_mod_cast hbaseLtNat
  have hbaseClock :
      0 < 4 * c - 2 * ∑ i : Fin 4, w i := by omega
  have hclockEq :
      4 * L - 2 * ∑ i : Fin 4, W i =
        A * (4 * c - 2 * ∑ i : Fin 4, w i) := by
    rw [hsumW]
    dsimp [L]
    ring
  have hclock : 0 < 4 * L - 2 * ∑ i : Fin 4, W i := by
    rw [hclockEq]
    exact mul_pos hA hbaseClock

  have hdetF : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := hdetF
  have hdetComponent :
      HC4.Polynomial.initialForm W
        (4 * L - 2 * ∑ i : Fin 4, W i)
        (HC4.Polynomial.hessianDeterminant F) = 0 := by
    exact HC4.MongeAmpere.initialForm_hessianDeterminant_eq_zero
      hMA (ne_of_gt hclock)
  have hcarrierZero : HC4.Polynomial.hessianDeterminant carrier = 0 := by
    have hcompat :=
      HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
        W L F hWBound
    rw [← hcompat]
    simpa using hdetComponent

  refine ⟨{
    weight := W
    level := L
    carrier := carrier
    carrier_eq_initialForm := by rfl
    source_bound := hWBound
    ray_support_subset := hRayCarrier
    strict_superface := ⟨eNew, heNewCarrier, ?_⟩
    nonlinear_pair_exit := ⟨eNew, heNewCarrier, heNewPair⟩
    hessianClock_pos := hclock
    hessian_zero := hcarrierZero
  }⟩
  exact heNewNotRay

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation