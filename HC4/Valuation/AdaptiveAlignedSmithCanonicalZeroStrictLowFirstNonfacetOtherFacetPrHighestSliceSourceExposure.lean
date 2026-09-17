import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarHighestPairSlice
import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import Mathlib.Tactic

/-!
# Direct source exposure of the `.pr` highest pair slice

The planar carrier is already an exact positive weighted initial form of the
represented determinant-one source.  The highest pair slice is in turn an
exact pair-weight initial form of that carrier.  Finite lexicographic exposed-
face refinement collapses these two nested exposures into one exact source
exposure.

Because the primary source exposure has strictly positive coordinate weights,
positive level, and positive Hessian clock, the generic positive refinement
theorem chooses the lexicographic scale so that all three properties survive.
Thus the highest pair slice can be used directly as the special fibre of an
honest bounded reverse-Rees family of the represented source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Combined coordinate weight obtained by making the planar-carrier exposure
primary and pair degree secondary. -/
def prHighestSliceCombinedWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (M : ℕ) (i : Fin 4) : ℤ :=
  (M : ℤ) * P.finalWeight i + qsOtherFacetPairWeight .pr i

/-- Combined level corresponding to `prHighestSliceCombinedWeight`. -/
def prHighestSliceCombinedLevel
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (M : ℕ) : ℤ :=
  (M : ℤ) * P.finalLevel + S.pairLevel

/-- Exact positive source exposure of a stored `.pr` highest pair slice. -/
structure QsOtherFacetPrHighestSliceSourceExposure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P) where
  scale : ℕ
  scale_pos : 0 < scale
  exposed :
    HC4.Newton.IsExposedFace
      (↑(polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support : Set (Fin 4 →₀ ℕ))
      (↑S.slice.support : Set (Fin 4 →₀ ℕ))
      (fun e => Finsupp.weight (prHighestSliceCombinedWeight P scale) e)
      (prHighestSliceCombinedLevel S scale)
  weight_pos :
    ∀ i : Fin 4, 0 < prHighestSliceCombinedWeight P scale i
  level_pos : 0 < prHighestSliceCombinedLevel S scale
  hessianClock_pos :
    0 < 4 * prHighestSliceCombinedLevel S scale -
      2 * ∑ i : Fin 4, prHighestSliceCombinedWeight P scale i
  initialForm_eq :
    HC4.Polynomial.initialForm
      (prHighestSliceCombinedWeight P scale)
      (prHighestSliceCombinedLevel S scale)
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) =
    S.slice

namespace QsOtherFacetPrHighestSliceSourceExposure

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}

/-- Global represented-source bound for the collapsed highest-slice exposure. -/
theorem source_bound
    (E : QsOtherFacetPrHighestSliceSourceExposure P S) :
    HC4.Polynomial.IsWeightLE
      (prHighestSliceCombinedWeight P E.scale)
      (prHighestSliceCombinedLevel S E.scale)
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro e he
  exact E.exposed.weight_le (by simpa using he)

end QsOtherFacetPrHighestSliceSourceExposure

/-- **Nested highest-slice exposures collapse to one honest positive source
exposure.** -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.exists_pr_sourceExposure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P) :
    Nonempty (QsOtherFacetPrHighestSliceSourceExposure P S) := by
  classical
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family

  have hsliceNonempty : S.slice.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr S.slice_ne_zero
  rcases hsliceNonempty with ⟨e, he⟩
  have heSource : e ∈ F.support := by
    dsimp [F]
    exact (S.support_source_and_finalLevel he).1
  have hsourceNonempty : F.support.Nonempty := ⟨e, heSource⟩

  have hP :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑P.carrier.support : Set (Fin 4 →₀ ℕ))
        (fun d => Finsupp.weight P.finalWeight d) P.finalLevel := by
    have h := HC4.Newton.initialForm_support_isExposedFace
      P.finalWeight P.finalLevel F P.source_bound
    rw [← P.carrier_eq_initialForm] at h
    exact h

  have hS :
      HC4.Newton.IsExposedFace
        (↑P.carrier.support : Set (Fin 4 →₀ ℕ))
        (↑S.slice.support : Set (Fin 4 →₀ ℕ))
        (fun d => Finsupp.weight (qsOtherFacetPairWeight .pr) d)
        S.pairLevel := by
    have h := HC4.Newton.initialForm_support_isExposedFace
      (qsOtherFacetPairWeight .pr) S.pairLevel P.carrier
      S.carrier_pair_bound
    rw [← S.slice_eq_initialForm] at h
    exact h

  rcases HC4.Newton.exists_nat_refine_exposed_face_fin4_positive_clock
      F.support hsourceNonempty hP hS
      P.finalWeight_pos P.finalLevel_pos P.hessianClock_pos with
    ⟨M, hM, hface, hweightPos, hlevelPos, hclockPos⟩

  have hface' :
      HC4.Newton.IsExposedFace
        (↑F.support : Set (Fin 4 →₀ ℕ))
        (↑S.slice.support : Set (Fin 4 →₀ ℕ))
        (fun d => Finsupp.weight (prHighestSliceCombinedWeight P M) d)
        (prHighestSliceCombinedLevel S M) := by
    simpa [prHighestSliceCombinedWeight, prHighestSliceCombinedLevel] using hface

  have hinit :
      HC4.Polynomial.initialForm
        (prHighestSliceCombinedWeight P M)
        (prHighestSliceCombinedLevel S M) F = S.slice := by
    exact HC4.Newton.initialForm_eq_of_exposedSupport_and_coeff
      (prHighestSliceCombinedWeight P M)
      (prHighestSliceCombinedLevel S M)
      F S.slice hface'
      (fun d hd => S.coeff_eq_source_of_mem hd)

  exact ⟨{
    scale := M
    scale_pos := hM
    exposed := by simpa [F] using hface'
    weight_pos := by
      simpa [prHighestSliceCombinedWeight] using hweightPos
    level_pos := by
      simpa [prHighestSliceCombinedLevel] using hlevelPos
    hessianClock_pos := by
      simpa [prHighestSliceCombinedWeight, prHighestSliceCombinedLevel] using hclockPos
    initialForm_eq := by simpa [F] using hinit
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
