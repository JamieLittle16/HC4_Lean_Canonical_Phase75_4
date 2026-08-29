import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralLockedFrontier
import Mathlib.Tactic

/-!
# A19.100: the actual integral first-contact face is Hessian singular

A19.97/A19.98 normalize the genuine lower `.qs` first contact to an integral
slope `r >= 2` on the represented zero-clock special fibre:

    ordinaryDegree4 d + r*d[0] <= D.

This is exactly the existing cleared contact weight with `scale = 1` and
`bump = r`.  The retained strict-low source witness has ordinary degree at
least three and omitted-coordinate multiplicity at least two, so the genuine
contact inequality `r + 3 <= D` required by the generic scaled-contact Hessian
theorem follows immediately.

The special fibre is polynomial Monge--Ampere because its Hessian determinant
is exactly one at raw defect zero.  Hence the actual integral weighted contact
initial form is Hessian singular by the already-proved generic first-contact
theorem.

No planar terminal, balance hypothesis, new carrier, or progress measure is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

-- CI anchor: compile the source-native weighted-contact singularity.

/-- **A19.100 source-native weighted-contact singularity.**  In the genuine
lower `.qs` other-facet branch, the integral contact slope exposes a maximal
weighted initial form of the actual represented special fibre whose Hessian
determinant is zero. -/
theorem qs_ray_otherFacet_weightedContact_hessianDeterminant_eq_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      HC4.Polynomial.IsWeightLE
        (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
        (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
          (T.topFace.degree : ℤ)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family)) = 0 := by
  rcases C.qs_ray_otherFacet_integral_locked_source_contact
      hthree hne houtThree with
    ⟨r, hr, _hbump, hsource, _hray, _hlock⟩
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let D : ℕ := T.topFace.degree
  have hLE : HC4.Polynomial.IsWeightLE
      (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r) (D : ℤ) F := by
    rw [HC4.Newton.isWeightLE_scaledContactWeight_iff]
    intro d hd
    have h := hsource hd
    unfold HC4.Newton.scaledContactExponentWeight
    push_cast
    exact_mod_cast h
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, _hcodim⟩
  have hdcontact := hsource hd
  have hrle : r ≤ r * d (0 : Fin 4) := by
    have hd0one : 1 ≤ d (0 : Fin 4) := by omega
    simpa using Nat.mul_le_mul_left r hd0one
  have hcontact : r + 3 ≤ D := by
    dsimp [D]
    omega
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hzero :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
          (D : ℤ) F) = 0 := by
    exact HC4.Newton.scaledContact_hessianDeterminant_eq_zero_of_isWeightLE
      (j := (0 : Fin 4)) (level := D) (scale := 1) (bump := r)
      (ψ := F) (by norm_num) (by simpa using hcontact) hLE hMA
  exact ⟨r, hr, by simpa [F, D] using hLE, by simpa [F, D] using hzero⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
