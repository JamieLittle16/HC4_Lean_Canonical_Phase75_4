import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactSingularity
import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingActualLayer
import Mathlib.Tactic

/-!
# A19.101: honest reverse Rees family of the integral lower `qs` contact

A19.97 bounds the actual represented zero-clock source by the integral contact
weight `ordinaryDegree4 d + r*d₀ <= D`, with `r >= 2`.  A19.R1 turns exactly
such a bounded filtration into an honest polynomial family.  This file records
the corresponding contact family and its positive pure Hessian clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Natural variable weights for the integral lower `.qs` contact.  Their
monomial weight is `ordinaryDegree4 d + r*d₀`. -/
def qsIntegralContactWeight (r : ℕ) (i : Fin 4) : ℕ :=
  if i = 0 then r + 1 else 1

@[simp] theorem qsIntegralContactWeight_zero (r : ℕ) :
    qsIntegralContactWeight r (0 : Fin 4) = r + 1 := by
  simp [qsIntegralContactWeight]

@[simp] theorem qsIntegralContactWeight_one (r : ℕ) :
    qsIntegralContactWeight r (1 : Fin 4) = 1 := by
  simp [qsIntegralContactWeight]

@[simp] theorem qsIntegralContactWeight_two (r : ℕ) :
    qsIntegralContactWeight r (2 : Fin 4) = 1 := by
  simp [qsIntegralContactWeight]

@[simp] theorem qsIntegralContactWeight_three (r : ℕ) :
    qsIntegralContactWeight r (3 : Fin 4) = 1 := by
  simp [qsIntegralContactWeight]

/-- Exact natural weighted degree of a source exponent. -/
theorem qsIntegralContactWeight_finsupp
    (r : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (qsIntegralContactWeight r) d =
      HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [qsIntegralContactWeight, HC4.Polynomial.ordinaryDegree4]
    ring
  · intro i
    simp

/-- Sum of the four contact variable weights. -/
theorem qsIntegralContactWeight_sum (r : ℕ) :
    ∑ i : Fin 4, qsIntegralContactWeight r i = r + 4 := by
  rw [Fin.sum_univ_four]
  simp [qsIntegralContactWeight]

/-- After casting to integers, the natural contact weights are exactly the
existing denominator-cleared contact weight with `scale = 1`. -/
theorem qsIntegralContactWeight_cast_eq_scaledContactWeight (r : ℕ) :
    (fun i : Fin 4 => (qsIntegralContactWeight r i : ℤ)) =
      HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r := by
  funext i
  fin_cases i <;>
    simp [qsIntegralContactWeight, HC4.Newton.scaledContactWeight] <;> ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **A19.101 contact-Rees package.**  A surviving lower `.qs` other-facet
endpoint determines one integral slope `r >= 2` and an honest reverse Rees
family whose special fibre is the actual singular weighted-contact face, whose
Hessian determinant is a positive pure parameter power, and which therefore
has a positive actual source layer. -/
theorem qs_ray_otherFacet_contactRees_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ r : ℕ,
      ∃ hbound : HasReverseWeightBound
          (qsIntegralContactWeight r) T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family),
        2 ≤ r ∧
        C.bump = C.scale * r ∧
        (∀ {d : Fin 4 →₀ ℕ},
          d ∈ (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support →
          HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) ≤
            T.topFace.degree) ∧
        polynomialFamilySpecialFiber
            (reverseWeightedReesFamily
              (qsIntegralContactWeight r) T.topFace.degree
              (polynomialFamilySpecialFiber
                T.terminal.blocker.presented.family) hbound) =
          HC4.Polynomial.initialForm
            (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
            (T.topFace.degree : ℤ)
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family) ∧
        HC4.Polynomial.hessianDeterminant
            (polynomialFamilySpecialFiber
              (reverseWeightedReesFamily
                (qsIntegralContactWeight r) T.topFace.degree
                (polynomialFamilySpecialFiber
                  T.terminal.blocker.presented.family) hbound)) = 0 ∧
        HasPolynomialFamilyHessianDefect (K := K)
            (reverseWeightedReesFamily
              (qsIntegralContactWeight r) T.topFace.degree
              (polynomialFamilySpecialFiber
                T.terminal.blocker.presented.family) hbound)
            (4 * T.topFace.degree - 2 * (r + 4)) ∧
        0 < 4 * T.topFace.degree - 2 * (r + 4) ∧
        HasPositiveActualParameterLayer
            (reverseWeightedReesFamily
              (qsIntegralContactWeight r) T.topFace.degree
              (polynomialFamilySpecialFiber
                T.terminal.blocker.presented.family) hbound) := by
  rcases C.qs_ray_otherFacet_integral_locked_source_contact
      hthree hne houtThree with
    ⟨r, hr, hbump, hsource0, _hray, _hlock⟩
  have hsource :
      ∀ {d : Fin 4 →₀ ℕ},
        d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support →
        HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) ≤
          T.topFace.degree := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hsource0
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let D : ℕ := T.topFace.degree
  have hbound : HasReverseWeightBound (qsIntegralContactWeight r) D F := by
    intro d hd
    rw [qsIntegralContactWeight_finsupp]
    exact hsource hd
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, _hcodim⟩
  have hdcontact := hsource hd
  have hrle : r ≤ r * d (0 : Fin 4) := by
    have hd0one : 1 ≤ d (0 : Fin 4) := by omega
    simpa using Nat.mul_le_mul_left r hd0one
  have hcontact : r + 3 ≤ D := by
    dsimp [D]
    omega
  have hsum : ∑ i : Fin 4, qsIntegralContactWeight r i = r + 4 :=
    qsIntegralContactWeight_sum r
  have hnonneg :
      2 * ∑ i : Fin 4, qsIntegralContactWeight r i ≤ 4 * D := by
    rw [hsum]
    omega
  have hDelta : 0 < 4 * D - 2 * (r + 4) := by
    omega
  have hdetF : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hdef :
      HasPolynomialFamilyHessianDefect (K := K)
        (reverseWeightedReesFamily
          (qsIntegralContactWeight r) D F hbound)
        (4 * D - 2 * (r + 4)) := by
    have h := reverseWeightedReesFamily_hasHessianDefect
      (K := K) (qsIntegralContactWeight r) D F hbound hdetF hnonneg
    rw [hsum] at h
    exact h
  have hspecial :
      polynomialFamilySpecialFiber
          (reverseWeightedReesFamily
            (qsIntegralContactWeight r) D F hbound) =
        HC4.Polynomial.initialForm
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
          (D : ℤ) F := by
    rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
    rw [qsIntegralContactWeight_cast_eq_scaledContactWeight]
  have hLE : HC4.Polynomial.IsWeightLE
      (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r) (D : ℤ) F := by
    rw [HC4.Newton.isWeightLE_scaledContactWeight_iff]
    intro e he
    have hnat :
        HC4.Polynomial.ordinaryDegree4 e + r * e (0 : Fin 4) ≤ D :=
      hsource he
    unfold HC4.Newton.scaledContactExponentWeight
    have hz :
        (HC4.Polynomial.ordinaryDegree4 e : ℤ) +
            (r : ℤ) * (e (0 : Fin 4) : ℤ) ≤ (D : ℤ) := by
      exact_mod_cast hnat
    simpa using hz
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hcontactZero :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 r)
          (D : ℤ) F) = 0 := by
    exact HC4.Newton.scaledContact_hessianDeterminant_eq_zero_of_isWeightLE
      (j := (0 : Fin 4)) (level := D) (scale := 1) (bump := r)
      (ψ := F) (by norm_num) (by simpa using hcontact) hLE hMA
  have hspecialZero :
      HC4.Polynomial.hessianDeterminant
          (polynomialFamilySpecialFiber
            (reverseWeightedReesFamily
              (qsIntegralContactWeight r) D F hbound)) = 0 := by
    rw [hspecial]
    exact hcontactZero
  have hpositive :
      HasPositiveActualParameterLayer
        (reverseWeightedReesFamily
          (qsIntegralContactWeight r) D F hbound) :=
    hasPositiveActualParameterLayer_of_hessianDefect_pos
      _ hdef hDelta
  refine ⟨r, hbound, hr, hbump, ?_, ?_, ?_, ?_, ?_, hpositive⟩
  · exact hsource
  · simpa [F, D] using hspecial
  · simpa [F, D] using hspecialZero
  · simpa [F, D] using hdef
  · simpa [D] using hDelta

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
