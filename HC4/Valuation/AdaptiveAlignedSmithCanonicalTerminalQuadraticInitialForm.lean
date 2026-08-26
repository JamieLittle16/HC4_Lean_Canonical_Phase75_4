import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticWeight
import HC4.Newton.SmithRefinedFacePolynomial
import HC4.Newton.TerminalConformalWeight
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# A19.12: the terminal quadratic Smith face is the conformal initial form

A19.11 showed that every monomial of the full surviving terminal polynomial
has `(0,-1,-1,-2)`-weight at most `-2`.  This file identifies the equality
component exactly.

The canonical symmetric balanced Smith subface is precisely the set of
supported exponents of weight `-2`; hence its canonical Smith restriction is
literally the exact maximal initial form at that weight.  The same polynomial
is positively homogeneous of degree `2` for `(0,1,1,2)`.

This is a polynomial identity, not a rank-certificate reinterpretation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry

variable {RR : RepairRanking}
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {complexity : ℕ}
variable {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
  RR state complexity}

/-- The actual polynomial supported on the canonical balanced quadratic Smith
subface. -/
noncomputable def quadraticFace
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    MvPolynomial (Fin 4) K :=
  smithSubfacePolynomial (1 : Fin 4) 2 3
    (smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      0 (fun _ : SmithSupportExponent => (0 : ℤ)))
    T.specialFiber

/-- Positive conformal weighted degree written in the direct terminal API. -/
theorem terminalQuadraticPositiveWeight_integralWeightedDegree
    (d : Fin 4 →₀ ℕ) :
    integralWeightedDegree terminalQuadraticPositiveWeight d =
      (d (1 : Fin 4) : ℤ) + (d (2 : Fin 4) : ℤ) +
        2 * (d (3 : Fin 4) : ℤ) := by
  classical
  unfold integralWeightedDegree
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_four, terminalQuadraticPositiveWeight]
    ring
  · intro i
    simp

/-- On actual support, membership in the balanced Smith face is equivalent to
having maximal negative conformal weight `-2`. -/
theorem mem_balanced_iff_negativeWeight_eq_neg_two
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ T.specialFiber.support) :
    smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
        smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ)) ↔
      Finsupp.weight terminalQuadraticNegativeWeight d = -2 := by
  let e := smithSupportExponentOf (1 : Fin 4) 2 3 d
  have heproj :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  constructor
  · intro he
    have hq := G.quadratic e (by simpa [e] using he)
    have hq' :
        (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 2 ∧ d (3 : Fin 4) = 0) ∨
        (d (1 : Fin 4) = 1 ∧ d (2 : Fin 4) = 1 ∧ d (3 : Fin 4) = 0) ∨
        (d (1 : Fin 4) = 2 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) := by
      simpa [e, smithSupportExponentOf] using hq
    rw [terminalQuadraticNegativeWeight_finsupp]
    rcases hq' with h | h | h <;> rcases h with ⟨h1, h2, h3⟩ <;>
      simp [h1, h2, h3]
  · intro hweight
    have hdelta : smithSeparatorDelta 1 1 e = 0 := by
      rw [smithSeparatorDelta_one_one_eq_terminalQuadraticDegree]
      have hweight' := hweight
      rw [terminalQuadraticNegativeWeight_finsupp] at hweight'
      have hcoords :
          e.b = d (1 : Fin 4) ∧
          e.c = d (2 : Fin 4) ∧
          e.d = d (3 : Fin 4) := by
        simp [e, smithSupportExponentOf]
      rcases hcoords with ⟨hb, hc, hw⟩
      rw [hb, hc, hw]
      omega
    exact
      (mem_smithSymmetricBalancedSubface).2
        ⟨heproj, rfl, hdelta⟩

/-- **Exact polynomial identity:** the canonical quadratic Smith restriction
is the maximal negative-weight initial form of the actual terminal fibre. -/
theorem quadraticFace_eq_negativeInitialForm
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    G.quadraticFace =
      HC4.Polynomial.initialForm terminalQuadraticNegativeWeight (-2)
        T.specialFiber := by
  classical
  apply MvPolynomial.ext
  intro d
  unfold quadraticFace
  rw [coeff_smithSubfacePolynomial, HC4.Polynomial.coeff_initialForm]
  by_cases hcoeff : MvPolynomial.coeff d T.specialFiber = 0
  · simp [hcoeff]
  · have hd : d ∈ T.specialFiber.support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hiff := G.mem_balanced_iff_negativeWeight_eq_neg_two d hd
    by_cases hmem :
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
          smithSymmetricBalancedSubface
            (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
            0 (fun _ : SmithSupportExponent => (0 : ℤ))
    · have hw := hiff.mp hmem
      simp [hmem, hw]
    · have hw :
          Finsupp.weight terminalQuadraticNegativeWeight d ≠ -2 := by
        intro hw
        exact hmem (hiff.mpr hw)
      simp [hmem, hw]

/-- The same equality face is positively homogeneous of degree two for the
one-zero conformal weight `(0,1,1,2)`. -/
theorem quadraticFace_positiveHomogeneous
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    IsIntegralWeightedHomogeneous
      terminalQuadraticPositiveWeight 2 G.quadraticFace := by
  intro d hd
  unfold quadraticFace at hd
  rw [coeff_smithSubfacePolynomial] at hd
  split at hd
  · rename_i hmem
    have hq := G.quadratic _ hmem
    have hq' :
        (d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 2 ∧ d (3 : Fin 4) = 0) ∨
        (d (1 : Fin 4) = 1 ∧ d (2 : Fin 4) = 1 ∧ d (3 : Fin 4) = 0) ∨
        (d (1 : Fin 4) = 2 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) := by
      simpa [smithSupportExponentOf] using hq
    rw [terminalQuadraticPositiveWeight_integralWeightedDegree]
    rcases hq' with h | h | h <;> rcases h with ⟨h1, h2, h3⟩ <;>
      simp [h1, h2, h3]
  · exact (hd rfl).elim

end AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry

end

end HC4.Valuation
