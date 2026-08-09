import HC4.Valuation.DefectRetainingDepartureFrontier
import Mathlib.Tactic

/-!
# Exact parameter-layer extraction

`firstPositiveParameterOrder` in `DefectRetainingDepartureFrontier` records
least positive *X-adic valuation* among the source coefficients.  That is a
useful divisibility clock, but it is deliberately not the same thing as the
least positive parameter exponent occurring anywhere in the family: a
coefficient such as `1 + X^5` has valuation zero while still carrying a
nonzero fifth parameter layer.

This file adds the exact finite layer selector needed by the first Schur
departure argument.  It takes the union of the polynomial supports of all
source coefficients, hence records every parameter exponent that actually
occurs.  It also reconstructs the corresponding coefficient potential
`P_j : MvPolynomial (Fin 4) K`.

No geometric identification with the first non-one-sided Schur departure is
asserted here.  The point is to make the correct finite object available to
that theorem, so the next local bridge no longer has to reconstruct it.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- The coefficient potential at exact parameter exponent `j`.

If

    P = sum_j X^j P_j,

then `familyParameterLayer P j` is `P_j`.

The pinned mathlib version exposes coefficient-wise transport of a `Finsupp`
through `Finsupp.mapRange`; this is exactly the operation required here. -/
noncomputable def familyParameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : ℕ) :
    MvPolynomial (Fin 4) K :=
  Finsupp.mapRange
    (fun c : Polynomial K => c.coeff j)
    (by simp)
    P

/-- Coefficients of the reconstructed parameter layer are exactly the
`j`th coefficients of the coefficient-ring polynomials. -/
theorem familyParameterLayer_coeff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : ℕ)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (familyParameterLayer P j) =
      (MvPolynomial.coeff d P).coeff j := by
  simpa [familyParameterLayer] using
    (MvPolynomial.coeff_mapRange
      (fun c : Polynomial K => c.coeff j)
      (by simp)
      P d)

/-- All parameter exponents that occur in at least one source coefficient. -/
noncomputable def familyParameterLayerOrders
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset ℕ := by
  classical
  exact
    P.support.biUnion fun d =>
      (MvPolynomial.coeff d P).support

/-- Membership in the exact layer-order set has an actual source-monomial
witness. -/
theorem mem_familyParameterLayerOrders_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (j : ℕ) :
    j ∈ familyParameterLayerOrders P ↔
      ∃ d ∈ P.support,
        (MvPolynomial.coeff d P).coeff j ≠ 0 := by
  classical
  simp [familyParameterLayerOrders, Polynomial.mem_support_iff]

/-- An occurring parameter exponent reconstructs a nonzero coefficient
potential. -/
theorem familyParameterLayer_ne_zero_of_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {j : ℕ}
    (hj : j ∈ familyParameterLayerOrders P) :
    familyParameterLayer P j ≠ 0 := by
  rcases (mem_familyParameterLayerOrders_iff P j).1 hj with
    ⟨d, _hd, hcoeff⟩
  intro hzero
  have h := congrArg (MvPolynomial.coeff d) hzero
  rw [familyParameterLayer_coeff] at h
  simp only [MvPolynomial.coeff_zero] at h
  exact hcoeff h

/-- Strictly positive parameter exponents that actually occur anywhere in
the family. -/
noncomputable def familyPositiveActualLayerOrders
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset ℕ :=
  (familyParameterLayerOrders P).filter (fun j => 0 < j)

/-- There is an actual nonconstant parameter layer. -/
def HasPositiveActualParameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  (familyPositiveActualLayerOrders P).Nonempty

/-- Least strictly positive parameter exponent occurring in the family. -/
noncomputable def firstPositiveActualParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) : ℕ :=
  (familyPositiveActualLayerOrders P).min' h

theorem firstPositiveActualParameterOrder_mem
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    firstPositiveActualParameterOrder P h ∈
      familyPositiveActualLayerOrders P := by
  unfold firstPositiveActualParameterOrder
  exact Finset.min'_mem _ h

/-- The exact selected exponent is strictly positive. -/
theorem firstPositiveActualParameterOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    0 < firstPositiveActualParameterOrder P h := by
  have hmem := firstPositiveActualParameterOrder_mem P h
  exact (Finset.mem_filter.mp hmem).2

/-- The exact first later layer is a nonzero multivariate potential. -/
theorem firstPositiveActualParameterLayer_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    familyParameterLayer P
        (firstPositiveActualParameterOrder P h) ≠ 0 := by
  have hmem := firstPositiveActualParameterOrder_mem P h
  exact
    familyParameterLayer_ne_zero_of_mem P
      (Finset.mem_filter.mp hmem).1

/-- The exact first later layer is realised by a source monomial and a
nonzero coefficient at that exact parameter exponent. -/
theorem firstPositiveActualParameterOrder_realised
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    ∃ d ∈ P.support,
      (MvPolynomial.coeff d P).coeff
          (firstPositiveActualParameterOrder P h) ≠ 0 := by
  have hmem := firstPositiveActualParameterOrder_mem P h
  exact
    (mem_familyParameterLayerOrders_iff
      P (firstPositiveActualParameterOrder P h)).1
      (Finset.mem_filter.mp hmem).1

/-- Every other positive exponent actually occurring in the family is at
least the selected first exponent. -/
theorem firstPositiveActualParameterOrder_le
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {j : ℕ}
    (hj : j ∈ familyParameterLayerOrders P)
    (hpos : 0 < j) :
    firstPositiveActualParameterOrder P h ≤ j := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hj, hpos⟩

/-- Correct preterminal/closing trichotomy for the *actual* parameter
layers of a departure-ready frontier. -/
theorem CanonicalSmithDepartureFrontier.actualParameterClock_trichotomy
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier
      (K := K) D complexity) :
    (¬ HasPositiveActualParameterLayer f.lossless.family) ∨
      (∃ h : HasPositiveActualParameterLayer f.lossless.family,
        firstPositiveActualParameterOrder f.lossless.family h < f.defect) ∨
      (∃ h : HasPositiveActualParameterLayer f.lossless.family,
        f.defect ≤
          firstPositiveActualParameterOrder f.lossless.family h) := by
  classical
  by_cases h :
      HasPositiveActualParameterLayer f.lossless.family
  · rcases lt_or_ge
      (firstPositiveActualParameterOrder f.lossless.family h)
      f.defect with hpre | hclose
    · exact Or.inr (Or.inl ⟨h, hpre⟩)
    · exact Or.inr (Or.inr ⟨h, hclose⟩)
  · exact Or.inl h

end

end HC4.Valuation
