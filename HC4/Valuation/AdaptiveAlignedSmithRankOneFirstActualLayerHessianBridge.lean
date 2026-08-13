import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerSupport
import Mathlib.Tactic

/-!
# First actual source layer -> first Hessian layer

The rank-one closing analysis now has an honest least positive source layer

    j = firstActualLayerOrder,

and in the preclosing branch `j < defect` the retained Schur clock is
transverse-tangential at that same order.  To use that information at the
polynomial-potential level we must identify the order-`j` Hessian coefficient
with the Hessian of the actual coefficient potential `P_j`.

This file supplies exactly that linear bridge.

The key observation is elementary but important for the formal architecture:
coefficient extraction in the family parameter commutes with every spatial
formal derivative.  Hence

    [tau^n] Hess(P(tau)) = Hess(P_n)

entrywise.  In particular, because `j` is the *first actual* positive source
layer, every positive Hessian layer below `j` is zero, while the layer at `j`
is exactly the Hessian of the special fibre of the relative deformation
quotient

    P = P_0 + tau^j Q,      Q_0 = P_j.

Thus the remaining preclosing tangency problem can be attacked directly on
`Hess(Q_0)` rather than through an abstract matrix-series coefficient.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Parameter layers commute with spatial differentiation -/

/-- Exact family-parameter coefficient extraction commutes with formal
spatial differentiation. -/
theorem familyParameterLayer_pderiv
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (i : Fin 4) :
    familyParameterLayer (MvPolynomial.pderiv i P) n =
      MvPolynomial.pderiv i (familyParameterLayer P n) := by
  classical
  ext d
  simp only [familyParameterLayer_coeff, coeff_pderiv_commRing]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Polynomial.coeff_mul_natCast (R := K)
      (p := MvPolynomial.coeff (d + Finsupp.single i 1) P)
      (a := d i + 1) (k := n))

/-- Consequently the `n`th parameter layer of a Hessian entry is the
corresponding Hessian entry of the `n`th coefficient potential. -/
theorem familyParameterLayer_hessian_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (i k : Fin 4) :
    familyParameterLayer (HC4.Polynomial.hessian P i k) n =
      HC4.Polynomial.hessian (familyParameterLayer P n) i k := by
  simp [HC4.Polynomial.hessian_apply, familyParameterLayer_pderiv]

/-- The complete coefficientwise Hessian layer. -/
noncomputable def familyParameterHessianLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) :=
  fun i k => familyParameterLayer (HC4.Polynomial.hessian P i k) n

/-- Matrix form of the source/Hessian coefficient bridge. -/
theorem familyParameterHessianLayer_eq_hessian
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    familyParameterHessianLayer P n =
      HC4.Polynomial.hessian (familyParameterLayer P n) := by
  apply Matrix.ext
  intro i k
  exact familyParameterLayer_hessian_apply P n i k

/-! ## No hidden Hessian layers before the first actual source layer -/

/-- Every strictly positive source coefficient layer below the least actual
positive layer is zero. -/
theorem familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {n : ℕ}
    (hnpos : 0 < n)
    (hnlt : n < firstPositiveActualParameterOrder P h) :
    familyParameterLayer P n = 0 := by
  classical
  ext d
  rw [familyParameterLayer_coeff]
  by_contra hcoeff
  have hd : d ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  have hnmem : n ∈ familyParameterLayerOrders P :=
    (mem_familyParameterLayerOrders_iff P n).2
      ⟨d, hd, hcoeff⟩
  have hfirstle :
      firstPositiveActualParameterOrder P h ≤ n :=
    firstPositiveActualParameterOrder_le P h hnmem hnpos
  omega

/-- Hence every positive Hessian coefficient layer below the first actual
source layer vanishes entrywise. -/
theorem familyParameterHessianLayer_eq_zero_of_pos_lt_firstPositiveActual
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {n : ℕ}
    (hnpos : 0 < n)
    (hnlt : n < firstPositiveActualParameterOrder P h) :
    familyParameterHessianLayer P n = 0 := by
  rw [familyParameterHessianLayer_eq_hessian]
  rw [familyParameterLayer_eq_zero_of_pos_lt_firstPositiveActual
    P h hnpos hnlt]
  ext i k
  simp [HC4.Polynomial.hessian_apply]

/-! ## Rank-one closing specialisation -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The first Hessian coefficient layer of the honest closing source is
literally the Hessian of its first actual source coefficient potential. -/
theorem firstActualLayer_hessian
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    familyParameterHessianLayer C.family C.firstActualLayerOrder =
      HC4.Polynomial.hessian
        (familyParameterLayer C.family C.firstActualLayerOrder) := by
  exact familyParameterHessianLayer_eq_hessian
    C.family C.firstActualLayerOrder

/-- There are no hidden positive Hessian layers before the honest first
actual source deformation. -/
theorem hessianLayer_eq_zero_of_pos_lt_firstActual
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hnpos : 0 < n)
    (hnlt : n < C.firstActualLayerOrder) :
    familyParameterHessianLayer C.family n = 0 := by
  simpa [firstActualLayerOrder] using
    familyParameterHessianLayer_eq_zero_of_pos_lt_firstPositiveActual
      C.family C.hasPositiveActualParameterLayer hnpos hnlt

/-- The Hessian of the special fibre of the relative first-deformation
quotient is exactly the first positive Hessian layer of the original honest
closing family. -/
theorem relativeFirstActualDeformation_specialFiber_hessian
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber
          C.relativeFirstActualDeformationFamily) =
      familyParameterHessianLayer C.family C.firstActualLayerOrder := by
  rw [C.relativeFirstActualDeformation_specialFiber]
  exact (C.firstActualLayer_hessian).symm

/-- **Concrete preclosing Hessian frontier.**

If the first actual source deformation occurs before determinant closure,
then:

* every positive Hessian layer below it is zero;
* its Hessian is the Hessian of the honest relative quotient special fibre;
* the retained rank-one Schur clock is tangential at exactly that order.

This is the coefficient-level input needed by the next mixed/affine
linearisation step. -/
theorem relativeFirstActualDeformation_preclosing_hessianFrontier
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre :
      C.firstActualLayerOrder < B.aligned.endpoint.defect) :
    (∀ n : ℕ,
        0 < n →
        n < C.firstActualLayerOrder →
        familyParameterHessianLayer C.family n = 0) ∧
      HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber
            C.relativeFirstActualDeformationFamily) =
        familyParameterHessianLayer C.family C.firstActualLayerOrder ∧
      C.IsClosingClockSchurTangentialOrder
        C.firstActualLayerOrder := by
  refine ⟨?_, C.relativeFirstActualDeformation_specialFiber_hessian,
    C.firstActualLayer_schurTangential_of_lt_defect hpre⟩
  intro n hnpos hnlt
  exact C.hessianLayer_eq_zero_of_pos_lt_firstActual hnpos hnlt

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
