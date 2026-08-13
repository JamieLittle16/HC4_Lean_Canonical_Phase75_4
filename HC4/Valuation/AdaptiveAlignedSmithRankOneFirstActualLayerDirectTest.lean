import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerKernelClock
import Mathlib.Tactic

/-!
# Source test for equality of the first actual layer and the closing clock

The causality theorem gives `j <= Delta`.  It is tempting to try to improve
this immediately to `j < Delta`, but the exact Schur algebra does not by
itself justify that step.  This file records the strongest source-level
consequence of the remaining equality case.

If `j = Delta`, then the first actual source layer must already change the
source-origin Hessian.  Equivalently, that first layer contains a genuine
quadratic source coefficient.  The proof uses only the exact pure Hessian
clock and the already-green gap theorem: if the order-`j` origin Hessian
layer also vanished, every origin-Hessian entry would have no positive
parameter coefficient below `j+1`, so its determinant could not have the
required nonzero `X^j` coefficient.

Thus the timing frontier sharpens to

* `j < Delta`, Schur-tangential; or
* `j = Delta`, and an actual quadratic source monomial occurs already in
  the first positive source layer.

This does not assume JC2 and, importantly, does not assert the desired strict
inequality before the collision/support geometry has actually ruled out the
quadratic equality case.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {R : Type*} [CommRing R]

/-- Extending a coefficient gap by one step only requires vanishing at the
old endpoint. -/
theorem HasNoPositiveParameterCoeffBelow.succ_of_coeff_eq_zero
    {j : ℕ}
    {p : Polynomial R}
    (hgap : HasNoPositiveParameterCoeffBelow j p)
    (hj : p.coeff j = 0) :
    HasNoPositiveParameterCoeffBelow (j + 1) p := by
  intro n hnpos hnlt
  by_cases hn : n < j
  · exact hgap n hnpos hn
  · have hnj : n = j := by omega
    simpa [hnj] using hj

/-- A matrix whose entries all have the same parameter gap has determinant
in the same gap subring. -/
theorem matrix_det_hasNoPositiveParameterCoeffBelow
    {j : ℕ}
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (hM : ∀ i k, HasNoPositiveParameterCoeffBelow j (M i k)) :
    HasNoPositiveParameterCoeffBelow j M.det := by
  let S : Subring (Polynomial R) := parameterGapSubring (R := R) j
  let H : Matrix (Fin 4) (Fin 4) S :=
    fun i k => ⟨M i k, hM i k⟩
  have hmatrix : (S.subtype).mapMatrix H = M := by
    ext i k
    rfl
  have hmap := (S.subtype).map_det H
  have hdet : M.det = S.subtype H.det := by
    rw [← hmatrix]
    exact hmap.symm
  rw [hdet]
  exact H.det.property

variable {K : Type u} [Field K] [CharZero K]

/-- Taking an exact parameter coefficient commutes with taking the
source-origin Hessian entry. -/
theorem quadraticFamilyHessianMatrix_coeff_familyParameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (i k : Fin 4) :
    (quadraticFamilyHessianMatrix P i k).coeff n =
      quadraticFamilyHessianMatrix (familyParameterLayer P n) i k := by
  change
    (MvPolynomial.constantCoeff
      (HC4.Polynomial.hessian P i k)).coeff n =
      MvPolynomial.constantCoeff
        (HC4.Polynomial.hessian (familyParameterLayer P n) i k)
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.constantCoeff_eq]
  rw [← familyParameterLayer_coeff]
  exact congrArg (fun Q => MvPolynomial.coeff 0 Q)
    (familyParameterLayer_hessian_apply P n i k)

/-- Explicit source coefficient underlying an origin-Hessian entry. -/
theorem quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient
    (Q : MvPolynomial (Fin 4) K)
    (i k : Fin 4) :
    quadraticFamilyHessianMatrix Q i k =
      MvPolynomial.coeff
          (Finsupp.single k 1 + Finsupp.single i 1) Q *
        (((Finsupp.single k 1) i + 1 : ℕ) : K) := by
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv k (MvPolynomial.pderiv i Q)) = _
  rw [MvPolynomial.constantCoeff_eq]
  rw [coeff_pderiv_commRing, coeff_pderiv_commRing]
  simp [add_comm, add_left_comm, add_assoc]

/-- **Equality with the pure Hessian clock forces quadratic curvature in the
first actual layer.** -/
theorem firstPositiveActualParameterLayer_originHessian_ne_zero_of_eq_hessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (heq : firstPositiveActualParameterOrder P h = Delta) :
    quadraticFamilyHessianMatrix
        (familyParameterLayer P (firstPositiveActualParameterOrder P h)) ≠ 0 := by
  let j := firstPositiveActualParameterOrder P h
  have hjpos : 0 < j := by
    simpa [j] using firstPositiveActualParameterOrder_pos P h
  intro hzero

  have hcoeffj :
      ∀ i k,
        (quadraticFamilyHessianMatrix P i k).coeff j = 0 := by
    intro i k
    rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    have hentry := congrArg (fun M => M i k) hzero
    simpa [j] using hentry

  have hentryGap :
      ∀ i k,
        HasNoPositiveParameterCoeffBelow (j + 1)
          (quadraticFamilyHessianMatrix P i k) := by
    intro i k
    apply HasNoPositiveParameterCoeffBelow.succ_of_coeff_eq_zero
    · simpa [j] using
        quadraticFamilyHessianMatrix_entry_hasGapBefore_firstPositiveActualOrder
          P h i k
    · exact hcoeffj i k

  have hdetGap :
      HasNoPositiveParameterCoeffBelow (j + 1)
        (quadraticFamilyHessianMatrix P).det :=
    matrix_det_hasNoPositiveParameterCoeffBelow
      (quadraticFamilyHessianMatrix P) hentryGap

  have hdet :
      (quadraticFamilyHessianMatrix P).det =
        (Polynomial.X : Polynomial K) ^ Delta := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [hdef]
    simp

  have hzeroj :
      ((quadraticFamilyHessianMatrix P).det).coeff j = 0 :=
    hdetGap j hjpos (Nat.lt_succ_self j)
  have hzeroDelta :
      ((quadraticFamilyHessianMatrix P).det).coeff Delta = 0 := by
    simpa [j, heq] using hzeroj
  rw [hdet] at hzeroDelta
  have hne :
      ((Polynomial.X : Polynomial K) ^ Delta).coeff Delta ≠ 0 := by
    rw [Polynomial.coeff_X_pow]
    simp
  exact hne hzeroDelta

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable [CharZero K]
variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- In the direct-closing timing case the first actual source potential has a
nonzero source-origin Hessian. -/
theorem firstActualLayer_originHessian_ne_zero_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    quadraticFamilyHessianMatrix
        (familyParameterLayer C.family C.firstActualLayerOrder) ≠ 0 := by
  simpa [firstActualLayerOrder] using
    firstPositiveActualParameterLayer_originHessian_ne_zero_of_eq_hessianDefect
      C.family C.hasPositiveActualParameterLayer C.family_hessianDefect heq

/-- Therefore direct closing is already visible in an honest quadratic source
coefficient of the first actual layer. -/
theorem firstActualLayer_hasQuadraticSourceCoefficient_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    ∃ i k : Fin 4,
      (MvPolynomial.coeff
          (Finsupp.single k 1 + Finsupp.single i 1) C.family).coeff
        C.firstActualLayerOrder ≠ 0 := by
  have hH := C.firstActualLayer_originHessian_ne_zero_of_eq_defect heq
  by_contra hnot
  push_neg at hnot
  apply hH
  apply Matrix.ext
  intro i k
  have hqcoeff :
      MvPolynomial.coeff
          (Finsupp.single k 1 + Finsupp.single i 1)
          (familyParameterLayer C.family C.firstActualLayerOrder) = 0 := by
    rw [familyParameterLayer_coeff]
    exact hnot i k
  rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
  rw [hqcoeff]
  simp

/-- If direct closing occurs, the support split becomes especially concrete:
either there is genuinely fresh first-layer support, or the entire first
layer overlaps the old special fibre and one of those old quadratic monomials
changes coefficient at the closing order. -/
theorem firstActualLayer_directClosing_fresh_or_overlapQuadratic
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.FirstActualLayerHasFreshSupport ∨
      (C.FirstActualLayerSupportContainedInSpecialFiber ∧
        ∃ i k : Fin 4,
          (MvPolynomial.coeff
              (Finsupp.single k 1 + Finsupp.single i 1) C.family).coeff
                C.firstActualLayerOrder ≠ 0 ∧
            (Finsupp.single k 1 + Finsupp.single i 1) ∈
              (polynomialFamilySpecialFiber C.family).support) := by
  rcases C.firstActualLayer_fresh_or_overlap with hfresh | hoverlap
  · exact Or.inl hfresh
  · right
    refine ⟨hoverlap, ?_⟩
    rcases C.firstActualLayer_hasQuadraticSourceCoefficient_of_eq_defect heq with
      ⟨i, k, hcoeff⟩
    have hmemLayer :
        (Finsupp.single k 1 + Finsupp.single i 1) ∈
          (familyParameterLayer C.family C.firstActualLayerOrder).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [familyParameterLayer_coeff]
      exact hcoeff
    exact ⟨i, k, hcoeff, hoverlap hmemLayer⟩

/-- **Honest timing test.**  The mathematics currently gives exactly this
split: either the first actual layer is strictly preclosing and Schur
-tangential, or equality occurs and the very first source deformation
already contains a genuine quadratic coefficient. -/
theorem firstActualLayer_preclosing_or_directQuadratic
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      ∃ i k : Fin 4,
        (MvPolynomial.coeff
            (Finsupp.single k 1 + Finsupp.single i 1) C.family).coeff
          C.firstActualLayerOrder ≠ 0) := by
  rcases C.firstActualLayer_preclosingTangential_or_directClosing with
    hpre | hclose
  · exact Or.inl hpre
  · exact Or.inr
      ⟨hclose.1,
        C.firstActualLayer_hasQuadraticSourceCoefficient_of_eq_defect hclose.1⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
