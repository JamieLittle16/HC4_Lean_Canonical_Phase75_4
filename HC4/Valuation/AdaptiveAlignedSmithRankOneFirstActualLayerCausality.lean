import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerTangency
import HC4.Valuation.QuadraticFamilyCollision
import HC4.Valuation.SmithFrontierFourBlockExtraction
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# Causality of the first actual source layer

Let `j > 0` be the least positive parameter exponent which occurs in a
polynomial family

    P : MvPolynomial (Fin 4) (Polynomial K).

No coefficient polynomial of `P` has a positive parameter coefficient below
`j`.  This gap is stable under source differentiation and under determinants.

The clean way to formalise the latter statement is to package the
univariate polynomials with no positive coefficients below `j` as a subring.
The source-origin Hessian matrix has all entries in that subring, hence so
does its determinant.  But the source-origin Hessian determinant is exactly
the source-constant coefficient of the full Hessian determinant.

Therefore, if

    det Hess(P) = X^Delta

with `Delta > 0`, then necessarily

    j <= Delta.

Applied to a chart-aware rank-one closing this eliminates the
`sourceLayerAfterClosing` branch of the timing trichotomy.  The first actual
source deformation is now either Schur-tangential strictly before closure or
occurs exactly at the direct closing order.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

/-! ## A coefficient-gap subring -/

variable {R : Type*} [CommRing R]

/-- `p` has no strictly positive parameter coefficient below `j`.  The
constant coefficient is intentionally unrestricted. -/
def HasNoPositiveParameterCoeffBelow
    (j : ℕ)
    (p : Polynomial R) : Prop :=
  ∀ n : ℕ, 0 < n → n < j → p.coeff n = 0

theorem HasNoPositiveParameterCoeffBelow.zero
    (j : ℕ) :
    HasNoPositiveParameterCoeffBelow j (0 : Polynomial R) := by
  intro n hnpos hnlt
  simp

theorem HasNoPositiveParameterCoeffBelow.one
    (j : ℕ) :
    HasNoPositiveParameterCoeffBelow j (1 : Polynomial R) := by
  intro n hnpos hnlt
  simp [Polynomial.coeff_one, Nat.ne_of_gt hnpos]

theorem HasNoPositiveParameterCoeffBelow.C
    (j : ℕ)
    (a : R) :
    HasNoPositiveParameterCoeffBelow j (Polynomial.C a) := by
  intro n hnpos hnlt
  rw [Polynomial.coeff_C]
  simp [Nat.ne_of_gt hnpos]

theorem HasNoPositiveParameterCoeffBelow.add
    {j : ℕ}
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    HasNoPositiveParameterCoeffBelow j (p + q) := by
  intro n hnpos hnlt
  rw [Polynomial.coeff_add, hp n hnpos hnlt, hq n hnpos hnlt]
  simp

theorem HasNoPositiveParameterCoeffBelow.neg
    {j : ℕ}
    {p : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p) :
    HasNoPositiveParameterCoeffBelow j (-p) := by
  intro n hnpos hnlt
  rw [Polynomial.coeff_neg, hp n hnpos hnlt]
  simp

theorem HasNoPositiveParameterCoeffBelow.sub
    {j : ℕ}
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    HasNoPositiveParameterCoeffBelow j (p - q) := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

/-- The gap is multiplicatively stable.  A positive exponent `n < j` in a
convolution `a+b=n` has at least one positive summand, and both summands are
still below `j`. -/
theorem HasNoPositiveParameterCoeffBelow.mul
    {j : ℕ}
    {p q : Polynomial R}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    HasNoPositiveParameterCoeffBelow j (p * q) := by
  intro n hnpos hnlt
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = n :=
    Finset.mem_antidiagonal.mp hx
  have hx1lt : x.1 < j := by omega
  have hx2lt : x.2 < j := by omega
  by_cases hx1zero : x.1 = 0
  · have hx2pos : 0 < x.2 := by omega
    rw [hq x.2 hx2pos hx2lt]
    simp
  · have hx1pos : 0 < x.1 :=
      Nat.pos_of_ne_zero hx1zero
    rw [hp x.1 hx1pos hx1lt]
    simp

/-- Polynomials with a parameter gap below `j` form a subring. -/
def parameterGapSubring
    (j : ℕ) :
    Subring (Polynomial R) where
  carrier := {p | HasNoPositiveParameterCoeffBelow j p}
  zero_mem' := HasNoPositiveParameterCoeffBelow.zero j
  one_mem' := HasNoPositiveParameterCoeffBelow.one j
  add_mem' := fun hp hq =>
    HasNoPositiveParameterCoeffBelow.add hp hq
  mul_mem' := fun hp hq =>
    HasNoPositiveParameterCoeffBelow.mul hp hq
  neg_mem' := fun hp =>
    HasNoPositiveParameterCoeffBelow.neg hp

/-! ## Minimal actual layer gives coefficientwise gap -/

variable {K : Type*} [Field K]

/-- Every source coefficient polynomial has the gap determined by the least
positive actual family layer. -/
theorem sourceCoefficient_hasGapBefore_firstPositiveActualOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (d : Fin 4 →₀ ℕ) :
    HasNoPositiveParameterCoeffBelow
      (firstPositiveActualParameterOrder P h)
      (MvPolynomial.coeff d P) := by
  intro n hnpos hnlt
  by_contra hcoeff
  have hd : d ∈ P.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  have hnmem :
      n ∈ familyParameterLayerOrders P := by
    exact
      (mem_familyParameterLayerOrders_iff P n).2
        ⟨d, hd, hcoeff⟩
  have hle :
      firstPositiveActualParameterOrder P h ≤ n :=
    firstPositiveActualParameterOrder_le
      P h hnmem hnpos
  omega

/-- Natural scalar polynomials have every positive parameter coefficient
zero. -/
theorem natCast_hasNoPositiveParameterCoeffBelow
    (j m : ℕ) :
    HasNoPositiveParameterCoeffBelow
      j (m : Polynomial K) := by
  simpa using
    (HasNoPositiveParameterCoeffBelow.C
      (R := K) j (m : K))

/-! ## The source-origin Hessian lies in the gap subring -/

/-- Every source-origin Hessian entry has the same parameter gap as the
family.  The entry is a source coefficient of `P` multiplied by the usual
integer derivative factor. -/
theorem quadraticFamilyHessianMatrix_entry_hasGapBefore_firstPositiveActualOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (i k : Fin 4) :
    HasNoPositiveParameterCoeffBelow
      (firstPositiveActualParameterOrder P h)
      (quadraticFamilyHessianMatrix P i k) := by
  let j := firstPositiveActualParameterOrder P h
  have hentry :
      quadraticFamilyHessianMatrix P i k =
        MvPolynomial.coeff
            (Finsupp.single k 1 + Finsupp.single i 1) P *
          (((Finsupp.single k 1) i + 1 : ℕ) :
            Polynomial K) := by
    change
      MvPolynomial.constantCoeff
          (MvPolynomial.pderiv k (MvPolynomial.pderiv i P)) = _
    rw [MvPolynomial.constantCoeff_eq]
    rw [coeff_pderiv_commRing, coeff_pderiv_commRing]
    simp [add_comm, add_left_comm, add_assoc]
  rw [hentry]
  apply HasNoPositiveParameterCoeffBelow.mul
  · exact
      sourceCoefficient_hasGapBefore_firstPositiveActualOrder
        P h _
  · exact
      natCast_hasNoPositiveParameterCoeffBelow
        (K := K) j _

/-- Therefore the determinant of the source-origin Hessian has the same
parameter gap.  We obtain this without expanding the determinant: lift the
matrix to the gap subring and use `RingHom.map_det`. -/
theorem quadraticFamilyHessianMatrix_det_hasGapBefore_firstPositiveActualOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    HasNoPositiveParameterCoeffBelow
      (firstPositiveActualParameterOrder P h)
      (quadraticFamilyHessianMatrix P).det := by
  let j := firstPositiveActualParameterOrder P h
  let S : Subring (Polynomial K) :=
    parameterGapSubring (R := K) j
  let H :
      Matrix (Fin 4) (Fin 4) S :=
    fun i k =>
      ⟨quadraticFamilyHessianMatrix P i k,
        quadraticFamilyHessianMatrix_entry_hasGapBefore_firstPositiveActualOrder
          P h i k⟩
  have hmatrix :
      (S.subtype).mapMatrix H =
        quadraticFamilyHessianMatrix P := by
    ext i k
    rfl
  have hmap :=
    (S.subtype).map_det H
  have hdet :
      (quadraticFamilyHessianMatrix P).det =
        S.subtype H.det := by
    rw [← hmatrix]
    exact hmap.symm
  rw [hdet]
  exact H.det.property

/-! ## General causality theorem -/

/-- **First actual layer cannot occur after pure Hessian closure.**

If the pure Hessian determinant is `X^Delta` with `Delta > 0`, the least
positive actual source layer occurs no later than `Delta`. -/
theorem firstPositiveActualParameterOrder_le_hessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hDelta : 0 < Delta) :
    firstPositiveActualParameterOrder P h ≤ Delta := by
  let j := firstPositiveActualParameterOrder P h
  have hgap :
      HasNoPositiveParameterCoeffBelow
        j (quadraticFamilyHessianMatrix P).det := by
    simpa [j] using
      quadraticFamilyHessianMatrix_det_hasGapBefore_firstPositiveActualOrder
        P h
  have hdet :
      (quadraticFamilyHessianMatrix P).det =
        (Polynomial.X : Polynomial K) ^ Delta := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [hdef]
    simp
  by_contra hnot
  have hlt : Delta < j :=
    Nat.lt_of_not_ge hnot
  have hzero :
      ((quadraticFamilyHessianMatrix P).det).coeff Delta = 0 :=
    hgap Delta hDelta hlt
  rw [hdet] at hzero
  have hne :
      ((Polynomial.X : Polynomial K) ^ Delta).coeff Delta ≠ 0 := by
    rw [Polynomial.coeff_X_pow]
    simp
  exact hne hzero

/-! ## Rank-one closing consequence -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable [CharZero K]
variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The least positive actual source deformation of a rank-one closing
cannot occur after the determinant-closing order. -/
theorem firstActualLayerOrder_le_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.firstActualLayerOrder ≤
      B.aligned.endpoint.defect := by
  simpa [firstActualLayerOrder] using
    firstPositiveActualParameterOrder_le_hessianDefect
      C.family
      C.hasPositiveActualParameterLayer
      C.family_hessianDefect
      C.defect_pos

/-- The `sourceLayerAfterClosing` timing branch is impossible. -/
theorem not_sourceLayerAfterClosing
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    ¬ B.aligned.endpoint.defect <
        C.firstActualLayerOrder := by
  exact Nat.not_lt_of_ge C.firstActualLayerOrder_le_defect

/-- **Two-way first actual layer timing.**

After causality there are only the two meaningful cases:

* a genuine preclosing source deformation, necessarily Schur-tangential;
* the first actual source deformation occurs exactly at determinant closure
  and is genuinely transverse. -/
theorem firstActualLayer_preclosingTangential_or_directClosing
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder <
        B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder
        C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder =
        B.aligned.endpoint.defect ∧
      (C.chartData.clock.series.offDiag.coeff
            C.firstActualLayerOrder ≠ 0 ∨
       C.chartData.clock.series.kernel.coeff
            C.firstActualLayerOrder ≠ 0)) := by
  rcases C.firstActualLayer_timing_trichotomy with
    hpre | hclose | hpost
  · exact Or.inl hpre
  · exact Or.inr hclose
  · exact False.elim
      (C.not_sourceLayerAfterClosing hpost)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
