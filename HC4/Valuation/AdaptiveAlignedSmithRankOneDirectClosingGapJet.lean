import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingOriginPencil
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# The exact dual-number jet at direct closing

At the honest first actual source order `j`, every coefficient of the
source-origin Hessian has a gap: there are no positive parameter terms
strictly below `j`.  On that gap subring the operation

    p |-> (p.coeff 0, p.coeff j)

is therefore multiplicative when the target is the dual-number ring.  The
nilpotent coordinate remembers exactly the first possible positive layer.

For the direct-closing equality `j = Delta`, applying this jet entrywise to
the honest Hessian sends its determinant to `(0, 1)`.  This is the finite
square-zero avatar of the entire remaining equality branch.  The next file
can therefore compute the nilpotent determinant coefficient purely by
finite-dimensional adjugate algebra.
-/

namespace HC4.Valuation

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- At a positive gap order, the endpoint coefficient of a product only has
its two boundary convolution contributions. -/
theorem coeff_mul_at_gap_endpoint
    {j : ℕ}
    (hj : 0 < j)
    {p q : Polynomial K}
    (hp : HasNoPositiveParameterCoeffBelow j p)
    (hq : HasNoPositiveParameterCoeffBelow j q) :
    (p * q).coeff j =
      p.coeff 0 * q.coeff j + p.coeff j * q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal j
  let f : ℕ × ℕ → K := fun x => p.coeff x.1 * q.coeff x.2
  have h0j : (0, j) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hj0 : (j, 0) ∈ s := by
    simp [s, Finset.mem_antidiagonal]
  have hne : (j, 0) ≠ (0, j) := by
    intro h
    have hfirst : j = 0 := congrArg Prod.fst h
    omega
  have hj0erase : (j, 0) ∈ s.erase (0, j) := by
    exact Finset.mem_erase.mpr ⟨hne, hj0⟩
  have hrest :
      ∀ x ∈ (s.erase (0, j)).erase (j, 0), f x = 0 := by
    intro x hx
    have hxs : x ∈ s := by
      exact (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    have hxne0j : x ≠ (0, j) := by
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hxnej0 : x ≠ (j, 0) := by
      exact (Finset.mem_erase.mp hx).1
    have hsum : x.1 + x.2 = j := by
      exact Finset.mem_antidiagonal.mp (by simpa [s] using hxs)
    have hx1pos : 0 < x.1 := by
      by_contra hnot
      have hx1zero : x.1 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx2eq : x.2 = j := by omega
      exact hxne0j (Prod.ext hx1zero hx2eq)
    have hx2pos : 0 < x.2 := by
      by_contra hnot
      have hx2zero : x.2 = 0 := Nat.eq_zero_of_not_pos hnot
      have hx1eq : x.1 = j := by omega
      exact hxnej0 (Prod.ext hx1eq hx2zero)
    have hx1lt : x.1 < j := by omega
    have hx2lt : x.2 < j := by omega
    simp [f, hp x.1 hx1pos hx1lt, hq x.2 hx2pos hx2lt]
  have hsplit0 := Finset.add_sum_erase s f h0j
  have hsplitj := Finset.add_sum_erase (s.erase (0, j)) f hj0erase
  have hz : ∑ x ∈ (s.erase (0, j)).erase (j, 0), f x = 0 := by
    exact Finset.sum_eq_zero hrest
  change (∑ x ∈ s, f x) = _
  rw [← hsplit0, ← hsplitj, hz]
  simp [f]

/-- The exact `(0,j)` jet on the coefficient-gap subring.  Multiplication is
valid precisely because all intermediate positive coefficients vanish and
the target nilpotent satisfies `eps^2 = 0`. -/
noncomputable def parameterGapJet
    (j : ℕ)
    (hj : 0 < j) :
    parameterGapSubring (R := K) j →+* DualNumber K where
  toFun p := (p.1.coeff 0, p.1.coeff j)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change (1 : Polynomial K).coeff j = 0
      rw [Polynomial.coeff_one]
      exact if_neg (Nat.ne_of_gt hj)
  map_add' p q := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp [Polynomial.coeff_mul]
    · simp only [TrivSqZeroExt.snd_mk, DualNumber.snd_mul,
        TrivSqZeroExt.fst_mk]
      change
        (p.1 * q.1).coeff j =
          p.1.coeff 0 * q.1.coeff j + p.1.coeff j * q.1.coeff 0
      rw [coeff_mul_at_gap_endpoint hj p.property q.property]

@[simp]
theorem parameterGapJet_fst
    (j : ℕ)
    (hj : 0 < j)
    (p : parameterGapSubring (R := K) j) :
    TrivSqZeroExt.fst (parameterGapJet (K := K) j hj p) = p.1.coeff 0 := by
  rfl

@[simp]
theorem parameterGapJet_snd
    (j : ℕ)
    (hj : 0 < j)
    (p : parameterGapSubring (R := K) j) :
    TrivSqZeroExt.snd (parameterGapJet (K := K) j hj p) = p.1.coeff j := by
  rfl

/-- Lift a polynomial matrix whose entries share the `j`-gap into the gap
subring. -/
noncomputable def matrixToParameterGap
    {j : ℕ}
    (M : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hM : ∀ i k, HasNoPositiveParameterCoeffBelow j (M i k)) :
    Matrix (Fin 4) (Fin 4) (parameterGapSubring (R := K) j) :=
  fun i k => ⟨M i k, hM i k⟩

@[simp]
theorem matrixToParameterGap_coe
    {j : ℕ}
    (M : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hM : ∀ i k, HasNoPositiveParameterCoeffBelow j (M i k))
    (i k : Fin 4) :
    ((matrixToParameterGap M hM i k :
      parameterGapSubring (R := K) j) : Polynomial K) = M i k := by
  rfl

/-- The entrywise dual-number jet of a gap matrix has constant part `M_0`
and nilpotent part `M_j`. -/
theorem parameterGapJet_mapMatrix_apply
    {j : ℕ}
    (hj : 0 < j)
    (M : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hM : ∀ i k, HasNoPositiveParameterCoeffBelow j (M i k))
    (i k : Fin 4) :
    (parameterGapJet (K := K) j hj).mapMatrix
        (matrixToParameterGap M hM) i k =
      ((M i k).coeff 0, (M i k).coeff j) := by
  rfl

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable [CharZero K]
variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Every entry of the honest source-origin Hessian lies in the gap subring
at the first actual source order. -/
theorem family_originHessian_entry_hasGap
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i k : Fin 4) :
    HasNoPositiveParameterCoeffBelow
      C.firstActualLayerOrder
      (quadraticFamilyHessianMatrix C.family i k) := by
  simpa [firstActualLayerOrder] using
    quadraticFamilyHessianMatrix_entry_hasGapBefore_firstPositiveActualOrder
      C.family C.hasPositiveActualParameterLayer i k

/-- The exact dual-number origin Hessian attached to the direct-closing jet. -/
noncomputable def directClosingOriginDualHessian
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  (parameterGapJet (K := K)
      C.firstActualLayerOrder C.firstActualLayerOrder_pos).mapMatrix
    (matrixToParameterGap
      (quadraticFamilyHessianMatrix C.family)
      C.family_originHessian_entry_hasGap)

/-- Entrywise, the dual Hessian is exactly `H_0 + eps H_j`. -/
theorem directClosingOriginDualHessian_apply
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (i k : Fin 4) :
    C.directClosingOriginDualHessian i k =
      (sourceOriginHessianLayer C.family 0 i k,
       sourceOriginHessianLayer C.family C.firstActualLayerOrder i k) := by
  rw [directClosingOriginDualHessian]
  rw [parameterGapJet_mapMatrix_apply]
  rw [sourceOriginHessianLayer_apply, sourceOriginHessianLayer_apply]

/-- At direct closing, the determinant of the dual Hessian is exactly the
pure nilpotent `eps`: constant determinant zero, first determinant
coefficient one. -/
theorem directClosingOriginDualHessian_det
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.directClosingOriginDualHessian.det = DualNumber.eps := by
  let j := C.firstActualLayerOrder
  let J := parameterGapJet (K := K) j (by
    simpa [j] using C.firstActualLayerOrder_pos)
  let G : Matrix (Fin 4) (Fin 4) (parameterGapSubring (R := K) j) :=
    matrixToParameterGap
      (quadraticFamilyHessianMatrix C.family)
      (by
        intro i k
        simpa [j] using C.family_originHessian_entry_hasGap i k)
  have hJG : J.mapMatrix G = C.directClosingOriginDualHessian := by
    ext i k <;>
      simp [J, G, j, directClosingOriginDualHessian, parameterGapJet,
        matrixToParameterGap]
  have hmap : J G.det = (J.mapMatrix G).det := J.map_det G
  rw [← hJG]
  rw [← hmap]
  have hdetGap :
      ((G.det : parameterGapSubring (R := K) j) : Polynomial K) =
        (quadraticFamilyHessianMatrix C.family).det := by
    have hsub :=
      (parameterGapSubring (R := K) j).subtype.map_det G
    have hmatrix :
        (parameterGapSubring (R := K) j).subtype.mapMatrix G =
          quadraticFamilyHessianMatrix C.family := by
      ext i k
      rfl
    rw [hmatrix] at hsub
    exact hsub.symm
  apply TrivSqZeroExt.ext
  · change
      ((G.det : parameterGapSubring (R := K) j) : Polynomial K).coeff 0 =
        TrivSqZeroExt.fst DualNumber.eps
    rw [hdetGap]
    rw [C.family_originHessian_det_eq_X_pow]
    have hDelta : 0 < B.aligned.endpoint.defect := C.defect_pos
    simp [Polynomial.coeff_X_pow]
    exact Ne.symm hDelta.ne'
  · change
      ((G.det : parameterGapSubring (R := K) j) : Polynomial K).coeff j =
        TrivSqZeroExt.snd DualNumber.eps
    rw [hdetGap]
    have hone := C.directClosing_family_originHessian_det_coeff_firstActual heq
    simpa [j] using hone

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
