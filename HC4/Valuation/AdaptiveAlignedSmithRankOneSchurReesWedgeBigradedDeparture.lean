import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurRawWedgeReesDeparture
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyMaximalHomogeneousKernel
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLongitudinalCancellationInterface
import Mathlib.Tactic

/-!
# Stage 4B37: exact bigraded normalisation of the first Rees projective departure

B36 selects the first nonzero auxiliary-Rees coefficient of a genuine source
projective wedge.  Before the corrected-RS2 calculation one further grading
must be kept honest: the first spatial key is homogeneous in transverse degree,
whereas its `x₀^e L^m` normal form is obtained only after taking a maximal
ordinary-homogeneous component.

The key simplification is that the B34 Rees projective wedge itself has an
*exact factorisation*.  If `R` denotes transverse Rees substitution and
`s_j` the complementary kernel shift, then

    W^R_j = tau^(s_j) R(W_j)

and the source chain rule gives

    wedge(W^R_i,W^R_j; k)
      = tau^(s_i+s_j+d_k) R(wedge(W_i,W_j; k)),

where `d_k` is `0` in the longitudinal variable and `1` in a transverse
variable.  Thus B36's first Rees wedge layer is not an opaque convolution: it
is literally one transverse weighted initial form of the original source
wedge, up to the explicit common shift.

We then take the already-existing B9 maximal ordinary slice of that nonzero
weighted initial form.  The output is therefore a genuine *bigraded* first
projective departure: exact transverse degree first, maximal ordinary degree
second.  No identification of the two gradings is made.

This is the normalisation consumed by the final corrected-RS2 coefficient
calculation.  It introduces no repair assertion and no new projective choice.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Parameter shift contributed by one source derivative under simultaneous
transverse Rees inflation. -/
def transverseReesDerivativeParameterShift (k : Fin 4) : ℕ :=
  if k = 0 then 0 else 1

@[simp] theorem transverseReesDerivativeParameterShift_zero :
    transverseReesDerivativeParameterShift (0 : Fin 4) = 0 := by
  simp [transverseReesDerivativeParameterShift]

@[simp] theorem transverseReesDerivativeParameterShift_succ (k : Fin 3) :
    transverseReesDerivativeParameterShift k.succ = 1 := by
  simp [transverseReesDerivativeParameterShift]

/-- The B34 derivative coefficient is exactly the corresponding parameter
monomial. -/
theorem transverseReesDerivativeCoefficient_eq_X_pow_shift
    (k : Fin 4) :
    transverseReesDerivativeCoefficient (K := K) k =
      Polynomial.X ^ transverseReesDerivativeParameterShift k := by
  fin_cases k <;>
    simp [transverseReesDerivativeCoefficient,
      transverseReesDerivativeParameterShift]

/-- First-order chain rule for the simultaneous three-variable transverse
Rees substitution. -/
theorem pderiv_transverseSourceReesFamily
    (F : MvPolynomial (Fin 4) K)
    (k : Fin 4) :
    MvPolynomial.pderiv k (transverseSourceReesFamily F) =
      MvPolynomial.C (transverseReesDerivativeCoefficient (K := K) k) *
        transverseSourceReesFamily (MvPolynomial.pderiv k F) := by
  unfold transverseSourceReesFamily unitTransverseInflateFamily
  rw [pderiv_kernelInflateHom]
  rw [pderiv_kernelInflateHom]
  rw [pderiv_kernelInflateHom]
  simp only [MvPolynomial.pderiv_map, map_mul, kernelInflateHom_C]
  fin_cases k <;>
    simp [transverseReesDerivativeCoefficient,
      kernelInflateDerivativeCoefficient] <;> ring

/-- Rees transport is additive. -/
theorem transverseSourceReesFamily_sub
    (P Q : MvPolynomial (Fin 4) K) :
    transverseSourceReesFamily (P - Q) =
      transverseSourceReesFamily P - transverseSourceReesFamily Q := by
  simp [transverseSourceReesFamily, unitTransverseInflateFamily, map_sub]

/-- Common parameter shift of one rescaled Rees projective wedge. -/
def transverseReesProjectiveWedgeShift
    (i j k : Fin 4) : ℕ :=
  transverseReesKernelParameterShift i +
    transverseReesKernelParameterShift j +
      transverseReesDerivativeParameterShift k

/-- The three scalar chain-rule factors in a Rees projective wedge collapse
to one explicit parameter monomial. -/
theorem transverseReesProjectiveWedgeCoefficient_eq_X_pow_shift
    (i j k : Fin 4) :
    transverseReesKernelScale (K := K) i *
        transverseReesKernelScale (K := K) j *
          transverseReesDerivativeCoefficient (K := K) k =
      Polynomial.X ^ transverseReesProjectiveWedgeShift i j k := by
  rw [transverseReesKernelScale_eq_X_pow_shift]
  rw [transverseReesKernelScale_eq_X_pow_shift]
  rw [transverseReesDerivativeCoefficient_eq_X_pow_shift]
  simp [transverseReesProjectiveWedgeShift, pow_add]

/-- **Exact projective-wedge covariance of the B34 Rees kernel.**

There is no hidden convolution in the projective expression: after the
explicit common parameter shift it is exactly the transverse Rees transform
of the original source-coordinate projective wedge. -/
theorem reesVectorProjectiveWedge_transverseSourceReesKernel
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) :
    reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k =
      MvPolynomial.C
          (Polynomial.X ^ transverseReesProjectiveWedgeShift i j k) *
        transverseSourceReesFamily
          (sourceVectorProjectiveWedge W i j k) := by
  unfold reesVectorProjectiveWedge sourceVectorProjectiveWedge
  unfold transverseSourceReesKernel
  simp only [MvPolynomial.pderiv_C_mul]
  rw [pderiv_transverseSourceReesFamily]
  rw [pderiv_transverseSourceReesFamily]
  rw [transverseSourceReesFamily_sub]
  rw [transverseSourceReesFamily_mul]
  rw [transverseSourceReesFamily_mul]
  rw [← transverseReesProjectiveWedgeCoefficient_eq_X_pow_shift
      (K := K) i j k]
  simp only [MvPolynomial.C_mul]
  ring

/-! ## Exact layers after an external parameter monomial -/

/-- Scalar coefficient formula after multiplying a transverse Rees family by
an external parameter monomial. -/
theorem coeff_coeff_C_X_pow_mul_transverseSourceReesFamily
    (P : MvPolynomial (Fin 4) K)
    (s n : ℕ)
    (d : Fin 4 →₀ ℕ) :
    (MvPolynomial.coeff d
        (MvPolynomial.C (Polynomial.X ^ s) *
          transverseSourceReesFamily P)).coeff n =
      if s + pureLongitudinalTransverseDegree d = n then
        MvPolynomial.coeff d P
      else 0 := by
  rw [MvPolynomial.coeff_C_mul]
  rw [coeff_transverseSourceReesFamily]
  rw [← mul_assoc, ← pow_add]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hdn : s + pureLongitudinalTransverseDegree d = n
  · subst n
    simp
  · have hlt_or_gt :
        n < s + pureLongitudinalTransverseDegree d ∨
          s + pureLongitudinalTransverseDegree d < n := by
      omega
    rcases hlt_or_gt with hlt | hgt
    · simp [Nat.not_le.mpr hlt, hdn]
    · have hle : s + pureLongitudinalTransverseDegree d ≤ n :=
        Nat.le_of_lt hgt
      have hsubpos :
          0 < n - (s + pureLongitudinalTransverseDegree d) := by
        omega
      simp [hle, hdn, Polynomial.coeff_C, Nat.ne_of_gt hsubpos]

/-- Parameter layer after an external monomial shift.  Once the shift has
been crossed, the coefficient is exactly the corresponding old transverse
weighted initial form. -/
theorem familyParameterLayer_C_X_pow_mul_transverseSourceReesFamily
    (P : MvPolynomial (Fin 4) K)
    (s n : ℕ) :
    familyParameterLayer
        (MvPolynomial.C (Polynomial.X ^ s) *
          transverseSourceReesFamily P) n =
      if s ≤ n then
        initialForm pureLongitudinalTransverseWeight
          (-((n - s : ℕ) : ℤ)) P
      else 0 := by
  ext d
  rw [familyParameterLayer_coeff]
  rw [coeff_coeff_C_X_pow_mul_transverseSourceReesFamily]
  by_cases hsn : s ≤ n
  · rw [if_pos hsn]
    rw [coeff_initialForm]
    rw [weight_pureLongitudinalTransverseWeight]
    by_cases hdeg : pureLongitudinalTransverseDegree d = n - s
    · have hsum : s + pureLongitudinalTransverseDegree d = n := by
        omega
      rw [if_pos hsum]
      have hw :
          -(pureLongitudinalTransverseDegree d : ℤ) =
            -((n - s : ℕ) : ℤ) := by
        exact congrArg (fun q : ℕ => -(q : ℤ)) hdeg
      simp [hw]
    · have hsum : s + pureLongitudinalTransverseDegree d ≠ n := by
        intro h
        apply hdeg
        omega
      rw [if_neg hsum]
      have hw :
          -(pureLongitudinalTransverseDegree d : ℤ) ≠
            -((n - s : ℕ) : ℤ) := by
        intro h
        apply hdeg
        exact_mod_cast (neg_inj.mp h)
      simp [hw]
  · rw [if_neg hsn]
    have hsum : s + pureLongitudinalTransverseDegree d ≠ n := by
      intro h
      apply hsn
      omega
    rw [if_neg hsum]
    simp

/-! ## B36 becomes an exact weighted source-wedge initial form -/

namespace FirstReesProjectiveWedgeDepartureData

/-- Transverse degree of the actual source-wedge component represented by a
B36 Rees departure, after removing the explicit kernel/derivative shift. -/
noncomputable def sourceTransverseOrder
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) : ℕ :=
  D.order - transverseReesProjectiveWedgeShift i j k

/-- The explicit Rees shift cannot lie above B36's selected nonzero layer. -/
theorem wedgeShift_le_order
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) :
    transverseReesProjectiveWedgeShift i j k ≤ D.order := by
  by_contra hnot
  have hlt : D.order < transverseReesProjectiveWedgeShift i j k :=
    Nat.lt_of_not_ge hnot
  have hzero :
      familyParameterLayer
        (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k)
        D.order = 0 := by
    rw [reesVectorProjectiveWedge_transverseSourceReesKernel]
    rw [familyParameterLayer_C_X_pow_mul_transverseSourceReesFamily]
    simp [Nat.not_le.mpr hlt]
  exact D.layer_ne_zero hzero

/-- The B36 selected layer is exactly a transverse weighted initial form of
the honest source-coordinate projective wedge. -/
theorem layer_eq_sourceWedgeInitialForm
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) :
    familyParameterLayer
        (reesVectorProjectiveWedge (transverseSourceReesKernel W) i j k)
        D.order =
      initialForm pureLongitudinalTransverseWeight
        (-((D.sourceTransverseOrder : ℕ) : ℤ))
        (sourceVectorProjectiveWedge W i j k) := by
  rw [reesVectorProjectiveWedge_transverseSourceReesKernel]
  rw [familyParameterLayer_C_X_pow_mul_transverseSourceReesFamily]
  rw [if_pos D.wedgeShift_le_order]
  rfl

/-- Hence the selected source-wedge weighted initial form is nonzero. -/
theorem sourceWedgeInitialForm_ne_zero
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) :
    initialForm pureLongitudinalTransverseWeight
        (-((D.sourceTransverseOrder : ℕ) : ℤ))
        (sourceVectorProjectiveWedge W i j k) ≠ 0 := by
  rw [← D.layer_eq_sourceWedgeInitialForm]
  exact D.layer_ne_zero

/-- The source-wedge component selected by B36 is genuinely homogeneous in
one exact transverse degree. -/
theorem sourceWedgeInitialForm_isWeightedHomogeneous
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) :
    MvPolynomial.IsWeightedHomogeneous pureLongitudinalTransverseWeight
      (initialForm pureLongitudinalTransverseWeight
        (-((D.sourceTransverseOrder : ℕ) : ℤ))
        (sourceVectorProjectiveWedge W i j k))
      (-((D.sourceTransverseOrder : ℕ) : ℤ)) := by
  exact initialForm_isWeightedHomogeneous _ _ _

end FirstReesProjectiveWedgeDepartureData

/-- B36 followed by the lossless B9 maximal ordinary slice of its exact
transverse source-wedge component. -/
structure FirstBigradedProjectiveWedgeDepartureData
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (i j k : Fin 4) where
  rees : FirstReesProjectiveWedgeDepartureData W i j k
  ordinarySlice :
    FirstTransverseKeyMaximalHomogeneousSliceData
      (initialForm pureLongitudinalTransverseWeight
        (-((rees.sourceTransverseOrder : ℕ) : ℤ))
        (sourceVectorProjectiveWedge W i j k))
      rees.sourceTransverseOrder

/-- Every B36 first Rees projective departure has a nonzero maximal ordinary
homogeneous slice; no extra hypothesis is required. -/
theorem FirstReesProjectiveWedgeDepartureData.exists_bigradedDepartureData
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstReesProjectiveWedgeDepartureData W i j k) :
    Nonempty (FirstBigradedProjectiveWedgeDepartureData W i j k) := by
  rcases exists_firstTransverseKeyMaximalHomogeneousSlice
      (initialForm pureLongitudinalTransverseWeight
        (-((D.sourceTransverseOrder : ℕ) : ℤ))
        (sourceVectorProjectiveWedge W i j k))
      D.sourceTransverseOrder
      D.sourceWedgeInitialForm_ne_zero
      D.sourceWedgeInitialForm_isWeightedHomogeneous with
    ⟨S⟩
  exact ⟨{ rees := D, ordinarySlice := S }⟩

namespace FirstBigradedProjectiveWedgeDepartureData

/-- The final bigraded projective-departure slice has the standard exact
longitudinal monomial factor used throughout B4/B9. -/
theorem slice_finSuccEquiv_eq_longitudinalMonomial
    {W : Fin 4 → MvPolynomial (Fin 4) K}
    {i j k : Fin 4}
    (D : FirstBigradedProjectiveWedgeDepartureData W i j k) :
    MvPolynomial.finSuccEquiv K 3 D.ordinarySlice.sliceData.slice =
      Polynomial.monomial
        (D.ordinarySlice.sliceData.ordinaryDegree -
          D.rees.sourceTransverseOrder)
        ((MvPolynomial.finSuccEquiv K 3
          D.ordinarySlice.sliceData.slice).coeff
            (D.ordinarySlice.sliceData.ordinaryDegree -
              D.rees.sourceTransverseOrder)) := by
  exact D.ordinarySlice.sliceData.finSuccEquiv_eq_longitudinalMonomial

end FirstBigradedProjectiveWedgeDepartureData

/-! ## Carrier-facing provenance -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The moving raw Schur branch with both gradings made explicit and attached
to the same B30 first-key packet. -/
structure RawWedgeBigradedDepartureProvenanceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4) where
  reesProvenance : C.RawWedgeFirstReesDepartureProvenanceData k
  bigraded :
    FirstBigradedProjectiveWedgeDepartureData
      reesProvenance.assembly.leading.sourceKernel.vector
      reesProvenance.i reesProvenance.j k

/-- Promote the B36 moving-raw-line packet to the exact bigraded packet needed
by the corrected-RS2 coefficient calculation. -/
theorem HasFirstTransverseSourceKey.exists_rawWedgeBigradedDepartureProvenanceData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey)
    (k : Fin 4)
    (hraw : C.rawSpecialSchurProjectiveWedge k ≠ 0) :
    Nonempty (C.RawWedgeBigradedDepartureProvenanceData k) := by
  rcases hkey.exists_rawWedgeFirstReesDepartureProvenanceData k hraw with
    ⟨R⟩
  rcases R.departure.exists_bigradedDepartureData with ⟨G⟩
  exact ⟨{
    reesProvenance := R
    bigraded := G
  }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
