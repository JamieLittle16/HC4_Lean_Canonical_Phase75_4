import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianFourBlock
import HC4.Newton.ZeroSchurFirstEntryClock
import Mathlib.Tactic

/-!
# Special-fibre calculus for the recentered adaptive Hessian block

`AdaptiveAlignedSmithRecenteredHessianFourBlock` put the genuine blocker
recentring and the genuine Hessian determinant clock on the same polynomial
family.  This file specialises that honest polynomial-series Hessian at the
family parameter `0`.

There are two points to the construction.

1.  The coefficient-swap homomorphism used by the family Hessian has special
    coefficient exactly equal to `polynomialFamilySpecialFiber`.  Hence the
    constant coefficient of every recentered Hessian-series entry is the
    corresponding entry of the Hessian of the recentered special fibre.

2.  Once a nonzero active `2 x 2` special-fibre Hessian minor is chosen, no
    further pivot calculation is needed.  If the constant cleared Schur block
    is nonzero, the exact determinant clock makes it determinant-zero and the
    generic domain theorem
    `leftPivot_or_rightAxisPivot_of_constantBlock` supplies the required
    rank-one pivot.  If the complete constant Schur block is zero, the same
    honest four-block is already an `ExactZeroSchurFourBlockData` object.

Thus, for positive defect, every nonzero active Hessian chart automatically
feeds one of the two Schur clocks already present in the repository.  The only
remaining finite geometric alternative is that *every coordinate-principal*
active `2 x 2` minor exposed by these simultaneous row/column permutations
vanishes.  We keep that no-active-chart branch explicit rather than silently
identifying it with a stronger matrix-rank statement.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u v

variable {K : Type u} [Field K]

/-! ## Constant coefficient of the coefficient-swap homomorphism -/

/-- Moving the family parameter to the outer polynomial ring and then taking
its constant coefficient is exactly passage to the polynomial-family special
fibre. -/
theorem polynomialFamilySeriesHom_constantCoeff
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Polynomial.constantCoeff
        (polynomialFamilySeriesHom (K := K) P) =
      polynomialFamilySpecialFiber P := by
  let f :
      MvPolynomial (Fin 4) (Polynomial K) →+*
        MvPolynomial (Fin 4) K :=
    (Polynomial.constantCoeff :
      Polynomial (MvPolynomial (Fin 4) K) →+*
        MvPolynomial (Fin 4) K).comp
      (polynomialFamilySeriesHom (K := K))
  let g :
      MvPolynomial (Fin 4) (Polynomial K) →+*
        MvPolynomial (Fin 4) K :=
    MvPolynomial.map Polynomial.constantCoeff
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, g, polynomialFamilySeriesHom]
    · intro i
      simp [f, g, polynomialFamilySeriesHom]
  change f P = g P
  exact RingHom.congr_fun hfg P

/-! ## The recentered Hessian series at parameter zero -/

/-- Constant parameter coefficient of the honest recentered Hessian series is
exactly the Hessian of the honest recentered special fibre. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_coeff_zero
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap)
    (i j : Fin 4) :
    (adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E i j).coeff 0 =
      HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber E.rightRecenteredFamily) i j := by
  unfold adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix
  change
    (polynomialFamilySeriesHom (K := K)
      (HC4.Polynomial.hessian E.rightRecenteredFamily i j)).coeff 0 = _
  change
    Polynomial.constantCoeff
      (polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian E.rightRecenteredFamily i j)) = _
  rw [polynomialFamilySeriesHom_constantCoeff]
  simp [HC4.Polynomial.hessian_apply,
    polynomialFamilySpecialFiber, MvPolynomial.pderiv_map]

/-- Rewriting the special fibre gives the exact finite polynomial Hessian
used by the blocker geometry. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_coeff_zero_recentered
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap)
    (i j : Fin 4) :
    (adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E i j).coeff 0 =
      HC4.Polynomial.hessian
        (longitudinalRightRecenterHom (K := K) E.rawSpecialFiber) i j := by
  rw [adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_coeff_zero]
  rw [E.rightRecenteredFamily_specialFiber]

/-! ## Entrywise specialisation of a four-block -/

/-- Apply the outer-parameter constant coefficient to all ten entries of a
four-block.  Unlike the older rigid-packet helper this is stated over an
arbitrary commutative coefficient ring, so here the target ring may itself be
`MvPolynomial (Fin 4) K`. -/
noncomputable def parameterConstantCoeffFourBlock
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    GeneralFourBlock R where
  a := H.a.coeff 0
  b := H.b.coeff 0
  d := H.d.coeff 0
  p := H.p.coeff 0
  q := H.q.coeff 0
  r := H.r.coeff 0
  s := H.s.coeff 0
  x := H.x.coeff 0
  y := H.y.coeff 0
  z := H.z.coeff 0

/-- Constant coefficient commutes with the active determinant. -/
theorem parameterConstantCoeffFourBlock_activeDet
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    H.activeDet.coeff 0 =
      (parameterConstantCoeffFourBlock H).activeDet := by
  simp [parameterConstantCoeffFourBlock, GeneralFourBlock.activeDet,
    Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the first cleared Schur entry. -/
theorem parameterConstantCoeffFourBlock_schurA
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    H.schurA.coeff 0 =
      (parameterConstantCoeffFourBlock H).schurA := by
  simp [parameterConstantCoeffFourBlock, GeneralFourBlock.schurA,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the off-diagonal cleared Schur entry. -/
theorem parameterConstantCoeffFourBlock_schurB
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    H.schurB.coeff 0 =
      (parameterConstantCoeffFourBlock H).schurB := by
  simp [parameterConstantCoeffFourBlock, GeneralFourBlock.schurB,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the kernel cleared Schur entry. -/
theorem parameterConstantCoeffFourBlock_schurC
    {R : Type v} [CommRing R]
    (H : GeneralFourBlock (Polynomial R)) :
    H.schurC.coeff 0 =
      (parameterConstantCoeffFourBlock H).schurC := by
  simp [parameterConstantCoeffFourBlock, GeneralFourBlock.schurC,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-! ## The actual finite Hessian block -/

/-- Finite special-fibre Hessian block in the same coordinate chart as the
honest parameter-series block. -/
noncomputable def adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  GeneralFourBlock.ofSymmetricMatrix
    (fun i j =>
      HC4.Polynomial.hessian
        (longitudinalRightRecenterHom (K := K) E.rawSpecialFiber)
        (rho i) (rho j))

/-- Entrywise parameter-zero specialisation of the honest recentered Hessian
four-block is literally the finite special-fibre Hessian four-block. -/
theorem parameterConstantCoeff_rightRecenteredHessianFourBlock
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    parameterConstantCoeffFourBlock
        (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E) =
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock rho E := by
  ext <;>
    simp [parameterConstantCoeffFourBlock,
      adaptiveAlignedEndpointRightRecenteredHessianFourBlock,
      adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_coeff_zero_recentered]

/-- The series active determinant at parameter zero is exactly the active
minor of the finite recentered special-fibre Hessian. -/
theorem rightRecenteredHessianFourBlock_activeDet_coeff_zero
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).activeDet.coeff 0 =
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho E).activeDet := by
  calc
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).activeDet.coeff 0 =
        (parameterConstantCoeffFourBlock
          (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E)).activeDet :=
      parameterConstantCoeffFourBlock_activeDet _
    _ =
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).activeDet := by
      rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-- Specialisation of the first cleared Schur entry. -/
theorem rightRecenteredHessianFourBlock_schurA_coeff_zero
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurA.coeff 0 =
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho E).schurA := by
  calc
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurA.coeff 0 =
        (parameterConstantCoeffFourBlock
          (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E)).schurA :=
      parameterConstantCoeffFourBlock_schurA _
    _ =
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).schurA := by
      rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-- Specialisation of the off-diagonal cleared Schur entry. -/
theorem rightRecenteredHessianFourBlock_schurB_coeff_zero
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurB.coeff 0 =
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho E).schurB := by
  calc
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurB.coeff 0 =
        (parameterConstantCoeffFourBlock
          (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E)).schurB :=
      parameterConstantCoeffFourBlock_schurB _
    _ =
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).schurB := by
      rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-- Specialisation of the kernel cleared Schur entry. -/
theorem rightRecenteredHessianFourBlock_schurC_coeff_zero
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurC.coeff 0 =
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho E).schurC := by
  calc
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).schurC.coeff 0 =
        (parameterConstantCoeffFourBlock
          (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E)).schurC :=
      parameterConstantCoeffFourBlock_schurC _
    _ =
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho E).schurC := by
      rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-! ## Positive determinant clock forces a rank-one constant Schur relation -/

/-- If the full determinant closes at a positive parameter order, the
constant cleared Schur determinant vanishes in every chart. -/
theorem rightRecenteredHessianFourBlock_schurConstant_det_eq_zero
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (rho : Equiv.Perm (Fin 4))
    (hdefect : 0 < B.aligned.endpoint.defect) :
    let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
      rho B.aligned.endpoint
    H.schurA.coeff 0 * H.schurC.coeff 0 -
      H.schurB.coeff 0 * H.schurB.coeff 0 = 0 := by
  dsimp only
  let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
    rho B.aligned.endpoint
  have hdet :
      H.polynomialSchurSeries.determinant =
        H.activeDet * Polynomial.X ^ B.aligned.endpoint.defect := by
    calc
      H.polynomialSchurSeries.determinant =
          H.activeDet * H.determinantCore :=
        H.polynomialSchurSeries_determinant
      _ = H.activeDet * Polynomial.X ^ B.aligned.endpoint.defect := by
        rw [B.rightRecenteredHessianFourBlock_determinantCore rho]
  have h0 := congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hdet
  have hne : B.aligned.endpoint.defect ≠ 0 := Nat.ne_of_gt hdefect
  simpa [H, GeneralFourBlock.polynomialSchurSeries,
    BinarySchurPolynomialSeries.determinant,
    Polynomial.coeff_zero_eq_eval_zero, hne] using h0

/-! ## One nonzero active minor exhausts both existing Schur architectures -/

/-- Once an active special-fibre Hessian minor is nonzero, the existing Schur
machinery is exhaustive.  A nonzero constant cleared Schur block gives the
rank-one-pivot clock; a zero constant cleared Schur block gives the exact
zero-Schur clock.

No blocker-pattern pivot identities are required. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredSchur_or_zeroSchur_of_active
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (rho : Equiv.Perm (Fin 4))
    (hdefect : 0 < B.aligned.endpoint.defect)
    (hactive :
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho B.aligned.endpoint).activeDet ≠ 0) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) := by
  let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
    rho B.aligned.endpoint
  have hactiveSeries : H.activeDet.coeff 0 ≠ 0 := by
    dsimp [H]
    rw [rightRecenteredHessianFourBlock_activeDet_coeff_zero]
    exact hactive

  by_cases hzero :
      H.schurA.coeff 0 = 0 ∧
        H.schurB.coeff 0 = 0 ∧
        H.schurC.coeff 0 = 0

  · right
    exact
      ⟨{
        block := H
        defect := B.aligned.endpoint.defect
        fullDet := by
          dsimp [H]
          exact B.rightRecenteredHessianFourBlock_determinantCore rho
        activeDet_coeff_zero_ne_zero := hactiveSeries
        schurA_coeff_zero := hzero.1
        schurB_coeff_zero := hzero.2.1
        schurC_coeff_zero := hzero.2.2
      }⟩

  · left
    have hnz : H.polynomialSchurSeries.ConstantBlockNonzero := by
      unfold BinarySchurPolynomialSeries.ConstantBlockNonzero
      simp only [GeneralFourBlock.polynomialSchurSeries]
      tauto

    have hdet0 :
        H.schurA.coeff 0 * H.schurC.coeff 0 -
          H.schurB.coeff 0 * H.schurB.coeff 0 = 0 := by
      dsimp [H]
      exact
        rightRecenteredHessianFourBlock_schurConstant_det_eq_zero
          B rho hdefect

    have hdetEq :
        H.polynomialSchurSeries.active.coeff 0 *
            H.polynomialSchurSeries.kernel.coeff 0 =
          H.polynomialSchurSeries.offDiag.coeff 0 *
            H.polynomialSchurSeries.offDiag.coeff 0 := by
      have heq :
          H.schurA.coeff 0 * H.schurC.coeff 0 =
            H.schurB.coeff 0 * H.schurB.coeff 0 :=
        sub_eq_zero.mp hdet0
      simpa [GeneralFourBlock.polynomialSchurSeries] using heq

    have hpivot :
        H.polynomialSchurSeries.LeftPivot ∨
          H.polynomialSchurSeries.RightAxisPivot :=
      H.polynomialSchurSeries.leftPivot_or_rightAxisPivot_of_constantBlock
        hnz hdetEq

    exact
      ⟨{
        block := H
        fullDet := by
          dsimp [H]
          exact B.rightRecenteredHessianFourBlock_determinantCore rho
        activeDet_coeff_zero_ne_zero := hactiveSeries
        rigid := hpivot
      }⟩

/-! ## Exhaustive blocker-facing algebraic frontier -/

/-- **Recentered blocker Hessian trichotomy.**

At positive defect, exactly one genuinely geometric question remains.  If
some coordinate chart has a nonzero active `2 x 2` special-fibre Hessian
minor, the existing rank-one or zero-Schur machinery applies automatically.
Otherwise every such chart minor vanishes.

The last alternative is the honest no-active-principal-chart branch; it is no
longer conflated with a failed Schur extraction.  Any later conversion of that
branch into a global Hessian-rank statement should be proved separately. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredSchur_or_zeroSchur_or_allActiveMinorsZero
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) ∨
      (∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).activeDet = 0) := by
  classical
  by_cases hchart :
      ∃ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).activeDet ≠ 0
  · rcases hchart with ⟨rho, hactive⟩
    rcases B.rightRecenteredSchur_or_zeroSchur_of_active
        rho hdefect hactive with hschur | hzero
    · exact Or.inl hschur
    · exact Or.inr (Or.inl hzero)
  · right
    right
    intro rho
    by_contra hne
    exact hchart ⟨rho, hne⟩

end

end HC4.Valuation
