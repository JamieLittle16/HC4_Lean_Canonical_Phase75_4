import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactActiveFourBlockRankThree
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianAllMinors
import Mathlib.Tactic

/-!
# A18.4.89: exact active chart or genuine rank-one special Hessian

For an arbitrary scale-aware restart state, inspect the honest special-fibre
Hessian itself.  The identity four-block already contains the full symmetric
`4 x 4` matrix, so `AllTwoByTwoMinorsZero` is the exact division-free
rank-at-most-one condition.

If that condition fails, one of the ten finite core relations used in the
A18 blocker rank-one proof must fail.  The six principal relations are exposed
by simultaneous coordinate permutations.  Once all six principal relations
vanish, each of the four possible cross relations is exposed by the existing
determinant-one `e_0 -> e_0 + e_2` shear after a suitable permutation.

Hence every state has exactly the geometric split needed by the kernel-opening
audit:

* an honest exact active `2 x 2` Hessian chart, immediately consumable by
  A18.4.88; or
* every `2 x 2` minor of the actual special-fibre Hessian vanishes.

No repair state, ramified order, or homogeneity assumption occurs in this
lemma.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The finite special-fibre Hessian four-block of a scale-aware state. -/
noncomputable def scaleAwareSpecialHessianFourBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  parameterConstantCoeffFourBlock
    (scaleAwareHessianFourBlock (Equiv.refl (Fin 4)) s)

/-- Constant coefficient of the honest Hessian series is literally the
Hessian of the special fibre. -/
theorem scaleAwareHessianSeriesMatrix_coeff_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (i j : Fin 4) :
    (scaleAwareHessianSeriesMatrix s i j).coeff 0 =
      HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber s.family) i j := by
  unfold scaleAwareHessianSeriesMatrix
  change
    (polynomialFamilySeriesHom (K := K)
      (HC4.Polynomial.hessian s.family i j)).coeff 0 = _
  change
    Polynomial.constantCoeff
      (polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian s.family i j)) = _
  rw [polynomialFamilySeriesHom_constantCoeff]
  simp [HC4.Polynomial.hessian_apply,
    polynomialFamilySpecialFiber, MvPolynomial.pderiv_map]

attribute [local simp] scaleAwareHessianSeriesMatrix_coeff_zero
attribute [local simp] GeneralFourBlock.activeDet
attribute [local simp] HC4.Polynomial.hessian_apply
attribute [local simp] pderiv_comm_commRing mul_comm

/-- The finite block is exactly the genuine special-fibre Hessian matrix. -/
theorem scaleAwareSpecialHessianFourBlock_matrix
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareSpecialHessianFourBlock s).matrix =
      HC4.Polynomial.hessian (polynomialFamilySpecialFiber s.family) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaleAwareSpecialHessianFourBlock,
      parameterConstantCoeffFourBlock,
      scaleAwareHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      GeneralFourBlock.matrix,
      scaleAwareHessianSeriesMatrix_coeff_zero]

/-! ## The finite permutations used by the ten core relations -/

private noncomputable def scaleRankSwap12 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2

private noncomputable def scaleRankSwap13 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 3

private noncomputable def scaleRankSwap02 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2

private noncomputable def scaleRankSwap03 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3

/-- Local order `(2,3,0,1)`. -/
private noncomputable def scaleRankOrder2301 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

/-- Local order `(0,1,3,2)`. -/
private noncomputable def scaleRankSwap23 : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

/-- Local order `(2,1,3,0)`. -/
private noncomputable def scaleRankOrder2130 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 3)

/-- Local order `(2,0,3,1)`. -/
private noncomputable def scaleRankOrder2031 : Equiv.Perm (Fin 4) :=
  ((Equiv.swap 0 1).trans (Equiv.swap 1 2)).trans (Equiv.swap 1 3)

@[simp] private theorem scaleRankSwap12_zero : scaleRankSwap12 0 = 0 := by decide
@[simp] private theorem scaleRankSwap12_one : scaleRankSwap12 1 = 2 := by decide
@[simp] private theorem scaleRankSwap12_two : scaleRankSwap12 2 = 1 := by decide
@[simp] private theorem scaleRankSwap12_three : scaleRankSwap12 3 = 3 := by decide

@[simp] private theorem scaleRankSwap13_zero : scaleRankSwap13 0 = 0 := by decide
@[simp] private theorem scaleRankSwap13_one : scaleRankSwap13 1 = 3 := by decide
@[simp] private theorem scaleRankSwap13_two : scaleRankSwap13 2 = 2 := by decide
@[simp] private theorem scaleRankSwap13_three : scaleRankSwap13 3 = 1 := by decide

@[simp] private theorem scaleRankSwap02_zero : scaleRankSwap02 0 = 2 := by decide
@[simp] private theorem scaleRankSwap02_one : scaleRankSwap02 1 = 1 := by decide
@[simp] private theorem scaleRankSwap02_two : scaleRankSwap02 2 = 0 := by decide
@[simp] private theorem scaleRankSwap02_three : scaleRankSwap02 3 = 3 := by decide

@[simp] private theorem scaleRankSwap03_zero : scaleRankSwap03 0 = 3 := by decide
@[simp] private theorem scaleRankSwap03_one : scaleRankSwap03 1 = 1 := by decide
@[simp] private theorem scaleRankSwap03_two : scaleRankSwap03 2 = 2 := by decide
@[simp] private theorem scaleRankSwap03_three : scaleRankSwap03 3 = 0 := by decide

@[simp] private theorem scaleRankOrder2301_zero : scaleRankOrder2301 0 = 2 := by decide
@[simp] private theorem scaleRankOrder2301_one : scaleRankOrder2301 1 = 3 := by decide
@[simp] private theorem scaleRankOrder2301_two : scaleRankOrder2301 2 = 0 := by decide
@[simp] private theorem scaleRankOrder2301_three : scaleRankOrder2301 3 = 1 := by decide

@[simp] private theorem scaleRankSwap23_zero : scaleRankSwap23 0 = 0 := by decide
@[simp] private theorem scaleRankSwap23_one : scaleRankSwap23 1 = 1 := by decide
@[simp] private theorem scaleRankSwap23_two : scaleRankSwap23 2 = 3 := by decide
@[simp] private theorem scaleRankSwap23_three : scaleRankSwap23 3 = 2 := by decide

@[simp] private theorem scaleRankOrder2130_zero : scaleRankOrder2130 0 = 2 := by decide
@[simp] private theorem scaleRankOrder2130_one : scaleRankOrder2130 1 = 1 := by decide
@[simp] private theorem scaleRankOrder2130_two : scaleRankOrder2130 2 = 3 := by decide
@[simp] private theorem scaleRankOrder2130_three : scaleRankOrder2130 3 = 0 := by decide

@[simp] private theorem scaleRankOrder2031_zero : scaleRankOrder2031 0 = 2 := by decide
@[simp] private theorem scaleRankOrder2031_one : scaleRankOrder2031 1 = 0 := by decide
@[simp] private theorem scaleRankOrder2031_two : scaleRankOrder2031 2 = 3 := by decide
@[simp] private theorem scaleRankOrder2031_three : scaleRankOrder2031 3 = 1 := by decide

/-- The active determinant at parameter zero is the active determinant of the
finite special block in the same coordinate ordering. -/
theorem scaleAwareHessianFourBlock_activeDet_coeff_zero
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 =
      (parameterConstantCoeffFourBlock
        (scaleAwareHessianFourBlock rho s)).activeDet :=
  parameterConstantCoeffFourBlock_activeDet _

/-- **Finite Hessian rank split on an arbitrary scale-aware state.** -/
theorem scaleAwareHessian_exactActive_or_rankOne
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty (AdaptiveAlignedSmithCanonicalExactActiveFourBlock s) ∨
      (scaleAwareSpecialHessianFourBlock s).AllTwoByTwoMinorsZero := by
  let H := scaleAwareSpecialHessianFourBlock s

  by_cases hp01 : H.a * H.d - H.b * H.b = 0
  · by_cases hp02 : H.a * H.x - H.p * H.p = 0
    · by_cases hp03 : H.a * H.z - H.q * H.q = 0
      · by_cases hp12 : H.x * H.d - H.r * H.r = 0
        · by_cases hp13 : H.z * H.d - H.s * H.s = 0
          · by_cases hp23 : H.x * H.z - H.y * H.y = 0
            · by_cases hc012 : H.p * H.d - H.b * H.r = 0
              · by_cases hc013 : H.q * H.d - H.b * H.s = 0
                · by_cases hc213 : H.y * H.d - H.r * H.s = 0
                  · by_cases hc203 : H.y * H.a - H.p * H.q = 0
                    · right
                      exact GeneralFourBlock.allTwoByTwoMinorsZero_of_rankOneCoreRelations
                        H {
                          principal01 := hp01
                          principal02 := hp02
                          principal03 := hp03
                          principal12 := hp12
                          principal13 := hp13
                          principal23 := hp23
                          cross012 := hc012
                          cross013 := hc013
                          cross213 := hc213
                          cross203 := hc203
                        }
                    · left
                      let rho := scaleRankOrder2031
                      have h01 :
                          (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                        rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
                        simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                          scaleAwareHessianFourBlock,
                          parameterConstantCoeffFourBlock,
                          GeneralFourBlock.ofSymmetricMatrix,
                          Equiv.trans_apply] using hp02
                      have h21 :
                          let T := parameterConstantCoeffFourBlock
                            (scaleAwareHessianFourBlock rho s)
                          T.x * T.d - T.r * T.r = 0 := by
                        dsimp
                        simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                          scaleAwareHessianFourBlock,
                          parameterConstantCoeffFourBlock,
                          GeneralFourBlock.ofSymmetricMatrix,
                          Equiv.trans_apply] using hp03
                      have hcross :
                          let T := parameterConstantCoeffFourBlock
                            (scaleAwareHessianFourBlock rho s)
                          T.p * T.d - T.b * T.r ≠ 0 := by
                        dsimp
                        simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                          scaleAwareHessianFourBlock,
                          parameterConstantCoeffFourBlock,
                          GeneralFourBlock.ofSymmetricMatrix,
                          Equiv.trans_apply, mul_comm] using hc203
                      have hactive :
                          ((scaleAwareHessianFourBlock rho s).shear02).activeDet.coeff 0 ≠ 0 := by
                        apply shear02_activeDet_coeff_zero_ne_zero_of_cross
                        · exact h01
                        · simpa [parameterConstantCoeffFourBlock] using h21
                        · simpa [parameterConstantCoeffFourBlock] using hcross
                      exact ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofShear02
                        rho hactive⟩
                  · left
                    let rho := scaleRankOrder2130
                    have h01 :
                        (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                      rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
                      simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                        scaleAwareHessianFourBlock,
                        parameterConstantCoeffFourBlock,
                        GeneralFourBlock.ofSymmetricMatrix,
                        Equiv.trans_apply] using hp12
                    have h21 :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.x * T.d - T.r * T.r = 0 := by
                      dsimp
                      simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                        scaleAwareHessianFourBlock,
                        parameterConstantCoeffFourBlock,
                        GeneralFourBlock.ofSymmetricMatrix,
                        Equiv.trans_apply] using hp13
                    have hcross :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.p * T.d - T.b * T.r ≠ 0 := by
                      dsimp
                      simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                        scaleAwareHessianFourBlock,
                        parameterConstantCoeffFourBlock,
                        GeneralFourBlock.ofSymmetricMatrix,
                        Equiv.trans_apply, mul_comm] using hc213
                    have hactive :
                        ((scaleAwareHessianFourBlock rho s).shear02).activeDet.coeff 0 ≠ 0 := by
                      apply shear02_activeDet_coeff_zero_ne_zero_of_cross
                      · exact h01
                      · simpa [parameterConstantCoeffFourBlock] using h21
                      · simpa [parameterConstantCoeffFourBlock] using hcross
                    exact ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofShear02
                      rho hactive⟩
                · left
                  let rho := scaleRankSwap23
                  have h01 :
                      (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
                    simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                      scaleAwareHessianFourBlock,
                      parameterConstantCoeffFourBlock,
                      GeneralFourBlock.ofSymmetricMatrix,
                      Equiv.trans_apply] using hp01
                  have h21 :
                      let T := parameterConstantCoeffFourBlock
                        (scaleAwareHessianFourBlock rho s)
                      T.x * T.d - T.r * T.r = 0 := by
                    dsimp
                    simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                      scaleAwareHessianFourBlock,
                      parameterConstantCoeffFourBlock,
                      GeneralFourBlock.ofSymmetricMatrix,
                      Equiv.trans_apply] using hp13
                  have hcross :
                      let T := parameterConstantCoeffFourBlock
                        (scaleAwareHessianFourBlock rho s)
                      T.p * T.d - T.b * T.r ≠ 0 := by
                    dsimp
                    simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                      scaleAwareHessianFourBlock,
                      parameterConstantCoeffFourBlock,
                      GeneralFourBlock.ofSymmetricMatrix,
                      Equiv.trans_apply] using hc013
                  have hactive :
                      ((scaleAwareHessianFourBlock rho s).shear02).activeDet.coeff 0 ≠ 0 := by
                    apply shear02_activeDet_coeff_zero_ne_zero_of_cross
                    · exact h01
                    · simpa [parameterConstantCoeffFourBlock] using h21
                    · simpa [parameterConstantCoeffFourBlock] using hcross
                  exact ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofShear02
                    rho hactive⟩
              · left
                let rho := Equiv.refl (Fin 4)
                have hactive :
                    ((scaleAwareHessianFourBlock rho s).shear02).activeDet.coeff 0 ≠ 0 := by
                  apply shear02_activeDet_coeff_zero_ne_zero_of_cross
                  · rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
                    simpa [H, scaleAwareSpecialHessianFourBlock, rho] using hp01
                  · simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                      parameterConstantCoeffFourBlock,
                      scaleAwareHessianFourBlock,
                      GeneralFourBlock.ofSymmetricMatrix] using hp12
                  · simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                      parameterConstantCoeffFourBlock,
                      scaleAwareHessianFourBlock,
                      GeneralFourBlock.ofSymmetricMatrix] using hc012
                exact ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofShear02
                  rho hactive⟩
            · left
              let rho := scaleRankOrder2301
              refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
                { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
              rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
              simpa [H, scaleAwareSpecialHessianFourBlock, rho,
                scaleAwareHessianFourBlock,
                parameterConstantCoeffFourBlock,
                GeneralFourBlock.ofSymmetricMatrix,
                Equiv.trans_apply] using hp23
          · left
            let rho := scaleRankSwap03
            refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
              { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
            rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
            simpa [H, scaleAwareSpecialHessianFourBlock, rho,
              scaleAwareHessianFourBlock,
              parameterConstantCoeffFourBlock,
              GeneralFourBlock.ofSymmetricMatrix,
              Equiv.trans_apply] using hp13
        · left
          let rho := scaleRankSwap02
          refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
            { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
          rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
          simpa [H, scaleAwareSpecialHessianFourBlock, rho,
            scaleAwareHessianFourBlock,
            parameterConstantCoeffFourBlock,
            GeneralFourBlock.ofSymmetricMatrix,
            Equiv.trans_apply] using hp12
      · left
        let rho := scaleRankSwap13
        refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
          { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
        rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
        simpa [H, scaleAwareSpecialHessianFourBlock, rho,
          scaleAwareHessianFourBlock,
          parameterConstantCoeffFourBlock,
          GeneralFourBlock.ofSymmetricMatrix,
          Equiv.trans_apply] using hp03
    · left
      let rho := scaleRankSwap12
      refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
        { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
      rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
      simpa [H, scaleAwareSpecialHessianFourBlock, rho,
        scaleAwareHessianFourBlock,
        parameterConstantCoeffFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        Equiv.trans_apply] using hp02
  · left
    let rho := Equiv.refl (Fin 4)
    refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
      { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero]
    simpa [H, scaleAwareSpecialHessianFourBlock, rho] using hp01

end

end HC4.Valuation