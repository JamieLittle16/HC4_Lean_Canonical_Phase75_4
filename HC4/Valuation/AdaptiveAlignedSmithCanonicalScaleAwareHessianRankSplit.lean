import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactActiveFourBlockRankThree
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianAllMinors
import Mathlib.Tactic

/-!
# A18.4.89: exact active chart or genuine rank-one special Hessian

The expensive parameter-series specialization is collapsed once to a finite
special-fibre four-block. The subsequent ten-relation rank split works only
with those ten finite entries; no branch unfolds the polynomial-series Hessian.
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

/-- Genuine finite Hessian block in an arbitrary simultaneous permutation. -/
private noncomputable def scaleAwarePermutedFiniteHessianBlock
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  GeneralFourBlock.ofSymmetricMatrix
    (fun i j =>
      HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber s.family) (rho i) (rho j))

/-- Identity-coordinate version of the finite block. -/
private noncomputable def scaleAwareFiniteHessianBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  scaleAwarePermutedFiniteHessianBlock (Equiv.refl (Fin 4)) s

/-- Hessian symmetry on the finite special fibre. -/
private theorem scaleAwareFiniteHessian_symmetric
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber s.family) i j =
      HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber s.family) j i := by
  change
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i (polynomialFamilySpecialFiber s.family)) =
      MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (polynomialFamilySpecialFiber s.family))
  exact (pderiv_comm_backport i j _).symm

/-- Specializing the honest series block once gives exactly the finite
permuted Hessian block. -/
private theorem parameterConstantCoeff_scaleAwareHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    parameterConstantCoeffFourBlock (scaleAwareHessianFourBlock rho s) =
      scaleAwarePermutedFiniteHessianBlock rho s := by
  ext <;>
    simp [parameterConstantCoeffFourBlock,
      scaleAwareHessianFourBlock,
      scaleAwarePermutedFiniteHessianBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      scaleAwareHessianSeriesMatrix_coeff_zero]

private theorem scaleAwareSpecialHessianFourBlock_eq_finite
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    scaleAwareSpecialHessianFourBlock s = scaleAwareFiniteHessianBlock s := by
  unfold scaleAwareSpecialHessianFourBlock scaleAwareFiniteHessianBlock
  exact parameterConstantCoeff_scaleAwareHessianFourBlock
    (Equiv.refl (Fin 4)) s

/-- The finite block is exactly the genuine special-fibre Hessian matrix. -/
theorem scaleAwareSpecialHessianFourBlock_matrix
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareSpecialHessianFourBlock s).matrix =
      HC4.Polynomial.hessian (polynomialFamilySpecialFiber s.family) := by
  rw [scaleAwareSpecialHessianFourBlock_eq_finite]
  unfold scaleAwareFiniteHessianBlock scaleAwarePermutedFiniteHessianBlock
  simpa using
    (GeneralFourBlock.matrix_ofSymmetricMatrix
      (HC4.Polynomial.hessian (polynomialFamilySpecialFiber s.family))
      (scaleAwareFiniteHessian_symmetric s))

/-! ## The finite permutations used by the ten core relations -/

private noncomputable def scaleRankSwap12 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2

private noncomputable def scaleRankSwap13 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 3

private noncomputable def scaleRankSwap02 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2

private noncomputable def scaleRankSwap03 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3

private noncomputable def scaleRankOrder2301 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

private noncomputable def scaleRankSwap23 : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

private noncomputable def scaleRankOrder2130 : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 3)

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

/-- Finite version of the same statement, used by the rank split so the
parameter-series machinery is never reopened in a branch. -/
private theorem scaleAwareHessianFourBlock_activeDet_coeff_zero_finite
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 =
      (scaleAwarePermutedFiniteHessianBlock rho s).activeDet := by
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero,
    parameterConstantCoeff_scaleAwareHessianFourBlock]

/-! ## Tiny finite permutation identities -/

private theorem active_swap12_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwarePermutedFiniteHessianBlock scaleRankSwap12 s).activeDet =
      let H := scaleAwareFiniteHessianBlock s
      H.a * H.x - H.p * H.p := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem active_swap13_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwarePermutedFiniteHessianBlock scaleRankSwap13 s).activeDet =
      let H := scaleAwareFiniteHessianBlock s
      H.a * H.z - H.q * H.q := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem active_swap02_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwarePermutedFiniteHessianBlock scaleRankSwap02 s).activeDet =
      let H := scaleAwareFiniteHessianBlock s
      H.x * H.d - H.r * H.r := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem active_swap03_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwarePermutedFiniteHessianBlock scaleRankSwap03 s).activeDet =
      let H := scaleAwareFiniteHessianBlock s
      H.z * H.d - H.s * H.s := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem active_order2301_eq
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2301 s).activeDet =
      let H := scaleAwareFiniteHessianBlock s
      H.x * H.z - H.y * H.y := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem relations_order2031
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    let H := scaleAwareFiniteHessianBlock s
    let T := scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s
    T.activeDet = H.a * H.x - H.p * H.p ∧
      T.x * T.d - T.r * T.r = H.a * H.z - H.q * H.q ∧
      T.p * T.d - T.b * T.r = H.y * H.a - H.p * H.q := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem relations_order2130
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    let H := scaleAwareFiniteHessianBlock s
    let T := scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s
    T.activeDet = H.x * H.d - H.r * H.r ∧
      T.x * T.d - T.r * T.r = H.z * H.d - H.s * H.s ∧
      T.p * T.d - T.b * T.r = H.y * H.d - H.r * H.s := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

private theorem relations_swap23
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    let H := scaleAwareFiniteHessianBlock s
    let T := scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s
    T.activeDet = H.a * H.d - H.b * H.b ∧
      T.x * T.d - T.r * T.r = H.z * H.d - H.s * H.s ∧
      T.p * T.d - T.b * T.r = H.q * H.d - H.b * H.s := by
  simp [scaleAwarePermutedFiniteHessianBlock, scaleAwareFiniteHessianBlock,
    GeneralFourBlock.activeDet, GeneralFourBlock.ofSymmetricMatrix,
    scaleAwareFiniteHessian_symmetric, mul_comm]

/-- **Finite Hessian rank split on an arbitrary scale-aware state.** -/
theorem scaleAwareHessian_exactActive_or_rankOne
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty (AdaptiveAlignedSmithCanonicalExactActiveFourBlock s) ∨
      (scaleAwareSpecialHessianFourBlock s).AllTwoByTwoMinorsZero := by
  let H := scaleAwareFiniteHessianBlock s
  have hH : scaleAwareSpecialHessianFourBlock s = H :=
    scaleAwareSpecialHessianFourBlock_eq_finite s

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
                      rw [hH]
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
                      have hrel := relations_order2031 s
                      dsimp only at hrel
                      have h01 :
                          (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                        rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
                        change
                          (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).activeDet = 0
                        rw [hrel.1]
                        exact hp02
                      have h21 :
                          let T := parameterConstantCoeffFourBlock
                            (scaleAwareHessianFourBlock rho s)
                          T.x * T.d - T.r * T.r = 0 := by
                        dsimp only
                        rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                        change
                          (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).x *
                              (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).d -
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).r *
                              (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).r = 0
                        rw [hrel.2.1]
                        exact hp03
                      have hcross :
                          let T := parameterConstantCoeffFourBlock
                            (scaleAwareHessianFourBlock rho s)
                          T.p * T.d - T.b * T.r ≠ 0 := by
                        dsimp only
                        rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                        change
                          (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).p *
                              (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).d -
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).b *
                              (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2031 s).r ≠ 0
                        rw [hrel.2.2]
                        exact hc203
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
                    have hrel := relations_order2130 s
                    dsimp only at hrel
                    have h01 :
                        (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                      rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
                      change
                        (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).activeDet = 0
                      rw [hrel.1]
                      exact hp12
                    have h21 :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.x * T.d - T.r * T.r = 0 := by
                      dsimp only
                      rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                      change
                        (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).x *
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).d -
                          (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).r *
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).r = 0
                      rw [hrel.2.1]
                      exact hp13
                    have hcross :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.p * T.d - T.b * T.r ≠ 0 := by
                      dsimp only
                      rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                      change
                        (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).p *
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).d -
                          (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).b *
                            (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2130 s).r ≠ 0
                      rw [hrel.2.2]
                      exact hc213
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
                  have hrel := relations_swap23 s
                  dsimp only at hrel
                  have h01 :
                      (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 = 0 := by
                    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
                    change
                      (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).activeDet = 0
                    rw [hrel.1]
                    exact hp01
                  have h21 :
                      let T := parameterConstantCoeffFourBlock
                        (scaleAwareHessianFourBlock rho s)
                      T.x * T.d - T.r * T.r = 0 := by
                    dsimp only
                    rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                    change
                      (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).x *
                          (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).d -
                        (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).r *
                          (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).r = 0
                    rw [hrel.2.1]
                    exact hp13
                  have hcross :
                      let T := parameterConstantCoeffFourBlock
                        (scaleAwareHessianFourBlock rho s)
                      T.p * T.d - T.b * T.r ≠ 0 := by
                    dsimp only
                    rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                    change
                      (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).p *
                          (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).d -
                        (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).b *
                          (scaleAwarePermutedFiniteHessianBlock scaleRankSwap23 s).r ≠ 0
                    rw [hrel.2.2]
                    exact hc013
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
                  · rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
                    change (scaleAwareFiniteHessianBlock s).activeDet = 0
                    simpa [H, GeneralFourBlock.activeDet] using hp01
                  · have h21 :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.x * T.d - T.r * T.r = 0 := by
                      dsimp only
                      rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                      change
                        (scaleAwareFiniteHessianBlock s).x *
                            (scaleAwareFiniteHessianBlock s).d -
                          (scaleAwareFiniteHessianBlock s).r *
                            (scaleAwareFiniteHessianBlock s).r = 0
                      exact hp12
                    simpa [parameterConstantCoeffFourBlock] using h21
                  · have hcross :
                        let T := parameterConstantCoeffFourBlock
                          (scaleAwareHessianFourBlock rho s)
                        T.p * T.d - T.b * T.r ≠ 0 := by
                      dsimp only
                      rw [parameterConstantCoeff_scaleAwareHessianFourBlock]
                      change
                        (scaleAwareFiniteHessianBlock s).p *
                            (scaleAwareFiniteHessianBlock s).d -
                          (scaleAwareFiniteHessianBlock s).b *
                            (scaleAwareFiniteHessianBlock s).r ≠ 0
                      exact hc012
                    simpa [parameterConstantCoeffFourBlock] using hcross
                exact ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofShear02
                  rho hactive⟩
            · left
              let rho := scaleRankOrder2301
              refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
                { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
              rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
              change
                (scaleAwarePermutedFiniteHessianBlock scaleRankOrder2301 s).activeDet ≠ 0
              rw [active_order2301_eq]
              exact hp23
          · left
            let rho := scaleRankSwap03
            refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
              { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
            rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
            change
              (scaleAwarePermutedFiniteHessianBlock scaleRankSwap03 s).activeDet ≠ 0
            rw [active_swap03_eq]
            exact hp13
        · left
          let rho := scaleRankSwap02
          refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
            { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
          rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
          change
            (scaleAwarePermutedFiniteHessianBlock scaleRankSwap02 s).activeDet ≠ 0
          rw [active_swap02_eq]
          exact hp12
      · left
        let rho := scaleRankSwap13
        refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
          { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
        rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
        change
          (scaleAwarePermutedFiniteHessianBlock scaleRankSwap13 s).activeDet ≠ 0
        rw [active_swap13_eq]
        exact hp03
    · left
      let rho := scaleRankSwap12
      refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
        { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
      rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
      change
        (scaleAwarePermutedFiniteHessianBlock scaleRankSwap12 s).activeDet ≠ 0
      rw [active_swap12_eq]
      exact hp02
  · left
    let rho := Equiv.refl (Fin 4)
    refine ⟨AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect
      { permutation := rho, activeDet_coeff_zero_ne_zero := ?_ }⟩
    rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_finite]
    change (scaleAwareFiniteHessianBlock s).activeDet ≠ 0
    simpa [H, GeneralFourBlock.activeDet] using hp01

end

end HC4.Valuation