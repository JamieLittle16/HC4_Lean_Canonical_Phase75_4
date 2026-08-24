import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningRankFrontier
import Mathlib.Tactic

/-!
# A18.4.91: a genuine rank-one opening has a scalar Hessian pivot

A18.4.90 leaves a sound rigidity branch: the post-opening special Hessian is
nonzero and every `2 x 2` minor vanishes.  Over the source polynomial domain,
such a symmetric matrix must have a nonzero diagonal entry.  Indeed, if all
four diagonal entries vanished, each off-diagonal square is itself a
`2 x 2` minor and therefore vanishes; the domain property then kills every
entry.

After a coordinate permutation we may therefore arrange that the `(0,0)`
entry of the honest parameter-series Hessian has nonzero constant coefficient.
This is the scalar pivot required for the next `1+3` cleared Schur clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u v
variable {K : Type u} [Field K] [CharZero K]

namespace GeneralFourBlock

variable {R : Type v} [CommRing R] [IsDomain R]

/-- A nonzero symmetric four-block with all `2 x 2` minors zero has a nonzero
diagonal entry. -/
theorem exists_diagonal_ne_zero_of_allTwoByTwoMinorsZero
    (H : GeneralFourBlock R)
    (hall : H.AllTwoByTwoMinorsZero)
    (hmat : H.matrix ≠ 0) :
    H.a ≠ 0 ∨ H.d ≠ 0 ∨ H.x ≠ 0 ∨ H.z ≠ 0 := by
  by_contra hdiag
  push_neg at hdiag
  rcases hdiag with ⟨ha, hd, hx, hz⟩

  have hb2 : H.b * H.b = 0 := by
    have h := hall (0 : Fin 4) 1 1 0
    simpa [GeneralFourBlock.matrix, ha, hd] using h
  have hp2 : H.p * H.p = 0 := by
    have h := hall (0 : Fin 4) 2 2 0
    simpa [GeneralFourBlock.matrix, ha, hx] using h
  have hq2 : H.q * H.q = 0 := by
    have h := hall (0 : Fin 4) 3 3 0
    simpa [GeneralFourBlock.matrix, ha, hz] using h
  have hr2 : H.r * H.r = 0 := by
    have h := hall (1 : Fin 4) 2 2 1
    simpa [GeneralFourBlock.matrix, hd, hx] using h
  have hs2 : H.s * H.s = 0 := by
    have h := hall (1 : Fin 4) 3 3 1
    simpa [GeneralFourBlock.matrix, hd, hz] using h
  have hy2 : H.y * H.y = 0 := by
    have h := hall (2 : Fin 4) 3 3 2
    simpa [GeneralFourBlock.matrix, hx, hz] using h

  have hb : H.b = 0 := by
    rcases mul_eq_zero.mp hb2 with hb | hb <;> exact hb
  have hp : H.p = 0 := by
    rcases mul_eq_zero.mp hp2 with hp | hp <;> exact hp
  have hq : H.q = 0 := by
    rcases mul_eq_zero.mp hq2 with hq | hq <;> exact hq
  have hr : H.r = 0 := by
    rcases mul_eq_zero.mp hr2 with hr | hr <;> exact hr
  have hs : H.s = 0 := by
    rcases mul_eq_zero.mp hs2 with hs | hs <;> exact hs
  have hy : H.y = 0 := by
    rcases mul_eq_zero.mp hy2 with hy | hy <;> exact hy

  apply hmat
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralFourBlock.matrix, ha, hd, hx, hz, hb, hp, hq, hr, hs, hy]

end GeneralFourBlock

private noncomputable def scalarPivotSwap01 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

private noncomputable def scalarPivotSwap02 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2

private noncomputable def scalarPivotSwap03 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3

@[simp] private theorem scalarPivotSwap01_zero : scalarPivotSwap01 0 = 1 := by decide
@[simp] private theorem scalarPivotSwap01_one : scalarPivotSwap01 1 = 0 := by decide
@[simp] private theorem scalarPivotSwap01_two : scalarPivotSwap01 2 = 2 := by decide
@[simp] private theorem scalarPivotSwap01_three : scalarPivotSwap01 3 = 3 := by decide

@[simp] private theorem scalarPivotSwap02_zero : scalarPivotSwap02 0 = 2 := by decide
@[simp] private theorem scalarPivotSwap02_one : scalarPivotSwap02 1 = 1 := by decide
@[simp] private theorem scalarPivotSwap02_two : scalarPivotSwap02 2 = 0 := by decide
@[simp] private theorem scalarPivotSwap02_three : scalarPivotSwap02 3 = 3 := by decide

@[simp] private theorem scalarPivotSwap03_zero : scalarPivotSwap03 0 = 3 := by decide
@[simp] private theorem scalarPivotSwap03_one : scalarPivotSwap03 1 = 1 := by decide
@[simp] private theorem scalarPivotSwap03_two : scalarPivotSwap03 2 = 2 := by decide
@[simp] private theorem scalarPivotSwap03_three : scalarPivotSwap03 3 = 0 := by decide

/-- Honest scalar-pivot chart on a genuine rank-one kernel opening. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningScalarPivot
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1) where
  permutation : Equiv.Perm (Fin 4)
  pivot_coeff_zero_ne_zero :
    (scaleAwareHessianFourBlock permutation G.firstContact.opening).a.coeff 0 ≠ 0

/-- **Every genuine rank-one first-contact opening has a scalar pivot.** -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry.scalarPivot
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningScalarPivot G) := by
  let s := G.firstContact.opening
  let H := scaleAwareSpecialHessianFourBlock s
  have hmat : H.matrix ≠ 0 := by
    intro hzero
    apply G.specialHessian_ne_zero
    rw [← scaleAwareSpecialHessianFourBlock_matrix s]
    exact hzero
  rcases H.exists_diagonal_ne_zero_of_allTwoByTwoMinorsZero G.allTwoByTwo hmat with
    ha | hd | hx | hz
  · exact ⟨{
      permutation := Equiv.refl (Fin 4)
      pivot_coeff_zero_ne_zero := by
        change (scaleAwareHessianFourBlock (Equiv.refl (Fin 4)) s).a.coeff 0 ≠ 0
        simpa [H, scaleAwareSpecialHessianFourBlock,
          parameterConstantCoeffFourBlock] using ha
    }⟩
  · exact ⟨{
      permutation := scalarPivotSwap01
      pivot_coeff_zero_ne_zero := by
        change (scaleAwareHessianFourBlock scalarPivotSwap01 s).a.coeff 0 ≠ 0
        simpa [H, scaleAwareSpecialHessianFourBlock,
          scaleAwareHessianFourBlock, GeneralFourBlock.ofSymmetricMatrix,
          parameterConstantCoeffFourBlock] using hd
    }⟩
  · exact ⟨{
      permutation := scalarPivotSwap02
      pivot_coeff_zero_ne_zero := by
        change (scaleAwareHessianFourBlock scalarPivotSwap02 s).a.coeff 0 ≠ 0
        simpa [H, scaleAwareSpecialHessianFourBlock,
          scaleAwareHessianFourBlock, GeneralFourBlock.ofSymmetricMatrix,
          parameterConstantCoeffFourBlock] using hx
    }⟩
  · exact ⟨{
      permutation := scalarPivotSwap03
      pivot_coeff_zero_ne_zero := by
        change (scaleAwareHessianFourBlock scalarPivotSwap03 s).a.coeff 0 ≠ 0
        simpa [H, scaleAwareSpecialHessianFourBlock,
          scaleAwareHessianFourBlock, GeneralFourBlock.ofSymmetricMatrix,
          parameterConstantCoeffFourBlock] using hz
    }⟩

end

end HC4.Valuation
