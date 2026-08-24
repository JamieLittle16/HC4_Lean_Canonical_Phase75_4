import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidTopLayer
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreDirectionLock
import Mathlib.Tactic

/-!
# Final assembly A17.3C: an explicit transverse kernel of the rigid top layer

A17.3B proved that the maximal nonlinear ordinary-homogeneous layer of the
literal rigid special fibre is a scalar multiple of `L^D`, with `D >= 2`.
This file extracts an explicit constant direction in `ker L` which has a
nonzero transverse component and proves, on the nose, that the Hessian of the
maximal layer kills that constant vector.

No descent is claimed here.  The point is to replace the abstract linear-power
normal form by the exact constant kernel direction needed by the final
cross-degree locking argument.  The full-special-fibre all-minors certificate
is retained through `topLayer.rigid`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A deterministic transverse coordinate different from a chosen pivot. -/
def rigidTopTransverseIndex (p : Fin 4) : Fin 4 :=
  if p = (1 : Fin 4) then (2 : Fin 4) else (1 : Fin 4)

@[simp] theorem rigidTopTransverseIndex_ne_zero (p : Fin 4) :
    rigidTopTransverseIndex p ≠ (0 : Fin 4) := by
  fin_cases p <;> simp [rigidTopTransverseIndex]

@[simp] theorem rigidTopTransverseIndex_ne_pivot (p : Fin 4) :
    rigidTopTransverseIndex p ≠ p := by
  fin_cases p <;> simp [rigidTopTransverseIndex]

/-- The canonical two-coordinate vector perpendicular to a coefficient vector
`c`: it has value `c p` in the selected transverse coordinate and `-c j` in
the pivot coordinate. -/
def rigidTopKernelDirection
    (c : Fin 4 → K) (p : Fin 4) : Fin 4 → K :=
  let j := rigidTopTransverseIndex p
  fun i => if i = j then c p else if i = p then - c j else 0

@[simp] theorem rigidTopKernelDirection_transverse
    (c : Fin 4 → K) (p : Fin 4) :
    rigidTopKernelDirection c p (rigidTopTransverseIndex p) = c p := by
  simp [rigidTopKernelDirection, rigidTopTransverseIndex_ne_pivot]

/-- The chosen vector is perpendicular to the top linear form. -/
theorem rigidTopKernelDirection_annihilates_linearForm
    (c : Fin 4 → K) (p : Fin 4) :
    ∑ i : Fin 4, c i * rigidTopKernelDirection c p i = 0 := by
  fin_cases p <;>
    simp [rigidTopKernelDirection, rigidTopTransverseIndex, Fin.sum_univ_four] <;>
    ring

/-- Four-variable version of the Hessian formula already used by the binary
direction-lock proof. -/
theorem hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour
    (a : K)
    (c : Fin 4 → K)
    (n : ℕ)
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) i j =
      MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) * c i * c j) *
        (gradientRatioLinearForm c) ^ n := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c i (n + 1)]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c j n]
  push_cast
  simp only [MvPolynomial.C_mul]
  ring

/-- The explicit vector perpendicular to `c` is a constant Hessian-kernel
vector of every positive-degree linear power `a * L^(n+2)`. -/
theorem hessian_linearPower_mulVec_rigidTopKernelDirection
    (a : K)
    (c : Fin 4 → K)
    (n : ℕ)
    (p : Fin 4) :
    (HC4.Polynomial.hessian
      (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2))).mulVec
        (fun i => MvPolynomial.C (rigidTopKernelDirection c p i)) = 0 := by
  funext r
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_four]
  repeat' rw [hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour]
  fin_cases p <;> fin_cases r <;>
    simp [rigidTopKernelDirection, rigidTopTransverseIndex] <;> ring

/-- A17.3C kernel packet: the top-layer direction is now completely explicit,
nonzero, transverse, and certified in the Hessian kernel of the actual
maximal homogeneous component. -/
structure AdaptiveAlignedSmithCanonicalRigidTopKernelData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) where
  topLayer : AdaptiveAlignedSmithCanonicalRigidTopLayerData S
  pivot : Fin 4
  pivot_ne_zero : topLayer.ratio pivot ≠ 0
  transverse : Fin 4
  transverse_eq : transverse = rigidTopTransverseIndex pivot
  transverse_ne_zero : transverse ≠ (0 : Fin 4)
  transverse_ne_pivot : transverse ≠ pivot
  direction : Fin 4 → K
  direction_eq : direction = rigidTopKernelDirection topLayer.ratio pivot
  direction_ne_zero : direction ≠ 0
  direction_transverse_ne_zero : direction transverse ≠ 0
  linearForm_annihilation :
    ∑ i : Fin 4, topLayer.ratio i * direction i = 0
  topKernel :
    (HC4.Polynomial.hessian topLayer.top).mulVec
      (fun i => MvPolynomial.C (direction i)) = 0

namespace AdaptiveAlignedSmithCanonicalRigidTopLayerData

/-- The coefficient vector of the nonzero top linear power is nonzero. -/
theorem ratio_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (T : AdaptiveAlignedSmithCanonicalRigidTopLayerData S) :
    T.ratio ≠ 0 := by
  intro hratio
  have hL : gradientRatioLinearForm T.ratio = 0 := by
    rw [hratio]
    simp [gradientRatioLinearForm]
  apply T.top_ne_zero
  rw [T.linearPower, hL]
  have hpos : 0 < T.degree := lt_of_lt_of_le (by decide : 0 < 2) T.degree_ge_two
  simp [Nat.ne_of_gt hpos]

/-- Hence some coefficient of the top linear form is nonzero. -/
theorem exists_ratio_pivot
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (T : AdaptiveAlignedSmithCanonicalRigidTopLayerData S) :
    ∃ p : Fin 4, T.ratio p ≠ 0 := by
  by_contra h
  apply T.ratio_ne_zero
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

/-- **A17.3C top-kernel extraction.** -/
theorem toRigidTopKernelData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (T : AdaptiveAlignedSmithCanonicalRigidTopLayerData S) :
    Nonempty (AdaptiveAlignedSmithCanonicalRigidTopKernelData S) := by
  rcases T.exists_ratio_pivot with ⟨p, hp⟩
  let j := rigidTopTransverseIndex p
  let v := rigidTopKernelDirection T.ratio p
  have hj0 : j ≠ (0 : Fin 4) := by
    simpa [j] using rigidTopTransverseIndex_ne_zero p
  have hjp : j ≠ p := by
    simpa [j] using rigidTopTransverseIndex_ne_pivot p
  have hvj : v j ≠ 0 := by
    simpa [v, j] using hp
  have hv : v ≠ 0 := by
    intro hzero
    apply hvj
    rw [hzero]
    rfl
  have hann : ∑ i : Fin 4, T.ratio i * v i = 0 := by
    simpa [v] using rigidTopKernelDirection_annihilates_linearForm T.ratio p
  obtain ⟨n, hdeg⟩ : ∃ n : ℕ, T.degree = n + 2 := by
    exact ⟨T.degree - 2, (Nat.sub_add_cancel T.degree_ge_two).symm⟩
  have htop :
      T.top = MvPolynomial.C T.coefficient *
        (gradientRatioLinearForm T.ratio) ^ (n + 2) := by
    rw [T.linearPower, hdeg]
  have hker0 := hessian_linearPower_mulVec_rigidTopKernelDirection
    T.coefficient T.ratio n p
  have hker :
      (HC4.Polynomial.hessian T.top).mulVec
        (fun i => MvPolynomial.C (v i)) = 0 := by
    rw [htop]
    exact hker0
  exact ⟨{
    topLayer := T
    pivot := p
    pivot_ne_zero := hp
    transverse := j
    transverse_eq := rfl
    transverse_ne_zero := hj0
    transverse_ne_pivot := hjp
    direction := v
    direction_eq := rfl
    direction_ne_zero := hv
    direction_transverse_ne_zero := hvj
    linearForm_annihilation := hann
    topKernel := hker
  }⟩

end AdaptiveAlignedSmithCanonicalRigidTopLayerData

end

end HC4.Valuation
