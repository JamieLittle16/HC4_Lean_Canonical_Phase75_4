import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurKernelCoordinateChart
import Mathlib.Tactic

/-!
# Returning the early-Schur kernel to the literal source coordinates

Stage 4B6 removes the auxiliary `swap02` / `shear02` Hessian chart.  Its
remaining kernel is still indexed by the retained coordinate permutation

    rho : Equiv.Perm (Fin 4),

so its matrix has entries

    Hess(F₀) (rho i) (rho j).

The first source key from Stages 4B1--B5 is extracted from `F₀` itself, in
literal source coordinates.  This file removes that final index discrepancy.
No polynomial is renamed and no source geometry is changed: we only reindex
the kernel vector by `rho.symm`.

The only linear-algebra input is mathlib's existing dot-product permutation
identity `comp_equiv_symm_dotProduct`.  Thus this is bookkeeping, not a new
classification or repair theorem.

After this file every early-Schur carrier has a nonzero polynomial vector

    w : Fin 4 -> MvPolynomial (Fin 4) K

satisfying literally

    Hess(polynomialFamilySpecialFiber C.family) * w = 0.

This is the coordinate system used by the first-key initial-form machinery,
so the next theorem can finally compare the polynomial kernel with the first
spatial key without any chart or permutation transport left over.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

/-! ## Generic simultaneous row/column permutation transport -/

/-- Reindex a column vector from `rho`-coordinates back to the original
coordinates. -/
def sourceCoordinateKernelVector
    {R : Type*}
    (rho : Equiv.Perm (Fin 4))
    (w : Fin 4 → R) :
    Fin 4 → R :=
  w ∘ rho.symm

@[simp] theorem sourceCoordinateKernelVector_apply
    {R : Type*}
    (rho : Equiv.Perm (Fin 4))
    (w : Fin 4 → R)
    (i : Fin 4) :
    sourceCoordinateKernelVector rho w i = w (rho.symm i) := rfl

@[simp] theorem sourceCoordinateKernelVector_zero
    {R : Type*} [Zero R]
    (rho : Equiv.Perm (Fin 4)) :
    sourceCoordinateKernelVector rho (0 : Fin 4 → R) = 0 := by
  funext i
  simp [sourceCoordinateKernelVector]

/-- Reindexing by a permutation loses no vector information. -/
theorem sourceCoordinateKernelVector_injective
    {R : Type*}
    (rho : Equiv.Perm (Fin 4)) :
    Function.Injective (sourceCoordinateKernelVector (R := R) rho) := by
  intro u v huv
  funext i
  have hi := congrFun huv (rho i)
  simpa [sourceCoordinateKernelVector] using hi

/-- If the simultaneously row/column-permuted matrix kills `w`, then the
original matrix kills the source-coordinate vector `w ∘ rho.symm`.

This is exactly `comp_equiv_symm_dotProduct` row-by-row. -/
theorem mulVec_sourceCoordinateKernelVector_eq_zero
    {R : Type*} [CommRing R]
    (rho : Equiv.Perm (Fin 4))
    (M : Matrix (Fin 4) (Fin 4) R)
    (w : Fin 4 → R)
    (hker :
      Matrix.mulVec (fun i j => M (rho i) (rho j)) w = 0) :
    M.mulVec (sourceCoordinateKernelVector rho w) = 0 := by
  funext i
  have hi := congrFun hker (rho.symm i)
  change
    (fun j => M (rho (rho.symm i)) (rho j)) ⬝ᵥ w = 0 at hi
  simp only [Equiv.apply_symm_apply] at hi
  change
    (fun j => M i j) ⬝ᵥ (w ∘ rho.symm) = 0
  rw [← comp_equiv_symm_dotProduct
    (fun j => M i j) w rho.symm]
  simpa [Function.comp_def] using hi

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The B6 coordinate four-block is exactly the honest special-fibre Hessian
with both matrix indices reindexed by the retained permutation. -/
theorem coordinateSpecialFourBlock_matrix_eq_sourceHessian_reindexed
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.coordinateSpecialFourBlock.matrix =
      fun i j =>
        HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber C.family)
          (C.chartData.chart.rho i)
          (C.chartData.chart.rho j) := by
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  have hspecial :
      polynomialFamilySpecialFiber C.family = G := by
    simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family, G] using
      B.aligned.endpoint.rightRecenteredFamily_specialFiber
  rw [hspecial]
  have hsymm :
      ∀ i j : Fin 4,
        HC4.Polynomial.hessian G
            (C.chartData.chart.rho i) (C.chartData.chart.rho j) =
          HC4.Polynomial.hessian G
            (C.chartData.chart.rho j) (C.chartData.chart.rho i) := by
    intro i j
    simp only [HC4.Polynomial.hessian_apply]
    exact pderiv_comm_commRing _ _ _
  unfold coordinateSpecialFourBlock
  simpa [adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock, G] using
    GeneralFourBlock.matrix_ofSymmetricMatrix
      (fun i j =>
        HC4.Polynomial.hessian G
          (C.chartData.chart.rho i) (C.chartData.chart.rho j)) hsymm

/-- Nonzero polynomial Hessian-kernel data in the literal coordinates of the
honest special fibre used by the Stage-4B first-key filtration. -/
structure SourceCoordinateSpecialKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  vector : Fin 4 → MvPolynomial (Fin 4) K
  vector_ne_zero : vector ≠ 0
  kernel :
    (HC4.Polynomial.hessian
      (polynomialFamilySpecialFiber C.family)).mulVec vector = 0

namespace CoordinateSpecialKernelData

/-- Remove the final retained coordinate permutation from a B6 kernel.
Nothing is renamed in the coefficient polynomials: only vector indices are
returned to the source coordinates. -/
noncomputable def toSourceCoordinateSpecialKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : C.CoordinateSpecialKernelData) :
    C.SourceCoordinateSpecialKernelData := by
  let rho := C.chartData.chart.rho
  let H := HC4.Polynomial.hessian
    (polynomialFamilySpecialFiber C.family)
  let w := sourceCoordinateKernelVector rho D.vector
  refine {
    vector := w
    vector_ne_zero := ?_
    kernel := ?_
  }
  · intro hw
    apply D.vector_ne_zero
    apply sourceCoordinateKernelVector_injective (R := MvPolynomial (Fin 4) K) rho
    simpa [w] using hw
  · have hker := D.kernel
    rw [C.coordinateSpecialFourBlock_matrix_eq_sourceHessian_reindexed] at hker
    exact
      mulVec_sourceCoordinateKernelVector_eq_zero
        rho H D.vector hker

end CoordinateSpecialKernelData

/-- Every early-Schur carrier now has a nonzero polynomial kernel of the
literal honest special-fibre Hessian, with all swap/shear/permutation chart
bookkeeping removed. -/
theorem exists_sourceCoordinateSpecialKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    Nonempty C.SourceCoordinateSpecialKernelData := by
  rcases C.exists_coordinateSpecialKernelData with ⟨D⟩
  exact ⟨D.toSourceCoordinateSpecialKernelData⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
