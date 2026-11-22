import HC4.Polynomial.RankThreeCubicDetOneKernelLinePrincipalPivot
import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib.Tactic

/-!
# Determinant-one source: the true quadratic transverse origin block
# has a principal two-by-two Schur pivot

The previously proved source Hessian kernel-line theorem says that
any nonzero vector w0 in the true quadratic transverse Hessian kernel
at (x=a,y=0) spans that kernel.

Symmetry of the Hessian is automatic from equality of mixed
partial derivatives. The general kernel-line principal-pivot lemma
therefore supplies an actual nonzero diagonal adjugate entry.

The chart is in the ORIGINAL source coordinates, with no arbitrary
change of variables or extra endpoint assumptions.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- In the determinant-one source, a known nonzero quadratic
transverse origin kernel yields a nonzero principal cofactor
of the original quadratic source Hessian. -/
theorem sourceCubic_detOne_originQuadraticKernel_principalCofactor
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w0 : Fin 3 → K) (hw0 : w0 ≠ 0)
    (hTker : ∀ i : Fin 3,
      (∑ j : Fin 3,
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (referenceSlice a
            (hessian (initialForm transverseCubicWeight 2 F)
              (.inr i) (.inr j)))) * w0 j) = 0) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    ∃ k : Fin 3, T.adjugate k k ≠ 0 := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  obtain ⟨_, hline⟩ :=
    sourceCubic_detOne_originQuadraticKernel_isLine
      F a hcap hdetOne w0 hw0 hTker
  have hTw : T *ᵥ w0 = 0 := by
    funext i
    have hi := hTker i
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hi
  have hsourceSym : (sourceTransverseHessian a L2).IsSymm :=
    sourceTransverseHessian_isSymm a L2
  have hSym : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hij := hsourceSym.apply i j
    exact congrArg
      (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) hij
  exact symmetricThree_kernelLine_exists_principalCofactor
    T hSym w0 hw0 hTw hline

end
end HC4.Polynomial.RankThreeCubic
