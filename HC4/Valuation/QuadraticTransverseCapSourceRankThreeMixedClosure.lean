import HC4.Valuation.QuadraticTransverseCapRankThreeMixedProductODE
import HC4.Valuation.QuadraticTransverseCapSourceMarkedCollision
import Mathlib.Tactic

/-!
# Source-honest quadratic-cap rank-three marked-collision contradiction

The determinant-one source supplies polynomial Riccati identities for
its transverse Hessian C and its transverse-linear coefficient b.
The rational-to-polynomial source theorem gives a polynomial inverse
M of C.  The matrix Riccati identity makes M affine, and the linear
source Riccati equation gives (M b)''=0.  Since the *actual* source
has b(0)=b(1), the affine-vector collision theorem makes b'=0.

Finally, the source-level longitudinal Hessian identity and the
original marked gradient collision contradict det Hess(F)=1.

No additional Riccati, derivation, nilpotence, endpoint producer,
or zero-mixed-derivative hypotheses occur in the final theorem.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
variable {K : Type*} [Field K] [CharZero K]

/-- Cancel the nonzero transverse determinant in the *actual*
linear matrix Riccati equation after inserting a two-sided
polynomial inverse.  This is a purely algebraic polynomial
matrix/vector identity. -/
theorem quadraticTransverse_clearedLinearRiccati_polynomialInverse
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hMC : M * C = 1)
    (hdet : C.det ≠ 0)
    (b : Fin 3 → Polynomial K)
    (hlinear : ∀ i : Fin 3,
      C.det *
          (quadraticTransverse_polynomialVectorDerivative
            (quadraticTransverse_polynomialVectorDerivative b)) i =
        2 * ((quadraticTransverse_polynomialMatrixDerivative C *
          C.adjugate).mulVec
            (quadraticTransverse_polynomialVectorDerivative b)) i) :
    let P := quadraticTransverse_polynomialMatrixDerivative C
    let v := quadraticTransverse_polynomialVectorDerivative b
    quadraticTransverse_polynomialVectorDerivative v =
      (P * M).mulVec v + (P * M).mulVec v := by
  dsimp only
  let δ := quadraticTransverse_polynomialVectorDerivative (K := K)
  let P := quadraticTransverse_polynomialMatrixDerivative C
  let v := δ b
  have hAdj : C.adjugate = C.det • M := by
    calc
      C.adjugate = (M * C) * C.adjugate := by rw [hMC, one_mul]
      _ = M * (C * C.adjugate) := by rw [mul_assoc]
      _ = M * (C.det • 1) := by rw [Matrix.mul_adjugate]
      _ = C.det • M := by simp
  have hpoint (i : Fin 3) :
      C.det * (δ v i) = C.det * (2 * ((P * M).mulVec v i)) := by
    have hi := hlinear i
    change C.det * (δ v i) = 2 * ((P * C.adjugate).mulVec v i) at hi
    rw [hAdj, Matrix.mul_smul, Matrix.smul_mulVec] at hi
    have hi' :
        C.det * (δ v i) =
          2 * (C.det * ((P * M).mulVec v i)) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hi
    calc
      C.det * (δ v i) =
          2 * (C.det * ((P * M).mulVec v i)) := hi'
      _ = C.det * (2 * ((P * M).mulVec v i)) := by ring
  funext i
  change (δ v i) =
    ((P * M).mulVec v i) + ((P * M).mulVec v i)
  have hi := mul_left_cancel₀ hdet (hpoint i)
  rw [hi]
  ring

/-- **Rank-three quadratic-cap source: mixed coefficients are constant.**

The only hypotheses are the quadratic transverse cap, the
determinant-one Hessian, nonzero source transverse determinant, and
the actual marked gradient collision. -/
theorem quadraticTransverseCap_two_rankThree_sourceMixedDerivative_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hHessDet : HC4.Polynomial.hessianDeterminant F = 1)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    ∀ i : Fin 3,
      Polynomial.derivative
        (quadraticTransverseCapSourceLinearCoefficients F i) = 0 := by
  let G := quadraticTransverseCapSourceAxisThreeBlock F
  let C := G.matrix
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let δ := quadraticTransverse_polynomialVectorDerivative (K := K)
  let D := quadraticTransverse_polynomialMatrixDerivative (K := K)
  let P := D C
  obtain ⟨M, hCM, hMC, d, hd, hconst⟩ :=
    quadraticTransverseCap_two_source_constantDet
      F hbound hHessDet hCdet
  have hcleared :
      C.det • D (D C) =
        2 • (D C * C.adjugate * D C) := by
    simpa only [C, G, D, GeneralThreeBlock.matrix_det] using
      (quadraticTransverseCap_two_sourceRiccati_matrixCleared
        F hbound hHessDet)
  obtain ⟨A, B, hAB⟩ :=
    quadraticTransverse_polynomialInverse_affine_of_clearedRiccati
      C M hCM hMC hcleared
  have hMsecond : D (D M) = 0 := by
    apply Matrix.ext
    intro i j
    change Polynomial.derivative (Polynomial.derivative (M i j)) = 0
    rw [hAB i j]
    simp [Polynomial.derivative_mul]
  have hMprime : D M = -(M * P * M) :=
    quadraticTransverse_polynomialInverse_derivative C M hCM hMC
  have hdet : C.det ≠ 0 := by
    rw [GeneralThreeBlock.matrix_det]
    exact hCdet
  have hlinear : ∀ i : Fin 3,
      C.det * (δ (δ b)) i =
        2 * ((P * C.adjugate).mulVec (δ b)) i := by
    simpa only [C, G, b, δ, D, P] using
      (quadraticTransverseCap_two_sourceRiccati_linearMatrixCleared
        F hbound hHessDet)
  have hlinear' :
      δ (δ b) = (P * M).mulVec (δ b) + (P * M).mulVec (δ b) :=
    quadraticTransverse_clearedLinearRiccati_polynomialInverse
      C M hMC hdet b hlinear
  have hMbsecond :
      ∀ i : Fin 3,
        Polynomial.derivative (Polynomial.derivative (M.mulVec b i)) = 0 :=
    quadraticTransverse_affineInverse_linearODE_productSecond_zero
      M P b hMsecond hMprime hlinear'
  have hMsecondEntries : ∀ i j : Fin 3,
      Polynomial.derivative (Polynomial.derivative (M i j)) = 0 := by
    intro i j
    have h := congrArg
      (fun Z : Matrix (Fin 3) (Fin 3) (Polynomial K) => Z i j) hMsecond
    simpa [D, quadraticTransverse_polynomialMatrixDerivative,
      Matrix.zero_apply] using h
  have hcollb :
      ∀ i : Fin 3,
        Polynomial.eval (1 : K) (b i) = Polynomial.eval (0 : K) (b i) := by
    intro i
    exact longitudinalCoefficient_single_eval_one_eq_eval_zero_of_collision
      i F hcoll
  exact quadraticTransverse_affineMatrixVector_markedCollision_zero
    C M hCM b hMsecondEntries hMbsecond hcollb

/-- **Source-level rank-three quadratic transverse cap is impossible
under the exact marked gradient collision.**

No rank-three Riccati, polynomial inverse, affine slope, or mixed
coefficient rigidity is assumed: each is derived from the actual
determinant-one source. -/
theorem quadraticTransverseCap_two_rankThree_source_impossible
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hHessDet : HC4.Polynomial.hessianDeterminant F = 1)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    False := by
  obtain ⟨_M, _hCM, _hMC, d, hd, hconst⟩ :=
    quadraticTransverseCap_two_source_constantDet
      F hbound hHessDet hCdet
  have hzero :=
    quadraticTransverseCap_two_rankThree_sourceMixedDerivative_zero
      F hbound hHessDet hCdet hcoll
  exact quadraticTransverseCap_two_rankThree_constantDetZeroMixed_impossible
    F hHessDet d hd hconst hzero hcoll

end
end HC4.Valuation
