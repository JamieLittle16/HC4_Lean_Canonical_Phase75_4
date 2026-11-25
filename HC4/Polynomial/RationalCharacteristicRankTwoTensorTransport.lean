import HC4.Polynomial.RationalCharacteristicRankTwoFrame

/-!
# Tensor transport to the rational Jordan frame

Transport the *already differentiated* equations by similarity
and congruence. The coefficients of the frame are contracted into
the derivative slot, not differentiated. Consequently there are
no connection terms and no need to assume a constant frame.

The resulting pointwise identities include vanishing of the whole
first column of the velocity derivative in the first Jordan
direction. This is the tensor input to straightness of the
one-dimensional velocity kernel.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Algebra

variable {F : Type*} [Field F]

private abbrev Mat (F : Type*) := Matrix (Fin 3) (Fin 3) F

/-- Contract the input slots of a three-index tensor and transform
its remaining slot by an arbitrary matrix. -/
def rankTwo_transportTensor
    (A M : Mat F) (T : Fin 3 → Mat F) (l : Fin 3) : Mat F :=
  A * (∑ k : Fin 3, M k l • T k) * M

/-- Symmetry in the input slots is tensorial, even for a frame with
coefficients in the rational function field. -/
theorem rankTwo_transportTensor_symm
    (A M : Mat F) (T : Fin 3 → Mat F)
    (h : ∀ i j l : Fin 3, T l i j = T j i l) (i j l : Fin 3) :
    rankTwo_transportTensor A M T l i j =
      rankTwo_transportTensor A M T j i l := by
  classical
  simp only [rankTwo_transportTensor, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  simp only [h 0 0 1, h 0 0 2, h 0 1 2,
    h 1 0 1, h 1 0 2, h 1 1 2,
    h 2 0 1, h 2 0 2, h 2 1 2]
  ring

/-- The intertwining relation also transports operators on the left
through the inverse frame. -/
theorem rankTwo_frame_left_intertwine
    (N M P J : Mat F) (hMP : M * P = 1) (hPM : P * M = 1)
    (hNM : N * M = M * J) : P * N = J * P := by
  calc
    P * N = P * (N * M) * P := by
      rw [← Matrix.mul_assoc P N M, Matrix.mul_assoc (P * N) M P, hMP, mul_one]
    _ = J * P := by
      rw [hNM, ← Matrix.mul_assoc P M J, hPM, one_mul]

/-- The differentiated nilpotence equation is equivariant under
pointwise similarity. -/
theorem rankTwo_transport_cubeDerivative
    (N M P J R : Mat F)
    (hMP : M * P = 1) (hPM : P * M = 1) (hNM : N * M = M * J)
    (h : (N * N) * R + N * R * N + R * (N * N) = 0) :
    (J * J) * (P * R * M) + J * (P * R * M) * J +
      (P * R * M) * (J * J) = 0 := by
  have hp := rankTwo_frame_left_intertwine N M P J hMP hPM hNM
  have h1 : (J * J) * (P * R * M) = P * ((N * N) * R) * M := by
    calc
      _ = J * (J * P) * R * M := by noncomm_ring
      _ = J * (P * N) * R * M := by rw [← hp]
      _ = (J * P) * N * R * M := by noncomm_ring
      _ = _ := by rw [← hp]; noncomm_ring
  have h2 : J * (P * R * M) * J = P * (N * R * N) * M := by
    calc
      _ = (J * P) * R * (M * J) := by noncomm_ring
      _ = _ := by rw [← hp, ← hNM]; noncomm_ring
  have h3 : (P * R * M) * (J * J) = P * (R * (N * N)) * M := by
    calc
      _ = P * R * (M * J) * J := by noncomm_ring
      _ = P * R * (N * M) * J := by rw [← hNM]
      _ = P * R * N * (M * J) := by noncomm_ring
      _ = _ := by rw [← hNM]; noncomm_ring
  rw [h1, h2, h3, ← Matrix.add_mul, ← Matrix.add_mul,
    ← Matrix.mul_add, ← Matrix.mul_add, h, Matrix.mul_zero, Matrix.zero_mul]

/-- Differentiated self-adjointness is transported by congruence. -/
theorem rankTwo_transport_selfAdjointDerivative
    (N H M P J R Q : Mat F) (hMP : M * P = 1)
    (hNM : N * M = M * J)
    (h : (Q * N + H * R).transpose = Q * N + H * R) :
    ((M.transpose * Q * M) * J +
      (M.transpose * H * M) * (P * R * M)).transpose =
      (M.transpose * Q * M) * J +
      (M.transpose * H * M) * (P * R * M) := by
  have he : (M.transpose * Q * M) * J +
      (M.transpose * H * M) * (P * R * M) =
      M.transpose * (Q * N + H * R) * M := by
    have h1 : (M.transpose * Q * M) * J = M.transpose * (Q * N) * M := by
      calc
        _ = M.transpose * Q * (M * J) := by noncomm_ring
        _ = _ := by rw [← hNM]; noncomm_ring
    have h2 : (M.transpose * H * M) * (P * R * M) =
        M.transpose * (H * R) * M := by
      calc
        _ = M.transpose * H * (M * P) * R * M := by noncomm_ring
        _ = _ := by rw [hMP, mul_one]; noncomm_ring
    rw [h1, h2, Matrix.mul_add, Matrix.add_mul]
  rw [he, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h]
  simp only [Matrix.mul_assoc]

end Algebra

section Source

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- A directional matrix derivative is the contraction of the
original partial derivative tensor. -/
theorem rankTwo_matrixDeriv_directional
    (w : Fin 3 → E K) (A : Matrix (Fin 3) (Fin 3) (E K)) :
    rankTwo_matrixDeriv (rankTwo_directionalDerivation w) A =
      ∑ k : Fin 3, w k • rankTwo_matrixDeriv (rationalCharacteristicPartial k) A := by
  apply Matrix.ext
  intro i j
  simp only [rankTwo_matrixDeriv, rankTwo_directionalDerivation_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The actual source supplies the transported Frobenius tensor,
including the stronger vanishing in the first Jordan direction. -/
theorem rankTwo_source_frameTensor
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ M P : Matrix (Fin 3) (Fin 3) (E K), M.det ≠ 0 ∧
      M * P = 1 ∧ P * M = 1 ∧
      rationalCharacteristicJacobian V * M = M * rankTwo_jordanBlock ∧
      (∀ i : Fin 3, (P * rankTwo_matrixDeriv
        (rankTwo_directionalDerivation (fun k => M k 0))
        (rationalCharacteristicJacobian V) * M) i 0 = 0) ∧
      (P * rankTwo_matrixDeriv
        (rankTwo_directionalDerivation (fun k => M k 1))
        (rationalCharacteristicJacobian V) * M) 2 1 = 0 := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := rationalCharacteristicHessian a L
  let J : Matrix (Fin 3) (Fin 3) (E K) := rankTwo_jordanBlock
  have h3 : N ^ 3 = 0 :=
    rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg (fun i => hgrad (.inr i))
  have hself : N.transpose * H = H * N :=
    rationalCharacteristicJacobian_selfAdjoint a L V hV (fun i => hgrad (.inr i))
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    change MvPolynomial.aeval (transverseGenericPoint a)
      (pderiv (.inr i) (pderiv (.inr j) L)) =
      MvPolynomial.aeval (transverseGenericPoint a)
        (pderiv (.inr j) (pderiv (.inr i) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have hminor : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h ⟨a, i, b, j, hz⟩
  obtain ⟨_, h2, _, hleft, _⟩ := rankTwo_square_frontier N h3 hminor
  obtain ⟨M, P, hd, hMP, hPM, hNM⟩ := rankTwo_exists_jordanFrame N hleft h2
  let G := M.transpose * H * M
  let D (l : Fin 3) := rankTwo_directionalDerivation (fun k => M k l)
  let U (l : Fin 3) := P * rankTwo_matrixDeriv (D l) N * M
  let T (l : Fin 3) := M.transpose * rankTwo_matrixDeriv (D l) H * M
  have hG : G.transpose = G := by
    change (M.transpose * H * M).transpose = M.transpose * H * M
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hH, Matrix.mul_assoc]
  have hJG : J.transpose * G = G * J := by
    have he : P * N * M = J := by
      rw [Matrix.mul_assoc, hNM, ← Matrix.mul_assoc, hPM, one_mul]
    have h := rationalAffine_similarity_selfAdjoint M P N H hMP hself
    rw [he] at h
    exact h
  have hform := rankTwo_jordan_hessian_form G hG hJG
  have hGdet : G.det ≠ 0 := by
    change (M.transpose * H * M).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hd
      (rationalCharacteristicHessian_det_ne_zero a L hreg)) hd
  have ha : G 0 2 ≠ 0 := by
    intro hz
    apply hGdet
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (E K) => A 0 j) hform
    fin_cases j <;> simpa [hz] using he
  have hUs (i j l : Fin 3) : U l i j = U j i l := by
    change (P * rankTwo_matrixDeriv (D l) N * M) i j =
      (P * rankTwo_matrixDeriv (D j) N * M) i l
    rw [rankTwo_matrixDeriv_directional, rankTwo_matrixDeriv_directional]
    exact rankTwo_transportTensor_symm P M
      (fun k => rankTwo_matrixDeriv (rationalCharacteristicPartial k) N)
      (rankTwo_velocityTensor_symm V) i j l
  have hTs (i j l : Fin 3) : T l i j = T j i l := by
    change (M.transpose * rankTwo_matrixDeriv (D l) H * M) i j =
      (M.transpose * rankTwo_matrixDeriv (D j) H * M) i l
    rw [rankTwo_matrixDeriv_directional, rankTwo_matrixDeriv_directional]
    apply rankTwo_transportTensor_symm
    intro i j l
    change rankTwo_matrixDeriv (rationalCharacteristicPartial l) H i j =
      rankTwo_matrixDeriv (rationalCharacteristicPartial j) H i l
    change rankTwo_matrixDeriv (rationalCharacteristicPartial l)
        (rationalCharacteristicHessian a L) i j =
      rankTwo_matrixDeriv (rationalCharacteristicPartial j)
        (rationalCharacteristicHessian a L) i l
    rw [rationalCharacteristicHessian_eq_slice_hessian]
    exact rankTwo_hessianTensor_symm (referenceSlice a L) i j l
  have hU3 (l : Fin 3) : (J * J) * U l + J * U l * J + U l * (J * J) = 0 :=
    rankTwo_transport_cubeDerivative N M P J _ hMP hPM hNM
      (rankTwo_cubeDerivative (D l) N h3)
  have hHN : (H * N).transpose = H * N := by
    rw [Matrix.transpose_mul, hH, hself]
  have hUT (l : Fin 3) : (T l * J + G * U l).transpose = T l * J + G * U l :=
    rankTwo_transport_selfAdjointDerivative N H M P J _ _ hMP hNM
      (rankTwo_selfAdjointDerivative (D l) H N hHN)
  have hz : U 1 2 1 = 0 := by
    apply rankTwo_jordan_frobenius_tensor (G 0 2) (G 1 2) (G 2 2) ha U T
      hUs hTs hU3
    intro l
    have h := hUT l
    rw [hform] at h
    exact h
  have hc0 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).1
  have hc1 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).2.1
  have hc2 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).2.2
  have h01 : U 0 2 1 = 0 := (hUs 2 1 0).trans (hc0 1)
  have h02 : U 0 2 2 = 0 := (hUs 2 2 0).trans (hc0 2)
  have h10 : U 0 1 0 = 0 := by
    have h := hc1 0
    rw [h01, zero_add] at h
    exact h
  have h11 : U 0 1 1 = 0 := by
    have h := hc1 1
    rw [hz, zero_add] at h
    exact (hUs 1 1 0).trans h
  have h00 : U 0 0 0 = 0 := by
    have h := hc2 0
    rw [h02, h11, zero_add, zero_add] at h
    exact h
  refine ⟨M, P, hd, hMP, hPM, hNM, ?_, hz⟩
  intro i
  change U 0 i 0 = 0
  fin_cases i
  · exact h00
  · exact h10
  · exact hc0 0

end Source
end
end HC4.Polynomial.RankThreeCubic
