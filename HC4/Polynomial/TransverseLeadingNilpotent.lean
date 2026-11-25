import HC4.Polynomial.TransverseLeadingFixedPower
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import HC4.Polynomial.RankThreeCubicPoleJacobiBridge
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.ParameterGapSecondJet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import Mathlib.Tactic
import HC4.Polynomial.TransverseLeadingSchurFoundation
import HC4.Polynomial.TransverseLeadingStationary

/-!
# Nilpotent transverse characteristic transport and inverse coordinates

The actual source Hessian kernel, self-adjointness, gradient evolution,
longitudinal support bounds, and polynomial inverse shear. Includes the
first lower-grade affine formula; later Schur corrections are downstream.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton HC4.Valuation
open scoped BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [CharZero K]

open MvPolynomial

private abbrev StationarySource (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

private abbrev StationaryExponent := (Unit ⊕ Fin 3) →₀ ℕ

/-! ## Pull the nilpotent characteristic back to the actual source

The inverse shear is polynomial. In the original coordinates the
characteristic velocity is (1, Ny-(x-a)N²y). Its Hessian kernel is
an exact source polynomial identity; it is not a claim that the
shear preserves the Hessian determinant of the full source.
-/

/-- The transverse linear vector associated to a constant matrix. -/
def sourceLinearVector (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    StationarySource K :=
  ∑ j : Fin 3, MvPolynomial.C (M i j) * X (.inr j)

def referenceLinearVector (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    MvPolynomial (Fin 3) K :=
  ∑ j : Fin 3, MvPolynomial.C (M i j) * X j

/-- Linear matrix forms transform by the actual characteristic pencil. -/
theorem linearLineEval_sourceLinearVector
    (a : K) (M N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    linearLineEval a N (sourceLinearVector M i) =
      _root_.Polynomial.C (referenceLinearVector M i) +
        _root_.Polynomial.C (referenceLinearVector (M * N) i) *
          _root_.Polynomial.X := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hC (c : K) :
      linearLineEval a N (MvPolynomial.C c) =
        _root_.Polynomial.C (MvPolynomial.C c) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have hX (j : Fin 3) :
      linearLineEval a N (X (.inr j)) =
        _root_.Polynomial.C (X j : B) +
        _root_.Polynomial.C (referenceLinearVector N j) * _root_.Polynomial.X := by
    simp [linearLineEval, lineEval, referenceLinearVector]
  have hprod :
      (∑ j : Fin 3, MvPolynomial.C (M i j) * referenceLinearVector N j) =
        referenceLinearVector (M * N) i := by
    unfold referenceLinearVector
    calc
      _ = ∑ j : Fin 3, ∑ k : Fin 3,
          MvPolynomial.C (M i j * N j k) * (X k : B) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← mul_assoc, ← map_mul]
      _ = ∑ k : Fin 3, ∑ j : Fin 3,
          MvPolynomial.C (M i j * N j k) * (X k : B) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_mul, Matrix.mul_apply, map_sum]
  calc
    _ = ∑ j : Fin 3, _root_.Polynomial.C (MvPolynomial.C (M i j)) *
        (_root_.Polynomial.C (X j : B) +
          _root_.Polynomial.C (referenceLinearVector N j) * _root_.Polynomial.X) := by
        simp only [sourceLinearVector, map_sum, map_mul, hC, hX]
    _ = _root_.Polynomial.C (referenceLinearVector M i) +
        _root_.Polynomial.C
          (∑ j : Fin 3, MvPolynomial.C (M i j) * referenceLinearVector N j) *
            _root_.Polynomial.X := by
        simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← map_mul, ← map_sum, referenceLinearVector]
    _ = _ := by rw [hprod]

/-- The source velocity of a nilpotent straight characteristic. -/
def sourceNilpotentVelocity (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (i : Fin 3) : StationarySource K :=
  sourceLinearVector N i -
    (X (.inl ()) - MvPolynomial.C a) * sourceLinearVector (N ^ 2) i

theorem linearLineEval_sourceNilpotentVelocity
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (i : Fin 3) :
    linearLineEval a N (sourceNilpotentVelocity a N i) =
      _root_.Polynomial.C (referenceLinearVector N i) := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hx : linearLineEval a N (X (.inl ()) - MvPolynomial.C a) =
      (_root_.Polynomial.X : _root_.Polynomial B) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have h2 : N * N = N ^ 2 := (pow_two N).symm
  have h3 : N ^ 2 * N = 0 := by rw [← pow_succ, hN]
  have hz : referenceLinearVector (0 : Matrix (Fin 3) (Fin 3) K) i = 0 := by
    simp [referenceLinearVector]
  rw [sourceNilpotentVelocity, map_sub, map_mul, hx,
    linearLineEval_sourceLinearVector, linearLineEval_sourceLinearVector, h2, h3, hz,
    map_zero, zero_mul, add_zero]
  ring

/-- The exact gradient-transport identity gives a polynomial kernel
equation in the ORIGINAL source, simultaneously for all gradient
components. This is a first-order system with no rational denominators. -/
theorem sourceNilpotent_gradient_kernel
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    ∀ i : Unit ⊕ Fin 3,
      pderiv (.inl ()) (pderiv i L) +
        ∑ j : Fin 3, sourceNilpotentVelocity a N j * pderiv (.inr j) (pderiv i L) = 0 := by
  classical
  intro i
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  have he : lineEval (K := K) z V = linearLineEval a N := rfl
  have h := transverse_lineEval_derivative z V (pderiv i L)
  rw [he, hgrad i, _root_.Polynomial.derivative_C] at h
  have h' : linearLineEval a N (pderiv (.inl ()) (pderiv i L)) +
      ∑ j : Fin 3, _root_.Polynomial.C (referenceLinearVector N j) *
        linearLineEval a N (pderiv (.inr j) (pderiv i L)) = 0 := by
    simpa [Fintype.sum_sum_type, V] using h.symm
  apply linearLineEval_injective_of_cube_zero a N hN
  simp only [map_add, map_sum, map_mul, linearLineEval_sourceNilpotentVelocity a N hN,
    map_zero]
  exact h'




/-! ## Source-wide self-adjointness and nilpotent gradient evolution

The differentiated transport equation T(I+tN)=M, with both Hessians
symmetric, makes TN symmetric at EVERY characteristic time (not only
at the reference slice). Injective pullback gives the same identity
on the original leading source. Euler homogeneity then turns the
source kernel equation into a nilpotent matrix ODE for its transverse
gradient. Neither identity asserts that the full source Hessian is
preserved by the nonlinear characteristic substitution.
-/

/-- Self-adjointness at all characteristic times, pulled back to
the actual source transverse Hessian. -/
theorem sourceNilpotent_hessian_selfAdjoint
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let A := N.map MvPolynomial.C
    (H * A).transpose = H * A := by
  classical
  let B := MvPolynomial (Fin 3) K
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  let C := (N.map (MvPolynomial.C : K →+* B)).map _root_.Polynomial.C
  have hT (i j : Fin 3) : T i j = T j i := by
    change linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) L)) =
      linearLineEval a N (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have hM (i j : Fin 3) : M i j = M j i := by
    change referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L)) =
      referenceSlice a (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have ht := transverseHessian_transport_of_linear_gradient a N L hgrad
  change T * (1 + (_root_.Polynomial.X : _root_.Polynomial B) • C) =
    M.map _root_.Polynomial.C at ht
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at ht
  have he (i j : Fin 3) :
      T i j + (_root_.Polynomial.X : _root_.Polynomial B) * (T * C) i j =
        _root_.Polynomial.C (M i j) := by
    have h := congrArg (fun Q : Matrix (Fin 3) (Fin 3) (_root_.Polynomial B) =>
      Q i j) ht
    exact h
  have hTC (i j : Fin 3) : (T * C) i j = (T * C) j i := by
    apply mul_left_cancel₀ (_root_.Polynomial.X_ne_zero (R := B))
    have h₁ := he i j
    rw [hT i j, hM i j] at h₁
    exact add_left_cancel (h₁.trans (he j i).symm)
  have hc (r : K) : linearLineEval a N (MvPolynomial.C r) =
      _root_.Polynomial.C (MvPolynomial.C r) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have hmap (i j : Fin 3) :
      linearLineEval a N ((H * A) i j) = (T * C) i j := by
    simp only [Matrix.mul_apply, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    change linearLineEval a N (H i k) * linearLineEval a N (MvPolynomial.C (N k j)) =
      linearLineEval a N (H i k) * _root_.Polynomial.C (MvPolynomial.C (N k j))
    rw [hc]
  change (H * A).transpose = H * A
  apply Matrix.ext
  intro i j
  change (H * A) j i = (H * A) i j
  apply linearLineEval_injective_of_cube_zero a N hN
  rw [hmap, hmap]
  exact hTC j i

/-- Transverse Euler identity before any longitudinal specialization. -/
theorem sourceTransverseEuler_of_weight
    (P : StationarySource K) (n : ℕ)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    (∑ j : Fin 3, X (.inr j) * pderiv (.inr j) P) =
      (n : StationarySource K) * P := by
  classical
  have hnat : P.IsWeightedHomogeneous transverseCubicNatWeight n := by
    intro d hd
    have he : ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) =
        Finsupp.weight transverseCubicWeight d := by
      simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases i with
      | inl u => cases u; simp [transverseCubicNatWeight, transverseCubicWeight]
      | inr j => simp [transverseCubicNatWeight, transverseCubicWeight, nsmul_eq_mul]
    have hh := hP hd
    rw [← he] at hh
    exact_mod_cast hh
  have h := hnat.sum_weight_X_mul_pderiv
  simpa [transverseCubicNatWeight, Fintype.sum_sum_type, nsmul_eq_mul] using h

/-- Euler's identity in Hessian-vector form. Explicit entrywise
rewriting avoids reducing the matrix multiplication implementation
during definitional equality checking. -/
theorem sourceTransverseHessian_mulVec_coordinates
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1)) :
    (hessian L).submatrix Sum.inr Sum.inr *ᵥ
      (fun j : Fin 3 => X (Sum.inr j)) =
      (n : StationarySource K) • (fun i : Fin 3 => pderiv (Sum.inr i) L) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hessian_apply,
    Pi.smul_apply, smul_eq_mul]
  have hp := pderiv_isWeightedHomogeneous hL (Sum.inr i)
  have hp' : (pderiv (Sum.inr i) L).IsWeightedHomogeneous
      transverseCubicWeight (n : ℤ) := by
    simpa [transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight (K := K) (pderiv (Sum.inr i) L) n hp'
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The matrix step of the gradient ODE is independent of the
polynomial ring. Keep its elaboration over an abstract ring rather
than unfolding the concrete multivariate polynomial arithmetic. -/
private theorem sourceNilpotent_gradient_ode_algebra
    {R : Type*} [CommRing R]
    (A H : Matrix (Fin 3) (Fin 3) R)
    (G Y W D : Fin 3 → R) (t c : R)
    (hcomm : A.transpose * H = H * A)
    (hE : H *ᵥ Y = c • G)
    (hW : W = A *ᵥ Y - t • ((A ^ 2) *ᵥ Y))
    (hk : D + H *ᵥ W = 0) :
    D = -c • (A.transpose *ᵥ G - t • ((A.transpose ^ 2) *ᵥ G)) := by
  have hcomm2 : H * A ^ 2 = A.transpose ^ 2 * H := by
    calc
      _ = (H * A) * A := by rw [pow_two, Matrix.mul_assoc]
      _ = (A.transpose * H) * A := congrArg (fun M => M * A) hcomm.symm
      _ = A.transpose * (H * A) := Matrix.mul_assoc _ _ _
      _ = A.transpose * (A.transpose * H) :=
        congrArg (fun M => A.transpose * M) hcomm.symm
      _ = _ := by rw [pow_two, Matrix.mul_assoc]
  have h1 : H *ᵥ (A *ᵥ Y) = c • (A.transpose *ᵥ G) := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul]
  have h2 : H *ᵥ ((A ^ 2) *ᵥ Y) = c • (A.transpose ^ 2 *ᵥ G) := by
    rw [Matrix.mulVec_mulVec, hcomm2, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul]
  have hHW : H *ᵥ W = c • (A.transpose *ᵥ G - t • (A.transpose ^ 2 *ᵥ G)) := by
    rw [hW, Matrix.mulVec_sub, Matrix.mulVec_smul, h1, h2]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hHW] at hk
  have hh : D = -(c • (A.transpose *ᵥ G - t • (A.transpose ^ 2 *ᵥ G))) :=
    eq_neg_iff_add_eq_zero.mpr hk
  simpa only [neg_smul] using hh

/-- The transverse gradient obeys an exact first-order nilpotent
matrix evolution at fixed ORIGINAL transverse coordinates.
Here n=m-1 for a leading layer of transverse degree m. -/
theorem sourceNilpotent_transverseGradient_ode
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
    let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
    let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
    (fun i : Fin 3 => pderiv (Sum.inl ()) (G i)) =
      - (n : StationarySource K) •
        (A.transpose *ᵥ G - t • ((A.transpose ^ 2) *ᵥ G)) := by
  classical
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
  let Y : Fin 3 → StationarySource K := fun i => X (.inr i)
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  let W : Fin 3 → StationarySource K := sourceNilpotentVelocity a N
  let D : Fin 3 → StationarySource K := fun i => pderiv (.inl ()) (G i)
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    simp only [H, Matrix.transpose_apply, Matrix.submatrix_apply, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have hcomm : A.transpose * H = H * A := by
    have h := sourceNilpotent_hessian_selfAdjoint a N hN L (fun i => hgrad (.inr i))
    change (H * A).transpose = H * A at h
    rwa [Matrix.transpose_mul, hH] at h
  have hE : H *ᵥ Y = (n : StationarySource K) • G :=
    sourceTransverseHessian_mulVec_coordinates L n hL
  have hA2 : A ^ 2 = (N ^ 2).map (MvPolynomial.C : K →+* StationarySource K) := by
    simp only [A, pow_two, Matrix.map_mul]
  have hW : W = A *ᵥ Y - t • ((A ^ 2) *ᵥ Y) := by
    rw [hA2]
    funext i
    simp only [W, sourceNilpotentVelocity, sourceLinearVector, A, t, Y,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hk : D + H *ᵥ W = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, D, G, H, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, hessian_apply]
    have hi := sourceNilpotent_gradient_kernel a N hN L hgrad (.inr i)
    rw [show (∑ j : Fin 3, pderiv (.inr j) (pderiv (.inr i) L) * W j) =
        ∑ j : Fin 3, W j * pderiv (.inr j) (pderiv (.inr i) L) by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _]
    exact hi
  exact sourceNilpotent_gradient_ode_algebra A H G Y W D t
    (n : StationarySource K) hcomm hE hW hk



/-! ## Uniform longitudinal rigidity in the pole-free branch

Use an abstract derivation on an abstract commutative ring for the
nilpotent ODE calculation. Only the final application knows that the
derivation is the longitudinal partial derivative of the source.
-/

private def nilpotentVectorDeriv {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (v : Fin 3 → R) : Fin 3 → R :=
  fun i => D (v i)

private theorem nilpotentVectorDeriv_sub {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (u v : Fin 3 → R) :
    nilpotentVectorDeriv D (u-v) =
      nilpotentVectorDeriv D u - nilpotentVectorDeriv D v := by
  funext i
  simp [nilpotentVectorDeriv, Pi.sub_apply]

private theorem nilpotentVectorDeriv_smul {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (r : R) (v : Fin 3 → R) :
    nilpotentVectorDeriv D (r • v) =
      D r • v + r • nilpotentVectorDeriv D v := by
  funext i
  simp only [nilpotentVectorDeriv, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Derivation.leibniz]
  ring

private theorem nilpotentVectorDeriv_mulVec {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R)
    (A : Matrix (Fin 3) (Fin 3) R) (hA : ∀ i j, D (A i j) = 0)
    (v : Fin 3 → R) :
    nilpotentVectorDeriv D (A *ᵥ v) = A *ᵥ nilpotentVectorDeriv D v := by
  classical
  funext i
  simp only [nilpotentVectorDeriv, Matrix.mulVec, dotProduct, map_sum,
    Derivation.leibniz, smul_eq_mul, hA, mul_zero, add_zero]

/-- Differentiating a nilpotent ODE twice and three times. This is
independent of the number of polynomial source variables. -/
private theorem nilpotentVectorDeriv_second_third
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, D (A i j) = 0) (h3 : A ^ 3 = 0)
    (c t : R) (hc : D c = 0) (ht : D t = 1) (G : Fin 3 → R)
    (hode : nilpotentVectorDeriv D G =
      -c • (A *ᵥ G - t • (A ^ 2 *ᵥ G))) :
    nilpotentVectorDeriv D (nilpotentVectorDeriv D G) =
      (c * (c+1)) • (A ^ 2 *ᵥ G) ∧
    nilpotentVectorDeriv D (nilpotentVectorDeriv D (nilpotentVectorDeriv D G)) = 0 := by
  classical
  let V := A *ᵥ G
  let W := A ^ 2 *ᵥ G
  have hA2 (i j : Fin 3) : D ((A ^ 2) i j) = 0 := by
    simp only [pow_two, Matrix.mul_apply, map_sum, Derivation.leibniz,
      hA, smul_zero, add_zero, Finset.sum_const_zero]
  have hleft : A * A ^ 2 = 0 := by rw [← pow_succ', h3]
  have hright : A ^ 2 * A = 0 := by rw [← pow_succ, h3]
  have hfour : A ^ 2 * A ^ 2 = 0 := by
    calc
      _ = (A ^ 2 * A) * A := by
        calc
          A ^ 2 * A ^ 2 = A ^ 2 * (A * A) :=
            congrArg (fun M => A ^ 2 * M) (pow_two A)
          _ = _ := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hright, zero_mul]
  have hAV : A *ᵥ V = W := by
    dsimp only [V, W]
    rw [Matrix.mulVec_mulVec, pow_two]
  have hAW : A *ᵥ W = 0 := by
    dsimp only [W]
    rw [Matrix.mulVec_mulVec, hleft, Matrix.zero_mulVec]
  have hA2V : A ^ 2 *ᵥ V = 0 := by
    dsimp only [V]
    rw [Matrix.mulVec_mulVec, hright, Matrix.zero_mulVec]
  have hA2W : A ^ 2 *ᵥ W = 0 := by
    dsimp only [W]
    rw [Matrix.mulVec_mulVec, hfour, Matrix.zero_mulVec]
  change nilpotentVectorDeriv D G = -c • (V - t • W) at hode
  have hV : nilpotentVectorDeriv D V = -c • W := by
    calc
      _ = A *ᵥ nilpotentVectorDeriv D G :=
        nilpotentVectorDeriv_mulVec D A hA G
      _ = _ := by
        rw [hode, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
          hAV, hAW, smul_zero, sub_zero]
  have hW : nilpotentVectorDeriv D W = 0 := by
    calc
      _ = A ^ 2 *ᵥ nilpotentVectorDeriv D G :=
        nilpotentVectorDeriv_mulVec D (A ^ 2) hA2 G
      _ = _ := by
        rw [hode, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
          hA2V, hA2W, smul_zero, sub_zero, smul_zero]
  have hsecond : nilpotentVectorDeriv D (nilpotentVectorDeriv D G) =
      (c * (c+1)) • W := by
    rw [hode, nilpotentVectorDeriv_smul, nilpotentVectorDeriv_sub,
      nilpotentVectorDeriv_smul, hV, hW, ht, map_neg, hc]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  refine ⟨hsecond, ?_⟩
  rw [hsecond, nilpotentVectorDeriv_smul, hW]
  have hcc : D (c * (c+1)) = 0 := by
    simp [Derivation.leibniz, hc]
  rw [hcc, zero_smul, smul_zero, add_zero]

/-- The actual transverse gradient is longitudinally quadratic, and
its second derivative is the explicit last nilpotent power. -/
theorem sourceNilpotent_transverseGradient_second_third
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.transpose.map MvPolynomial.C
    let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
    let c : StationarySource K := n
    (fun i : Fin 3 => pderiv (Sum.inl ()) (pderiv (Sum.inl ()) (G i))) =
      (c * (c+1)) • (A ^ 2 *ᵥ G) ∧
    ∀ i : Fin 3, pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) (G i))) = 0 := by
  classical
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.transpose.map MvPolynomial.C
  let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
  let c : StationarySource K := n
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  let D : Derivation K (StationarySource K) (StationarySource K) := pderiv (.inl ())
  have hA (i j : Fin 3) : D (A i j) = 0 := by
    simp [D, A, Matrix.map_apply, pderiv_C]
  have h3N : N.transpose ^ 3 = 0 := by rw [← Matrix.transpose_pow, hN, Matrix.transpose_zero]
  have h3 : A ^ 3 = 0 := by
    have h : (N.transpose ^ 3).map (MvPolynomial.C : K →+* StationarySource K) =
        (0 : Matrix (Fin 3) (Fin 3) (StationarySource K)) := by
      rw [h3N]
      ext i j
      simp
    have hA2 : A ^ 2 = (N.transpose ^ 2).map
        (MvPolynomial.C : K →+* StationarySource K) := by
      simp only [A, pow_two, Matrix.map_mul]
    calc
      A ^ 3 = A ^ 2 * A := pow_succ A 2
      _ = ((N.transpose ^ 2) * N.transpose).map
          (MvPolynomial.C : K →+* StationarySource K) := by
        rw [hA2, Matrix.map_mul]
      _ = (N.transpose ^ 3).map
          (MvPolynomial.C : K →+* StationarySource K) :=
        congrArg (fun M : Matrix (Fin 3) (Fin 3) K =>
          M.map (MvPolynomial.C : K →+* StationarySource K)) (pow_succ N.transpose 2).symm
      _ = 0 := h
  have hc : D c = 0 := D.map_natCast n
  have ht : D t = 1 := by simp [D, t, pderiv_X]
  have hAT : (N.map (MvPolynomial.C : K →+* StationarySource K)).transpose = A := by
    ext i j
    rfl
  have hode := sourceNilpotent_transverseGradient_ode a N hN L n hL hgrad
  dsimp only at hode
  rw [hAT] at hode
  have hode' : nilpotentVectorDeriv D G = -c • (A *ᵥ G - t • (A ^ 2 *ᵥ G)) := hode
  obtain ⟨hsecond, hthird⟩ :=
    nilpotentVectorDeriv_second_third D A hA h3 c t hc ht G hode'
  refine ⟨hsecond, ?_⟩
  intro i
  exact congrFun hthird i

/-- Uniform longitudinal degree restriction on the original
transverse-homogeneous leading layer. No lower layer is changed. -/
theorem sourceNilpotent_longitudinal_third_eq_zero
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) L)) = 0 := by
  classical
  let P := pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) L))
  have h := (sourceNilpotent_transverseGradient_second_third a N hN L n hL hgrad).2
  have hz (i : Fin 3) : pderiv (.inr i) P = 0 := by
    dsimp only [P]
    simp only [HC4.Newton.pderiv_comm_backport (Sum.inr i) (Sum.inl ())]
    exact h i
  have hp := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL (Sum.inl ())) (Sum.inl ())) (Sum.inl ())
  have hp' : P.IsWeightedHomogeneous transverseCubicWeight ((n+1 : ℕ) : ℤ) := by
    simpa [P, transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight P (n+1) hp'
  simp only [hz, mul_zero, Finset.sum_const_zero] at he
  have hn : ((n+1 : ℕ) : StationarySource K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (mul_eq_zero.mp he.symm).resolve_left hn




/-! ## Exact longitudinal support, with the nilpotence-index refinement

The derivative identities become literal exponent bounds in the
original source. In the square-zero case the explicit second
gradient derivative vanishes, so the leading layer is affine in x.
-/

/-- A nonzero coefficient of positive exponent survives one derivative
at its unique shifted exponent. Work over an abstract index type so
elaboration does not unfold the concrete sum-type Finsupp operations. -/
private theorem sourceCoeff_derivative_ne_zero
    {ι : Type*} (i : ι)
    (P : MvPolynomial ι K) (d : ι →₀ ℕ)
    (hd : MvPolynomial.coeff d P ≠ 0) (hp : 0 < d i) :
    MvPolynomial.coeff (d - Finsupp.single i 1) (pderiv i P) ≠ 0 := by
  classical
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  change MvPolynomial.coeff e (pderiv i P) ≠ 0
  rw [HC4.Newton.coeff_pderiv_backport, he]
  exact mul_ne_zero hd (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (e i)))

private theorem sourceSupport_secondDerivative_bound
    {ι : Type*} (i : ι) (P : MvPolynomial ι K)
    (hP : pderiv i (pderiv i P) = 0)
    (d : ι →₀ ℕ) (hd : MvPolynomial.coeff d P ≠ 0) :
    d i ≤ 1 := by
  classical
  by_contra hn
  have hp : 0 < d i := by omega
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hc : MvPolynomial.coeff e (pderiv i P) ≠ 0 :=
    sourceCoeff_derivative_ne_zero i P d hd hp
  have hz : e i = 0 :=
    HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero i (pderiv i P) hP e hc
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have heval := congrArg (fun z : ι →₀ ℕ => z i) he
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at heval
  omega

private theorem sourceSupport_thirdDerivative_bound
    {ι : Type*} (i : ι) (P : MvPolynomial ι K)
    (hP : pderiv i (pderiv i (pderiv i P)) = 0)
    (d : ι →₀ ℕ) (hd : MvPolynomial.coeff d P ≠ 0) :
    d i ≤ 2 := by
  classical
  by_contra hn
  have hp : 0 < d i := by omega
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hc : MvPolynomial.coeff e (pderiv i P) ≠ 0 :=
    sourceCoeff_derivative_ne_zero i P d hd hp
  have hz : e i ≤ 1 := sourceSupport_secondDerivative_bound i (pderiv i P) hP e hc
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have heval := congrArg (fun z : ι →₀ ℕ => z i) he
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at heval
  omega

/-- Two vanishing longitudinal derivatives force each surviving
monomial of the original polynomial to have longitudinal exponent ≤1. -/
theorem sourceLongitudinal_support_le_one
    (P : StationarySource K)
    (hP : pderiv (.inl ()) (pderiv (.inl ()) P) = 0)
    (d : StationaryExponent) (hd : MvPolynomial.coeff d P ≠ 0) :
    d (.inl ()) ≤ 1 :=
  sourceSupport_secondDerivative_bound (Sum.inl ()) P hP d hd

/-- Three vanishing longitudinal derivatives force each surviving
monomial of the original polynomial to have longitudinal exponent ≤2. -/
theorem sourceLongitudinal_support_le_two
    (P : StationarySource K)
    (hP : pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) P)) = 0)
    (d : StationaryExponent) (hd : MvPolynomial.coeff d P ≠ 0) :
    d (.inl ()) ≤ 2 :=
  sourceSupport_thirdDerivative_bound (Sum.inl ()) P hP d hd

/-- Square-zero linear characteristics force the original homogeneous
leading potential to be longitudinally affine. -/
theorem sourceNilpotent_longitudinal_second_eq_zero_of_square_zero
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 2 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    pderiv (.inl ()) (pderiv (.inl ()) L) = 0 := by
  classical
  have h3 : N ^ 3 = 0 := by rw [pow_succ N 2, hN, zero_mul]
  let P := pderiv (.inl ()) (pderiv (.inl ()) L)
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) :=
    N.transpose.map MvPolynomial.C
  have h2N : N.transpose ^ 2 = 0 := by
    rw [← Matrix.transpose_pow, hN, Matrix.transpose_zero]
  have h2A : A ^ 2 = 0 := by
    have h : (N.transpose ^ 2).map (MvPolynomial.C : K →+* StationarySource K) =
        (0 : Matrix (Fin 3) (Fin 3) (StationarySource K)) := by
      rw [h2N]
      ext i j
      simp
    simpa only [A, pow_two, Matrix.map_mul] using h
  have hs := (sourceNilpotent_transverseGradient_second_third a N h3 L n hL hgrad).1
  dsimp only at hs
  have hs' :
      (fun i : Fin 3 => pderiv (Sum.inl ()) (pderiv (Sum.inl ())
        (pderiv (Sum.inr i) L))) =
      ((n : StationarySource K) * ((n : StationarySource K)+1)) •
        (A ^ 2 *ᵥ (fun i : Fin 3 => pderiv (Sum.inr i) L)) := hs
  rw [h2A, Matrix.zero_mulVec, smul_zero] at hs'
  have hz (i : Fin 3) : pderiv (.inr i) P = 0 := by
    dsimp only [P]
    simp only [HC4.Newton.pderiv_comm_backport (Sum.inr i) (Sum.inl ())]
    exact congrFun hs' i
  have hp := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous hL (Sum.inl ())) (Sum.inl ())
  have hp' : P.IsWeightedHomogeneous transverseCubicWeight ((n+1 : ℕ) : ℤ) := by
    simpa [P, transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight P (n+1) hp'
  simp only [hz, mul_zero, Finset.sum_const_zero] at he
  have hn : ((n+1 : ℕ) : StationarySource K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (mul_eq_zero.mp he.symm).resolve_left hn

/-- A pole-free leading layer has total degree at most m+2, or m+1
when its characteristic matrix is square-zero. These are bounds on
the LEADING layer, not on the lower layers of the original source. -/
theorem sourceNilpotent_leading_totalDegree_support_bound
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    IsWeightLE (stationaryEdgeWeight 1 1) ((n : ℤ)+3) L ∧
      (N ^ 2 = 0 → IsWeightLE (stationaryEdgeWeight 1 1) ((n : ℤ)+2) L) := by
  have hthird := sourceNilpotent_longitudinal_third_eq_zero a N hN L n hL hgrad
  constructor
  · intro d hd
    have hc := MvPolynomial.mem_support_iff.mp hd
    have hp := sourceLongitudinal_support_le_two L hthird d hc
    have hq := hL hc
    rw [stationaryEdge_weight_eq, one_mul, one_mul, hq]
    omega
  · intro h2 d hd
    have hsecond :=
      sourceNilpotent_longitudinal_second_eq_zero_of_square_zero a N h2 L n hL hgrad
    have hc := MvPolynomial.mem_support_iff.mp hd
    have hp := sourceLongitudinal_support_le_one L hsecond d hc
    have hq := hL hc
    rw [stationaryEdge_weight_eq, one_mul, one_mul, hq]
    omega




/-! ## First LOWER layer in a pole-free chart

The first correction identity works over the polynomial coefficient
domain itself. The inverse nilpotent shear therefore reconstructs
the actual lower layer from its two time coefficients, with no
denominators and no claim of nonlinear Hessian invariance.
-/

/-- Polynomial first correction transport: the actual adjacent
source layer has only two characteristic-time coefficients. -/
theorem sourceNilpotent_firstCorrection_affine
    (F : StationarySource K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight m F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight m F)))) :
    let P := linearLineEval a N (initialForm transverseCubicWeight (m-1) F)
    P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  have hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0 := hreg
  have hV : V (.inl ()) = 1 := rfl
  have hg : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight m F)) =
      _root_.Polynomial.C (MvPolynomial.aeval z
        (pderiv i (initialForm transverseCubicWeight m F))) := hgrad
  exact sourceLeading_firstCorrection_affine_along_line F m hm hcap hdet z V hz hV hg

/-- The honest polynomial inverse characteristic coordinates, regarded
as a substitution of the reference transverse polynomial ring. -/
def sourceNilpotentInverseEval
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial (Fin 3) K →ₐ[K] StationarySource K :=
  MvPolynomial.aeval fun i =>
    X (.inr i) -
      (X (.inl ()) - MvPolynomial.C a) * sourceLinearVector N i +
      (X (.inl ()) - MvPolynomial.C a) ^ 2 * sourceLinearVector (N ^ 2) i

/-- The longitudinal coordinate minus its anchor is characteristic time. -/
theorem sourceNilpotent_time_eval
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) :
    linearLineEval a N (X (.inl ()) - MvPolynomial.C a) =
      (_root_.Polynomial.X : _root_.Polynomial (MvPolynomial (Fin 3) K)) := by
  simp [linearLineEval, lineEval]

private theorem sourceNilpotentInverseEval_X_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (i : Fin 3) :
    linearLineEval a N (sourceNilpotentInverseEval a N (X i)) =
      _root_.Polynomial.C (X i) := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hx : linearLineEval a N (X (.inr i)) =
      _root_.Polynomial.C (X i : B) +
        _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
    simp [linearLineEval, lineEval, referenceLinearVector]
  have h2 : N * N = N ^ 2 := (pow_two N).symm
  have h3 : N ^ 2 * N = 0 := by rw [← pow_succ, hN]
  have hz : referenceLinearVector (0 : Matrix (Fin 3) (Fin 3) K) i = 0 := by
    simp [referenceLinearVector]
  have hx0 : linearLineEval a N (X (Sum.inl ())) =
      _root_.Polynomial.C (MvPolynomial.C a : B) + _root_.Polynomial.X := by
    simp [linearLineEval, lineEval]
  have hc : linearLineEval a N (MvPolynomial.C a) =
      _root_.Polynomial.C (MvPolynomial.C a : B) := by
    simp [linearLineEval, lineEval]
  simp only [sourceNilpotentInverseEval, MvPolynomial.aeval_X, map_add, map_sub,
    map_mul, map_pow, hx, hx0, hc,
    linearLineEval_sourceLinearVector, h2, h3, hz, map_zero, zero_mul, add_zero]
  ring

/-- Composing inverse coordinates with forward line evaluation
recovers the reference polynomial as a constant time polynomial. -/
theorem sourceNilpotentInverseEval_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (P : MvPolynomial (Fin 3) K) :
    linearLineEval a N (sourceNilpotentInverseEval a N P) = _root_.Polynomial.C P := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hcomp : (linearLineEval a N).toRingHom.comp
      (sourceNilpotentInverseEval a N).toRingHom =
      (_root_.Polynomial.C : B →+* _root_.Polynomial B) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change linearLineEval a N (sourceNilpotentInverseEval a N (MvPolynomial.C c)) =
        _root_.Polynomial.C (MvPolynomial.C c)
      simp [sourceNilpotentInverseEval, linearLineEval, lineEval,
        IsScalarTower.algebraMap_apply K B (_root_.Polynomial B),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      exact sourceNilpotentInverseEval_X_transport a N hN i
  exact RingHom.congr_fun hcomp P

/-- Reconstruct any affine-in-time source polynomial from its first
two time coefficients using the nilpotent polynomial inverse. -/
theorem sourceNilpotent_affine_inverseFormula
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K)
    (hQ : let P := linearLineEval a N Q
      P = _root_.Polynomial.C (P.coeff 0) +
        _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X) :
    let P := linearLineEval a N Q
    Q = sourceNilpotentInverseEval a N (P.coeff 0) +
      sourceNilpotentInverseEval a N (P.coeff 1) *
        (X (.inl ()) - MvPolynomial.C a) := by
  apply linearLineEval_injective_of_cube_zero a N hN
  rw [map_add, map_mul, sourceNilpotentInverseEval_transport a N hN,
    sourceNilpotentInverseEval_transport a N hN, sourceNilpotent_time_eval]
  exact hQ

/-- Exact original-source reconstruction of the first lower grade.
This connects leading rigidity to the actual lower source support. -/
theorem sourceNilpotent_firstCorrection_inverseFormula
    (F : StationarySource K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight m F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight m F)))) :
    let Q := initialForm transverseCubicWeight (m-1) F
    let P := linearLineEval a N Q
    Q = sourceNilpotentInverseEval a N (P.coeff 0) +
      sourceNilpotentInverseEval a N (P.coeff 1) *
        (X (.inl ()) - MvPolynomial.C a) :=
  sourceNilpotent_affine_inverseFormula a N hN _ 
    (sourceNilpotent_firstCorrection_affine F m hm hcap hdet a N hreg hgrad)

end
end HC4.Polynomial.RankThreeCubic
