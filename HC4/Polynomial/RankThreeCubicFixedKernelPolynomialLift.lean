import HC4.Polynomial.RankThreeCubicAdaptedPlaneLinearVanishing
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# A fixed full tangent Hessian kernel lifts to polynomial divisibility

Let H(y) be a 3x3 matrix of homogeneous linear polynomials.
If M is an invertible frame adapted to the linear pole
p(y)=ell·y and the congruent Hessian

  B(u,v)=Mᵀ H(M(0,u,v)) M

annihilates the fixed tangent vector w=(0,r,t) for every
point (u,v) in the pole plane, then, for W=Mw,

  p divides ∑_j H_ij(y) * W_j

for each i. These are identities in the *polynomial ring*
K[y], and therefore hold in the residue quotient K[y]/(p).

The key step is to use the homogeneous degree-one Euler
identity to turn each row of H(y)W into an explicit linear
form and apply the adapted-frame linear-vanishing lemma.
This bridge does not invent a kernel in the quotient.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- A homogeneous degree-one polynomial has an explicit
coefficient-wise linear form, using Euler's identity. -/
theorem homogeneousOne_polynomial_linearForm
    (P : B3 K) (hP : P.IsHomogeneous 1) :
    P = ∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
      MvPolynomial.C ((pderiv j P).coeff 0) := by
  classical
  have hder (j : Fin 3) :
      pderiv j P = MvPolynomial.C ((pderiv j P).coeff 0) := by
    have hdeg0 : (pderiv j P).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2
        hP.pderiv
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
  have hEuler := hP.sum_X_mul_pderiv
  have heq : P = ∑ j : Fin 3,
      (MvPolynomial.X j : B3 K) * pderiv j P := by
    simpa only [one_nsmul] using hEuler.symm
  calc
    P = ∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
        pderiv j P := heq
    _ = ∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
        MvPolynomial.C ((pderiv j P).coeff 0) := by
          apply Finset.sum_congr rfl
          intro j _
          exact congrArg
            (fun q : B3 K => (MvPolynomial.X j : B3 K) * q)
            (hder j)

/-- A congruent fixed kernel descends from an invertible
frame to the original matrix at the same point. -/
theorem invertibleFrame_congruenceKernel_descends
    (H M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (w : Fin 3 → K)
    (hker : (M.transpose * H * M) *ᵥ w = 0) :
    H *ᵥ (M.mulVec w) = 0 := by
  classical
  have ht : M.transpose.det ≠ 0 := by
    simpa only [Matrix.det_transpose] using hM
  have hnull : M.transpose *ᵥ (H *ᵥ (M.mulVec w)) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hker
  by_contra hne
  exact ht (Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨H *ᵥ (M.mulVec w), hne, hnull⟩)

/-- The fixed tangent kernel of a degree-one polynomial Hessian
on the pole plane is a polynomial kernel *modulo the pole*.
No source-specific gradient or determinant assumptions are used. -/
theorem homogeneousLinearMatrix_tangentKernel_rows_divisible
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hhom : ∀ i j : Fin 3, (H i j).IsHomogeneous 1)
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (r t : K) [CharZero K]
    (hfixed : ∀ u v : K,
      let A := H.map
        (MvPolynomial.aeval (M.mulVec ![(0 : K), u, v])).toRingHom
      (M.transpose * A * M) *ᵥ ![(0 : K), r, t] = 0) :
    ∀ i : Fin 3,
      p ∣ (∑ j : Fin 3, H i j *
        MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) j)) := by
  classical
  let w : Fin 3 → K := ![(0 : K), r, t]
  let W : Fin 3 → K := M.mulVec w
  let P : Fin 3 → B3 K :=
    fun i => ∑ j : Fin 3, H i j * MvPolynomial.C (W j)
  have hP (i : Fin 3) : (P i).IsHomogeneous 1 := by
    dsimp [P]
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    have hc : (MvPolynomial.C (W j) : B3 K).IsHomogeneous 0 :=
      MvPolynomial.isHomogeneous_C (Fin 3) (W j)
    simpa only [add_zero] using (hhom i j).mul hc
  have hrowZero (i : Fin 3) (u v : K) :
      MvPolynomial.aeval (M.mulVec ![(0 : K), u, v]) (P i) = 0 := by
    let x : Fin 3 → K := M.mulVec ![(0 : K), u, v]
    let ev : B3 K →+* K := (MvPolynomial.aeval x).toRingHom
    have hH : (H.map ev) *ᵥ W = 0 :=
      invertibleFrame_congruenceKernel_descends
        (H.map ev) M hM w (hfixed u v)
    have hi := congrFun hH i
    change (∑ j : Fin 3, ev (H i j) * W j) = 0 at hi
    change ev (∑ j : Fin 3, H i j * MvPolynomial.C (W j)) = 0
    have hevC (j : Fin 3) : ev (MvPolynomial.C (W j)) = W j := by
      change MvPolynomial.aeval x (MvPolynomial.C (W j)) = W j
      simp
    simpa only [map_sum, map_mul, hevC] using hi
  intro i
  let gamma : Fin 3 → K := fun j => (pderiv j (P i)).coeff 0
  have hform : P i = ∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
      MvPolynomial.C (gamma j) :=
    homogeneousOne_polynomial_linearForm (P i) (hP i)
  have h1 : MvPolynomial.aeval (M.mulVec ![(0 : K), 1, 0])
      (∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
         MvPolynomial.C (gamma j)) = 0 := by
    rw [← hform]
    exact hrowZero i 1 0
  have h2 : MvPolynomial.aeval (M.mulVec ![(0 : K), 0, 1])
      (∑ j : Fin 3, (MvPolynomial.X j : B3 K) *
         MvPolynomial.C (gamma j)) = 0 := by
    rw [← hform]
    exact hrowZero i 0 1
  change p ∣ P i
  rw [hform]
  exact adaptedFrame_linearForm_dvd_of_tangentColumns_zero
    p ell gamma hpoly hell M hM hM1 hM2 h1 h2

end
end HC4.Polynomial.RankThreeCubic
