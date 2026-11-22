import HC4.Polynomial.RankThreeCubicTensorRepeatedPoleTangency
import HC4.Polynomial.RankThreeCubicSourceDegrees
import Mathlib.Tactic

/-!
# A homogeneous linear polynomial Hessian is its cubic tensor

These two evaluation lemmas are valid over arbitrary commutative
K-algebras. They provide the exact bridge from the actual source
Hessian H(y), whose entries are homogeneous linear polynomials,
to the symmetric tensor Hessian evaluated in the residue quotient
K[y]/(p).

The tensor coefficients are the first transverse derivatives
of H, transported by the quotient map. Homogeneity-one Euler
identity supplies equality at every point; no arbitrary
matrix-pencil representation is assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- For a degree-one homogeneous matrix, evaluating its entries
is exactly evaluating the associated linear tensor pencil.
The ring map q is required only to agree with scalar evaluation,
as the canonical prime quotient map does. -/
theorem homogeneousLinearHessian_tensor_evaluation
    {R : Type*} [CommRing R] [Algebra K R]
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hhom : ∀ i j : Fin 3, (H i j).IsHomogeneous 1)
    (q : B3 K →+* R)
    (hqC : ∀ b : K, q (MvPolynomial.C b) = algebraMap K R b)
    (v : Fin 3 → R) :
    H.map (MvPolynomial.aeval v).toRingHom =
      cubicTensorHessianAt (fun t i j => q (pderiv t (H i j))) v := by
  classical
  have hderConst (t i j : Fin 3) :
      pderiv t (H i j) = MvPolynomial.C ((pderiv t (H i j)).coeff 0) := by
    have hdeg0 : (pderiv t (H i j)).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2
        ((hhom i j).pderiv)
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
  ext i j
  have hEuler : H i j =
      ∑ t : Fin 3, (MvPolynomial.X t : B3 K) * pderiv t (H i j) := by
    have he := (hhom i j).sum_X_mul_pderiv
    simpa only [one_nsmul] using he.symm
  have hevalDer (t : Fin 3) :
      MvPolynomial.aeval v (pderiv t (H i j)) =
        q (pderiv t (H i j)) := by
    rw [hderConst t i j]
    rw [MvPolynomial.aeval_C, hqC]
  change MvPolynomial.aeval v (H i j) =
    ∑ t : Fin 3, v t * q (pderiv t (H i j))
  rw [hEuler]
  simp only [map_sum, map_mul, MvPolynomial.aeval_X]
  apply Finset.sum_congr rfl
  intro t _
  rw [hevalDer t]

/-- Evaluating a genuinely homogeneous linear polynomial in any
K-algebra is exactly the scalar-valued linear functional defined
by its three coefficients. -/
theorem homogeneousLinearPole_aeval_eq_linearFunctional
    {R : Type*} [CommRing R] [Algebra K R]
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ t : Fin 3,
      (MvPolynomial.X t : B3 K) * MvPolynomial.C (ell t))
    (v : Fin 3 → R) :
    MvPolynomial.aeval v p =
      cubicPoleLinearFunctional (fun t => algebraMap K R (ell t)) v := by
  classical
  rw [hpoly]
  simp only [map_sum, map_mul, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C]
  unfold cubicPoleLinearFunctional
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end HC4.Polynomial.RankThreeCubic
