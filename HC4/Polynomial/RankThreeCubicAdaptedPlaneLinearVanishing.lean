import HC4.Polynomial.RankThreeCubicZeroBinarySourceCofactor
import Mathlib.Tactic

/-!
# Lifting a linear identity from the actual pole plane

A homogeneous linear polynomial written as P(y)=gamma·y
vanishes at both tangent basis columns of an invertible
frame for p(y)=ell·y if and only if gamma is proportional
to ell. Hence p divides P *as a polynomial*, not just
after evaluation at points of the plane.

This lemma is the exact polynomial lift needed to move an
adapted full-Hessian tangent kernel into the residue quotient
K[y]/(p), where the actual normalized source pole residue lives.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- A linear polynomial vanishing on two independent tangent
columns is a multiple of the pole's own defining linear form. -/
theorem adaptedFrame_linearForm_dvd_of_tangentColumns_zero
    (p : B3 K) (ell gamma : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (hg1 : MvPolynomial.aeval
       (M.mulVec ![(0 : K), 1, 0])
       (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
          MvPolynomial.C (gamma i)) = 0)
    (hg2 : MvPolynomial.aeval
       (M.mulVec ![(0 : K), 0, 1])
       (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
          MvPolynomial.C (gamma i)) = 0) :
    p ∣ (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
      MvPolynomial.C (gamma i)) := by
  classical
  let P : B3 K := ∑ i : Fin 3,
    (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i)
  have hgM1 : (∑ i : Fin 3, gamma i * M i 1) = 0 := by
    have h := hg1
    change MvPolynomial.aeval (M.mulVec ![(0 : K), 1, 0]) P = 0 at h
    rw [polynomialLinearForm_evaluation_dot P gamma rfl,
      frame_linearFunctional_at] at h
    simpa using h
  have hgM2 : (∑ i : Fin 3, gamma i * M i 2) = 0 := by
    have h := hg2
    change MvPolynomial.aeval (M.mulVec ![(0 : K), 0, 1]) P = 0 at h
    rw [polynomialLinearForm_evaluation_dot P gamma rfl,
      frame_linearFunctional_at] at h
    simpa using h
  obtain ⟨k, hk⟩ :=
    tangentFrame_linearFunctional_proportional
      ell gamma hell M hM hM1 hM2 hgM1 hgM2
  have hP : P = MvPolynomial.C k * p := by
    calc
      P = ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        MvPolynomial.C (gamma i) := rfl
      _ = ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        MvPolynomial.C (k * ell i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hk i]
      _ = MvPolynomial.C k * p := by
          rw [hpoly, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [map_mul]
          ring
  exact ⟨MvPolynomial.C k, by change P = p * MvPolynomial.C k
                            rw [hP]
                            ring⟩

end
end HC4.Polynomial.RankThreeCubic
