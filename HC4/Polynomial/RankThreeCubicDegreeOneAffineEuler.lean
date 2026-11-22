import HC4.Polynomial.RankThreeCubicSourceHomogeneousPoleRankOneClosure
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Affine Euler identity for a degree-one transverse polynomial

Every polynomial of total degree exactly one is the sum of its
constant homogeneous component and its homogeneous linear component.

This supplies the exact affine Euler identity
  sum_i X_i * d_i P = P - C(P.coeff 0)
and, consequently, a canonical affine-linear representation.
No hypothesis of homogeneity is inserted.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

private theorem degreeOne_component_split
    (P : B3 K) (hdegree : P.totalDegree = 1) :
    P = MvPolynomial.C (P.coeff 0) +
      MvPolynomial.homogeneousComponent 1 P := by
  classical
  have h := MvPolynomial.sum_homogeneousComponent P
  have hs :
      MvPolynomial.homogeneousComponent 0 P +
        MvPolynomial.homogeneousComponent 1 P = P := by
    simpa [hdegree, Finset.sum_range_succ] using h
  simpa only [MvPolynomial.homogeneousComponent_zero] using hs.symm

/-- Exact degree-one Euler identity with the constant term retained. -/
theorem degreeOne_affineEuler
    (P : B3 K) (hdegree : P.totalDegree = 1) :
    (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i P) =
      P - MvPolynomial.C (P.coeff 0) := by
  classical
  let Q : B3 K := MvPolynomial.homogeneousComponent 1 P
  have hP : P = MvPolynomial.C (P.coeff 0) + Q :=
    degreeOne_component_split P hdegree
  have heuler :
      (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i Q) = Q := by
    have he := (MvPolynomial.homogeneousComponent_isHomogeneous 1 P).sum_X_mul_pderiv
    simpa only [one_nsmul] using he
  calc
    (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i P) =
        (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i Q) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hP]
          simp only [map_add, pderiv_C, zero_add]
    _ = Q := heuler
    _ = P - MvPolynomial.C (P.coeff 0) := by
          rw [hP]
          ring

/-- Every degree-one polynomial is affine-linear, with the linear
coefficients obtained from its first partial derivatives. -/
theorem degreeOne_affineRepresentation
    (P : B3 K) (hdegree : P.totalDegree = 1) :
    P = MvPolynomial.C (P.coeff 0) +
      ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        MvPolynomial.C ((pderiv i P).coeff 0) := by
  classical
  let Q : B3 K := MvPolynomial.homogeneousComponent 1 P
  have hP : P = MvPolynomial.C (P.coeff 0) + Q :=
    degreeOne_component_split P hdegree
  have hderiv (i : Fin 3) :
      pderiv i P = pderiv i Q := by
    rw [hP]
    simp only [map_add, pderiv_C, zero_add]
  have hconst (i : Fin 3) :
      pderiv i P = MvPolynomial.C ((pderiv i P).coeff 0) := by
    have hdeg : (pderiv i Q).totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).2
        ((MvPolynomial.homogeneousComponent_isHomogeneous 1 P).pderiv)
    have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
    rw [hderiv i]
    exact heq
  calc
    P = MvPolynomial.C (P.coeff 0) +
        (P - MvPolynomial.C (P.coeff 0)) := by ring
    _ = MvPolynomial.C (P.coeff 0) +
        ∑ i : Fin 3, (MvPolynomial.X i : B3 K) * pderiv i P := by
          rw [degreeOne_affineEuler P hdegree]
    _ = MvPolynomial.C (P.coeff 0) +
        ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
          MvPolynomial.C ((pderiv i P).coeff 0) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [hconst i]

end
end HC4.Polynomial.RankThreeCubic
