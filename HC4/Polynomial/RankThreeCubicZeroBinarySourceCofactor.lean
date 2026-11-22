import HC4.Polynomial.RankThreeCubicTensorZeroBinaryTriple
import HC4.Polynomial.RankThreeCubicAdaptedNormalProportional
import HC4.Polynomial.RankThreeCubicSourceLinearTensorEvaluation
import Mathlib.Tactic

/-!
# Zero tangential binary cubic forces the complementary pole factor to align

This is the essential geometry-to-polynomial bridge. Suppose a
homogeneous linear polynomial Hessian H has a genuinely symmetric
cubic third-derivative tensor D, det H = p²*c, and both p and c
are represented by linear forms ell and gamma.

For any invertible frame M tangent to p, if the tangent 2x2
Hessian block is zero everywhere on the p=0 plane, then the
explicit cubic tensor normal form forces gamma to vanish on
both tangent columns. Hence gamma is proportional to ell,
so p divides c.

This lemma does not assume p | c. Its conclusion derives it
from the square determinant factor and source-compatible
third-derivative symmetry. It will exclude the zero-binary
case of a genuinely exactly-double source pole.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section
set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- Evaluate a linear form on an arbitrary adapted-frame vector,
as the same linear combination of its three column values. -/
theorem frame_linearFunctional_at
    (ell : Fin 3 → K)
    (M : Matrix (Fin 3) (Fin 3) K)
    (z u v : K) :
    (∑ i : Fin 3, ell i * (M.mulVec ![z, u, v]) i) =
      (∑ i : Fin 3, ell i * M i 0) * z +
      (∑ i : Fin 3, ell i * M i 1) * u +
      (∑ i : Fin 3, ell i * M i 2) * v := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Polynomial linear form evaluation equals its scalar dot
product, using the verified homogeneous-linear pole lemma. -/
theorem polynomialLinearForm_evaluation_dot
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (x : Fin 3 → K) :
    MvPolynomial.aeval x p = ∑ i : Fin 3, ell i * x i := by
  simpa [cubicPoleLinearFunctional] using
    (homogeneousLinearPole_aeval_eq_linearFunctional p ell hpoly x)

/-- In an adapted frame, square repeated factor and zero
tangent block force the complementary linear polynomial
factor to be divisible by the original pole polynomial.

The theorem requires the genuine tensor symmetry and evaluation
equation as explicit, checkable hypotheses; the source-specific
third-derivative construction provides them without assumptions. -/
theorem homogeneousLinearCubic_zeroBinaryBlock_implies_p_dvd_cofactor
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hEval : ∀ x : Fin 3 → K,
      H.map (MvPolynomial.aeval x).toRingHom =
        cubicTensorHessianAt D x)
    (p c : B3 K) (ell gamma : Fin 3 → K)
    (hfactor : H.det = (p * p) * c)
    (hpform : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hcform : c = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (gamma i))
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (hzero : ∀ u v : K,
      let B := M.transpose *
        H.map (MvPolynomial.aeval (M.mulVec ![(0 : K), u, v])).toRingHom * M
      B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0) :
    p ∣ c := by
  classical
  let E := cubicTensorInFrame D M
  let t : K := ∑ i : Fin 3, ell i * M i 0
  let g0 : K := ∑ i : Fin 3, gamma i * M i 0
  let g1 : K := ∑ i : Fin 3, gamma i * M i 1
  let g2 : K := ∑ i : Fin 3, gamma i * M i 2
  let pref : K := M.det ^ 2 * t ^ 2
  have ht : t ≠ 0 :=
    tangentFrame_normal_first_ne_zero ell hell M hM hM1 hM2
  have hpref : pref ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hM) (pow_ne_zero 2 ht)
  have hs12 (i j k : Fin 3) : E i j k = E j i k :=
    cubicTensorInFrame_swap12 D hswap₁ M i j k
  have hs23 (i j k : Fin 3) : E i j k = E i k j :=
    cubicTensorInFrame_swap23 D hswap₂ M i j k
  have hmat (w : Fin 3 → K) :
      cubicTensorHessianAt E w =
        M.transpose *
          H.map (MvPolynomial.aeval (M.mulVec w)).toRingHom * M := by
    rw [← cubicTensorInFrame_hessian]
    rw [← hEval (M.mulVec w)]
  have hzeroE (u v : K) :
      let B := cubicTensorHessianAt E ![(0 : K), u, v]
      B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 0 := by
    change
      (cubicTensorHessianAt E ![(0 : K), u, v]) 1 1 = 0 ∧
      (cubicTensorHessianAt E ![(0 : K), u, v]) 1 2 = 0 ∧
      (cubicTensorHessianAt E ![(0 : K), u, v]) 2 2 = 0
    rw [hmat]
    exact hzero u v
  have hdetEval (x : Fin 3 → K) :
      (H.map (MvPolynomial.aeval x).toRingHom).det =
        MvPolynomial.aeval x H.det := by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply]
  have hpEval (z u v : K) :
      MvPolynomial.aeval (M.mulVec ![z, u, v]) p = t * z := by
    rw [polynomialLinearForm_evaluation_dot p ell hpform,
      frame_linearFunctional_at]
    simp only [hM1, hM2, zero_mul, add_zero]
  have hcEval (z u v : K) :
      MvPolynomial.aeval (M.mulVec ![z, u, v]) c =
        g0 * z + g1 * u + g2 * v := by
    rw [polynomialLinearForm_evaluation_dot c gamma hcform,
      frame_linearFunctional_at]
  have hfac (z u v : K) :
      (cubicTensorHessianAt E ![z, u, v]).det =
        z ^ 2 * ((pref * g0) * z + (pref * g1) * u +
          (pref * g2) * v) := by
    let w : Fin 3 → K := ![z, u, v]
    rw [hmat]
    calc
      (M.transpose *
          H.map (MvPolynomial.aeval (M.mulVec w)).toRingHom * M).det =
        M.det ^ 2 * MvPolynomial.aeval (M.mulVec w) H.det := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
            hdetEval]
          ring
      _ = M.det ^ 2 *
        ((t * z) * (t * z) * (g0 * z + g1 * u + g2 * v)) := by
          rw [hfactor]
          simp only [map_mul, hpEval, hcEval]
          ring
      _ = z ^ 2 * ((pref * g0) * z + (pref * g1) * u +
          (pref * g2) * v) := by ring
  obtain ⟨hB, hC⟩ :=
    cubicTensor_zeroBinaryBlock_squareFactor_tangentCoefficients_zero
      E hs12 hs23 hzeroE (pref * g0) (pref * g1) (pref * g2) hfac
  have hg1 : g1 = 0 := (mul_eq_zero.mp hB).resolve_left hpref
  have hg2 : g2 = 0 := (mul_eq_zero.mp hC).resolve_left hpref
  obtain ⟨k, hk⟩ :=
    tangentFrame_linearFunctional_proportional
      ell gamma hell M hM hM1 hM2 hg1 hg2
  have hc_eq : c = MvPolynomial.C k * p := by
    calc
      c = ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        MvPolynomial.C (gamma i) := hcform
      _ = ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        MvPolynomial.C (k * ell i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hk i]
      _ = MvPolynomial.C k * p := by
          rw [hpform]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [map_mul]
          ring
  exact ⟨MvPolynomial.C k, by rw [hc_eq]; ring⟩

end
end HC4.Polynomial.RankThreeCubic
