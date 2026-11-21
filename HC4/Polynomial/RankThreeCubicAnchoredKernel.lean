import HC4.Polynomial.RankThreeCubicCharacteristics
import HC4.Polynomial.RankThreeCubicPoleFreeLinear
import Mathlib.Tactic

/-!
# Recovering the anchored Hessian-kernel equation

The gradient is constant along the constructed affine characteristic
line. Extracting its linear coefficient proves that the velocity is
a kernel vector of the actual Hessian evaluated at the anchored point.
This step must precede the pole-free rational-to-linear argument.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The time derivative is a derivation over the base coefficient field. -/
private def timeDerivative : Derivation K (_root_.Polynomial F) (_root_.Polynomial F) where
  toFun := _root_.Polynomial.derivative
  map_add' x y := _root_.Polynomial.derivative_add
  map_smul' a p := by
    simp only [Algebra.smul_def,
      IsScalarTower.algebraMap_apply K F (_root_.Polynomial F),
      _root_.Polynomial.algebraMap_eq,
      _root_.Polynomial.derivative_C_mul, RingHom.id_apply]
  map_one_eq_zero' := _root_.Polynomial.derivative_one
  leibniz' x y := by
    simpa only [smul_eq_mul] using
      (_root_.Polynomial.derivative_mul (f := x) (g := y))

/-- The constant coefficient of the line evaluation is the ordinary
evaluation at its starting point. -/
private theorem coeff_zero_lineEval (z V : ι → F) (p : MvPolynomial ι K) :
    (lineEval z V p).coeff 0 = MvPolynomial.aeval z p := by
  classical
  let E := lineEval (K := K) z V
  have hev : (_root_.Polynomial.constantCoeff.comp E.toRingHom) =
      (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] F).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, lineEval, IsScalarTower.algebraMap_apply K F (_root_.Polynomial F),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      simp [E, lineEval]
  exact RingHom.congr_fun hev p

/-- The first time coefficient of a polynomial along an affine
characteristic equals its directional derivative at the basepoint. -/
theorem coeff_one_lineEval_eq_directional
    (z V : ι → F) (p : MvPolynomial ι K) :
    (lineEval z V p).coeff 1 =
      ∑ i : ι, MvPolynomial.aeval z (pderiv i p) * V i := by
  classical
  let E := lineEval (K := K) z V
  let D : Derivation K (_root_.Polynomial F) (_root_.Polynomial F) :=
    timeDerivative
  have hDX (i : ι) : D (_root_.Polynomial.C (z i) +
      _root_.Polynomial.C (V i) * _root_.Polynomial.X) =
      _root_.Polynomial.C (V i) := by
    change _root_.Polynomial.derivative
      (_root_.Polynomial.C (z i) + _root_.Polynomial.C (V i) *
        _root_.Polynomial.X) = _
    simp only [_root_.Polynomial.derivative_add,
      _root_.Polynomial.derivative_C, zero_add,
      _root_.Polynomial.derivative_C_mul, _root_.Polynomial.derivative_X, mul_one]
  have hchain := derivation_aeval D
    (fun i : ι => _root_.Polynomial.C (z i) +
      _root_.Polynomial.C (V i) * _root_.Polynomial.X) p
  change D (E p) = ∑ i : ι,
    E (pderiv i p) * D (_root_.Polynomial.C (z i) +
      _root_.Polynomial.C (V i) * _root_.Polynomial.X) at hchain
  simp_rw [hDX] at hchain
  have h := congrArg
    (fun q : _root_.Polynomial F => q.coeff 0) hchain
  have hleft : (D (E p)).coeff 0 = (E p).coeff 1 := by
    change (_root_.Polynomial.derivative (E p)).coeff 0 = _
    simpa using (_root_.Polynomial.coeff_derivative (E p) 0)
  change (D (E p)).coeff 0 =
    (∑ i : ι, E (pderiv i p) * _root_.Polynomial.C (V i)).coeff 0 at h
  rw [hleft] at h
  simp only [map_sum] at h
  have hterm (i : ι) :
      (E (pderiv i p) * _root_.Polynomial.C (V i)).coeff 0 =
        MvPolynomial.aeval z (pderiv i p) * V i := by
    rw [mul_comm, _root_.Polynomial.coeff_C_mul]
    rw [coeff_zero_lineEval]
    ring
  simpa only [hterm] using h

/-- The anchored straight-gradient identity supplies the normalized
Hessian-kernel equation, not an additional assumption. -/
theorem anchored_gradient_implies_hessian_kernel
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (z V : Unit ⊕ Fin 3 → F)
    (hgrad : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L))) :
    ∀ i : Unit ⊕ Fin 3,
      ∑ j : Unit ⊕ Fin 3,
        MvPolynomial.aeval z (pderiv j (pderiv i L)) * V j = 0 := by
  intro i
  have h := coeff_one_lineEval_eq_directional z V (pderiv i L)
  have hzero : (lineEval z V (pderiv i L)).coeff 1 = 0 := by
    calc
      (lineEval z V (pderiv i L)).coeff 1 =
          (_root_.Polynomial.C
            (MvPolynomial.aeval z (pderiv i L)) : _root_.Polynomial F).coeff 1 :=
              congrArg (fun q : _root_.Polynomial F => q.coeff 1) (hgrad i)
      _ = 0 := by simp
  rw [hzero] at h
  exact h.symm

end
end HC4.Polynomial.RankThreeCubic
