import HC4.Newton.TerminalCollision
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Action
import Mathlib.Tactic

/-!
# Linear covariance for the valuation restart

This file isolates the coordinate-change identities needed by the global
restart proof.

For a square matrix `D` and Hessian matrix `H`, the transformed Hessian is

    Dᵀ H D.

Its determinant is

    det(D)^2 det(H).

In four variables, after the conformal normalisation by a scalar `mu⁻¹`,
the determinant acquires the factor

    mu⁻⁴ det(D)^2.

Hence a conformal relation `det(D)^2 = mu^4` preserves determinant one
exactly.

The second half packages the corresponding evaluated-gradient covariance
at the function level.  It deliberately separates two issues:

* this file proves that the covariance formula transports an exact
  collision;
* a later polynomial substitution/kernel-blow-up file must prove that the
  concrete transformed polynomial really has that covariance formula.

Thus no global restart hypothesis is hidden here.
-/

namespace HC4.Valuation

noncomputable section

open Matrix

variable {K : Type*} [Field K]

/-! ## Hessian congruence -/

/-- Matrix congruence appearing in the Hessian chain rule under a linear
change of variables. -/
def hessianCongruence
    (D H : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  D.transpose * H * D

/-- Exact determinant scaling under Hessian congruence. -/
theorem det_hessianCongruence
    (D H : Matrix (Fin 4) (Fin 4) K) :
    (hessianCongruence D H).det =
      D.det ^ 2 * H.det := by
  simp [hessianCongruence, Matrix.det_mul, pow_two]
  ring

/-- If the coordinate matrix has determinant one, Hessian determinant is
preserved. -/
theorem det_hessianCongruence_of_det_one
    (D H : Matrix (Fin 4) (Fin 4) K)
    (hD : D.det = 1) :
    (hessianCongruence D H).det = H.det := by
  rw [det_hessianCongruence, hD]
  ring

/-- Conformally normalised Hessian congruence in four variables. -/
def normalizedHessianCongruence
    (mu : K)
    (D H : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  mu⁻¹ • hessianCongruence D H

/-- Determinant formula for the normalised four-dimensional congruence. -/
theorem det_normalizedHessianCongruence
    (mu : K)
    (D H : Matrix (Fin 4) (Fin 4) K) :
    (normalizedHessianCongruence mu D H).det =
      (mu⁻¹) ^ 4 * (D.det ^ 2 * H.det) := by
  rw [normalizedHessianCongruence, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [det_hessianCongruence]

/-- **Exact conformal Hessian covariance in dimension four.**

If `mu ≠ 0` and `det(D)^2 = mu^4`, the normalised congruence preserves the
Hessian determinant exactly. -/
theorem det_normalizedHessianCongruence_of_conformal
    (mu : K)
    (D H : Matrix (Fin 4) (Fin 4) K)
    (hmu : mu ≠ 0)
    (hconf : D.det ^ 2 = mu ^ 4) :
    (normalizedHessianCongruence mu D H).det =
      H.det := by
  rw [det_normalizedHessianCongruence, hconf]
  field_simp

/-- In particular determinant one remains determinant one. -/
theorem normalizedHessianCongruence_det_one
    (mu : K)
    (D H : Matrix (Fin 4) (Fin 4) K)
    (hmu : mu ≠ 0)
    (hconf : D.det ^ 2 = mu ^ 4)
    (hH : H.det = 1) :
    (normalizedHessianCongruence mu D H).det = 1 := by
  rw [det_normalizedHessianCongruence_of_conformal
    mu D H hmu hconf, hH]

/-! ## Evaluated-gradient covariance -/

/-- Pull back an arbitrary vector-valued map by the linear covariance
formula occurring for gradients:

    x ↦ Dᵀ G(Dx).
-/
def linearGradientPullback
    (D : Matrix (Fin 4) (Fin 4) K)
    (G : (Fin 4 -> K) -> (Fin 4 -> K)) :
    (Fin 4 -> K) -> (Fin 4 -> K) :=
  fun x =>
    D.transpose.mulVec (G (D.mulVec x))

/-- Equality of the original vector-valued map at the transformed points
is transported automatically by the gradient pullback. -/
theorem linearGradientPullback_eq_of_eq
    (D : Matrix (Fin 4) (Fin 4) K)
    (G : (Fin 4 -> K) -> (Fin 4 -> K))
    (p q : Fin 4 -> K)
    (h :
      G (D.mulVec p) =
        G (D.mulVec q)) :
    linearGradientPullback D G p =
      linearGradientPullback D G q := by
  unfold linearGradientPullback
  rw [h]

/-- Conformally normalised gradient pullback:

    x ↦ mu⁻¹ Dᵀ G(Dx).
-/
def normalizedLinearGradientPullback
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (G : (Fin 4 -> K) -> (Fin 4 -> K)) :
    (Fin 4 -> K) -> (Fin 4 -> K) :=
  fun x =>
    mu⁻¹ •
      D.transpose.mulVec (G (D.mulVec x))

/-- Exact collisions are preserved by the normalised gradient pullback. -/
theorem normalizedLinearGradientPullback_eq_of_eq
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (G : (Fin 4 -> K) -> (Fin 4 -> K))
    (p q : Fin 4 -> K)
    (h :
      G (D.mulVec p) =
        G (D.mulVec q)) :
    normalizedLinearGradientPullback mu D G p =
      normalizedLinearGradientPullback mu D G q := by
  unfold normalizedLinearGradientPullback
  rw [h]

/-! ## Exact polynomial collision transport -/

/-- A transformed polynomial has the expected normalised linear gradient
covariance with respect to `F`.  The later substitution/kernel-blow-up file
will prove this predicate for its concrete polynomial transform. -/
def HasNormalizedGradientCovariance
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (F P : MvPolynomial (Fin 4) K) : Prop :=
  HC4.Newton.mvGradientMap P =
    normalizedLinearGradientPullback
      mu D (HC4.Newton.mvGradientMap F)

/-- **Collision transport from exact gradient covariance.**

If `P` satisfies the concrete normalised covariance formula and `F` has an
exact collision at the transformed pair `Dp,Dq`, then `P` has an exact
collision at `p,q`.

This theorem does not assume invertibility of `D`: only equality of the
two original gradients is needed. -/
theorem exactGradientCollision_of_normalizedGradientCovariance
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (F P : MvPolynomial (Fin 4) K)
    (p q : Fin 4 -> K)
    (hcov :
      HasNormalizedGradientCovariance
        mu D F P)
    (hcoll :
      HC4.Newton.HasExactGradientCollision
        F (D.mulVec p) (D.mulVec q)) :
    HC4.Newton.HasExactGradientCollision
      P p q := by
  have hF :
      HC4.Newton.mvGradientMap F (D.mulVec p) =
        HC4.Newton.mvGradientMap F (D.mulVec q) :=
    HC4.Newton.mvGradientMap_eq_of_exactCollision
      F (D.mulVec p) (D.mulVec q) hcoll
  have hpull :
      normalizedLinearGradientPullback
          mu D (HC4.Newton.mvGradientMap F) p =
        normalizedLinearGradientPullback
          mu D (HC4.Newton.mvGradientMap F) q :=
    normalizedLinearGradientPullback_eq_of_eq
      mu D (HC4.Newton.mvGradientMap F) p q hF
  have hP :
      HC4.Newton.mvGradientMap P p =
        HC4.Newton.mvGradientMap P q := by
    rw [hcov]
    exact hpull
  intro i
  exact congrFun hP i

/-- Distinctness of the transformed original points immediately implies
distinctness of the new points. -/
theorem points_ne_of_mulVec_ne
    (D : Matrix (Fin 4) (Fin 4) K)
    (p q : Fin 4 -> K)
    (hneq : D.mulVec p ≠ D.mulVec q) :
    p ≠ q := by
  intro hpq
  exact hneq (congrArg (fun x => D.mulVec x) hpq)

/-- Full pointed collision-transport package. -/
theorem distinctExactGradientCollision_of_normalizedGradientCovariance
    (mu : K)
    (D : Matrix (Fin 4) (Fin 4) K)
    (F P : MvPolynomial (Fin 4) K)
    (p q : Fin 4 -> K)
    (hcov :
      HasNormalizedGradientCovariance
        mu D F P)
    (hneq :
      D.mulVec p ≠ D.mulVec q)
    (hcoll :
      HC4.Newton.HasExactGradientCollision
        F (D.mulVec p) (D.mulVec q)) :
    p ≠ q ∧
      HC4.Newton.HasExactGradientCollision
        P p q := by
  exact
    ⟨points_ne_of_mulVec_ne D p q hneq,
      exactGradientCollision_of_normalizedGradientCovariance
        mu D F P p q hcov hcoll⟩

end

end HC4.Valuation
