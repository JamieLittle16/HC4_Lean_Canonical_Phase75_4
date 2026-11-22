import HC4.Polynomial.RankThreeCubicFixedTangentFrameCompletion
import Mathlib.Tactic

/-!
# Sharpness audit: cubic source gradient transport can have a genuine double pole

This is a diagnostic finite calculation, **not** an HC4 counterexample.

Over characteristic zero, consider the honest polynomial

  F(x,z,u,v) = z^2*v/2 + (u-x*z)^3/6.

Its four formal partial derivatives, in (x,z,u,v) order, are

  (-z*(u-x*z)^2/2,
    z*v-x*(u-x*z)^2/2,
    (u-x*z)^2/2,
    z^2/2).

At longitudinal anchor x=0 its transverse Hessian is

  [v 0 z; 0 u 0; z 0 0]

with determinant -u*z^2. The entire four-variable Hessian has
identically zero determinant, so this is NOT a determinant-one
source or a counterexample to the target HC4 theorem.

Nevertheless its *entire* four-component gradient is constant along
the straight characteristic with velocity (1,0,z,u^2/(2*z)).
Thus fixed tangent kernel, rank two on the generic pole plane,
an exactly double factor, and full cubic gradient transport do
NOT alone imply that the rational velocity is polynomial.

The next source closure must use information beyond the cubic face's
gradient transport, such as its compatibility with the lower source
layers and the original determinant-one hypothesis.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

/-- The explicit four formal partial-derivative expressions for the
source polynomial z²v/2+(u-xz)³/6. -/
def cubicPoleToyGradient
    {K : Type*} [Field K]
    (x z u v : K) : Fin 4 → K :=
  ![-z * (u - x * z) ^ 2 / 2,
      z * v - x * (u - x * z) ^ 2 / 2,
      (u - x * z) ^ 2 / 2,
      z ^ 2 / 2]

/-- The transported gradient is constant for the rational
velocity with the cleared relation 2*z*w=u². By stating the
cleared relation, no localization or denominator assumptions
are hidden inside the algebraic transport certificate. -/
theorem cubicPoleToyGradient_transport
    {K : Type*} [Field K] [CharZero K]
    (z u v t w : K)
    (hw : 2 * z * w = u ^ 2) :
    cubicPoleToyGradient t z (u + t * z) (v + t * w) =
      cubicPoleToyGradient 0 z u v := by
  have hshift : u + t * z - t * z = u := by ring
  have hzw : z * w = u ^ 2 / 2 := by
    linear_combination (1 / 2 : K) * hw
  ext i
  fin_cases i <;>
    simp [cubicPoleToyGradient, hshift, hzw] <;> ring

/-- For z ≠ 0 this is exactly the rational source characteristic,
not a merely formal new velocity. -/
theorem cubicPoleToyGradient_transport_fraction
    {K : Type*} [Field K] [CharZero K]
    (z u v t : K) (hz : z ≠ 0) :
    cubicPoleToyGradient t z (u + t * z)
        (v + t * (u ^ 2 / (2 * z))) =
      cubicPoleToyGradient 0 z u v := by
  apply cubicPoleToyGradient_transport
  field_simp [hz]
  ring

/-- The transverse Hessian at longitudinal anchor x=0. -/
def cubicPoleToyHessian
    {K : Type*} [CommRing K]
    (z u v : K) : Matrix (Fin 3) (Fin 3) K :=
  ![![v, 0, z], ![0, u, 0], ![z, 0, 0]]

/-- The repeated factor is exactly a square in the normal
coordinate, with a nontrivial linear transverse cofactor. -/
theorem cubicPoleToyHessian_det
    {K : Type*} [CommRing K]
    (z u v : K) :
    (cubicPoleToyHessian z u v).det = -(u * z ^ 2) := by
  simp [cubicPoleToyHessian, Matrix.det_fin_three]
  ring

/-- The displayed rational velocity component cannot arise from
a polynomial solution of 2*Z*P=U²: evaluating Z=0, U=1
would equate zero and one. -/
theorem cubicPoleToyVelocity_nonPolynomial
    {K : Type*} [Field K] [CharZero K]
    (P : MvPolynomial (Fin 3) K)
    (hP : (2 : MvPolynomial (Fin 3) K) *
      (MvPolynomial.X 0) * P = (MvPolynomial.X 1) ^ 2) :
    False := by
  let ev : MvPolynomial (Fin 3) K →+* K :=
    (MvPolynomial.aeval ![(0 : K), 1, 0]).toRingHom
  have h := congrArg ev hP
  simp [ev] at h

end
end HC4.Polynomial.RankThreeCubic
