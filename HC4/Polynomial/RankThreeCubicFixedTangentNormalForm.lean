import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Fixed-tangent cubic Hessian: explicit five-parameter model

In coordinates (z,u,v) with repeated-pole plane z=0 and
the fixed *full* tangent kernel along the plane given by
e_v=(0,0,1), a completely symmetric cubic Hessian tensor
must have the five-parameter form

  H(z,u,v) =
    [a*z+b*u+c*v, b*z+m*u, c*z]
    [b*z+m*u,     m*z+n*u, 0  ]
    [c*z,         0,       0  ].

Its determinant is -c² z² (m*z+n*u).
Thus generic nonsingularity gives c != 0 and the genuinely
double case, as opposed to a triple normal factor, has n != 0.

For that exactly-double model, the fully symmetric quadratic
transport equations D_i(V,V)=0 force V_z=V_u=0. The only
possible velocity direction is the constant tangent kernel e_v.

These are algebraic normal-form facts, not yet a source theorem.
The remaining geometry must choose this tangent basis in the
actual adapted frame, and the source mixed-gradient equation
must then show that its scalar velocity is polynomial.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- Symmetric ternary cubic tensor of the fixed-tangent
kernel normal form. The first index is the Hessian pencil
variable, and the last two are matrix indices. -/
def cubicFixedTangentTensor
    {K : Type*} [CommRing K]
    (a b c m n : K) : Fin 3 → Fin 3 → Fin 3 → K :=
  ![
    ![![a, b, c], ![b, m, 0], ![c, 0, 0]],
    ![![b, m, 0], ![m, n, 0], ![0, 0, 0]],
    ![![c, 0, 0], ![0, 0, 0], ![0, 0, 0]]
  ]

/-- Corresponding linear homogeneous Hessian matrix. -/
def cubicFixedTangentHessian
    {K : Type*} [CommRing K]
    (a b c m n z u v : K) : Matrix (Fin 3) (Fin 3) K :=
  ![
    ![a * z + b * u + c * v, b * z + m * u, c * z],
    ![b * z + m * u, m * z + n * u, 0],
    ![c * z, 0, 0]
  ]

theorem cubicFixedTangentTensor_hessian
    {K : Type*} [CommRing K]
    (a b c m n z u v : K) :
    cubicTensorHessianAt (cubicFixedTangentTensor a b c m n) ![z, u, v] =
      cubicFixedTangentHessian a b c m n z u v := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicTensorHessianAt, cubicFixedTangentTensor,
      cubicFixedTangentHessian, Fin.sum_univ_three] <;> ring

/-- The exact Hessian determinant, exposing the normal factor
of multiplicity two and the residual linear factor. -/
theorem cubicFixedTangentHessian_det
    {K : Type*} [CommRing K]
    (a b c m n z u v : K) :
    (cubicFixedTangentHessian a b c m n z u v).det =
      -(c ^ 2) * z ^ 2 * (m * z + n * u) := by
  simp [cubicFixedTangentHessian, Matrix.det_fin_three]
  ring

/-- The v-component of the symmetric tensor's quadratic
contraction is simply c times the square of the normal
velocity component. -/
theorem cubicFixedTangentTensor_quadratic_two
    {K : Type*} [CommRing K]
    (a b c m n : K) (V : Fin 3 → K) :
    (∑ l : Fin 3, ∑ j : Fin 3,
      cubicFixedTangentTensor a b c m n 2 l j * V l * V j) =
        c * (V 0) ^ 2 := by
  classical
  simp [cubicFixedTangentTensor, Fin.sum_univ_three]
  ring

/-- After the normal component vanishes, the u-component
of the quadratic contraction is n times the square of
the second velocity component. -/
theorem cubicFixedTangentTensor_quadratic_one_of_normal_zero
    {K : Type*} [CommRing K]
    (a b c m n : K) (V : Fin 3 → K)
    (h0 : V 0 = 0) :
    (∑ l : Fin 3, ∑ j : Fin 3,
      cubicFixedTangentTensor a b c m n 1 l j * V l * V j) =
        n * (V 1) ^ 2 := by
  classical
  simp [cubicFixedTangentTensor, Fin.sum_univ_three, h0]
  ring

/-- The two source-style quadratic transport equations force
the velocity entirely along e_v when the residual factor
is transverse (n != 0) and the normal coupling c != 0. -/
theorem cubicFixedTangentTensor_isotropy_forces_fixed_direction
    {K : Type*} [Field K]
    (a b c m n : K)
    (hc : c ≠ 0) (hn : n ≠ 0)
    (V : Fin 3 → K)
    (hquad : ∀ i : Fin 3,
      (∑ l : Fin 3, ∑ j : Fin 3,
        cubicFixedTangentTensor a b c m n i l j * V l * V j) = 0) :
    V 0 = 0 ∧ V 1 = 0 := by
  have h0 : c * (V 0) ^ 2 = 0 := by
    simpa only [cubicFixedTangentTensor_quadratic_two] using hquad 2
  have hv0 : (V 0) ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_left hc
  have hV0 : V 0 = 0 := (pow_eq_zero hv0)
  have h1 : n * (V 1) ^ 2 = 0 := by
    simpa only [cubicFixedTangentTensor_quadratic_one_of_normal_zero a b c m n V hV0]
      using hquad 1
  have hv1 : (V 1) ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left hn
  exact ⟨hV0, pow_eq_zero hv1⟩

end
end HC4.Polynomial.RankThreeCubic
