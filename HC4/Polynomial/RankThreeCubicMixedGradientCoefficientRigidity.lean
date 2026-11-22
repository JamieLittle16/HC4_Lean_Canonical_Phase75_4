import Mathlib.Tactic

/-!
# Finite coefficient rigidity for a cubic mixed-gradient source

After choosing adapted coordinates (z,u,v) with constant
Hessian kernel e_v, the self-quadratic transport forces
the other components of the rational velocity to vanish
in the exactly-double case.

The remaining transverse Hessian equation then forces the
u- and v-derivatives of the *longitudinal derivative*
of the source cubic to vanish. If that cubic has coefficients

  A z³ + B z²u + C z²v + D zu² + E zuv + F zv²
         + G u³ + H u²v + I uv² + J v³,

its mixed-gradient vector therefore has no u or v component,
which forces B=C=D=E=F=0. Consequently the remaining
normal derivative is exactly 3A z²: a multiple of z².

The theorem below is the finite algebraic coefficient
certificate. Its arguments are the two explicit
tangential gradient identities, not an assumption that
the normal gradient has this form.
-/

namespace HC4.Polynomial.RankThreeCubic

noncomputable section

/-- The two vanishing tangential cubic-gradient components
force the normal gradient to be a square of the normal
coordinate. This is an explicit finite algebra calculation. -/
theorem homogeneousCubic_twoTangentialGradientZero_normalDerivative
    {K : Type*} [Field K] [CharZero K]
    (A B C D E F G H I J : K)
    (hU : ∀ z u v : K,
      B * z ^ 2 + 2 * D * z * u + E * z * v +
        3 * G * u ^ 2 + 2 * H * u * v + I * v ^ 2 = 0)
    (hV : ∀ z u v : K,
      C * z ^ 2 + E * z * u + 2 * F * z * v +
        H * u ^ 2 + 2 * I * u * v + 3 * J * v ^ 2 = 0) :
    ∀ z u v : K,
      3 * A * z ^ 2 + 2 * B * z * u + 2 * C * z * v +
          D * u ^ 2 + E * u * v + F * v ^ 2 =
        3 * A * z ^ 2 := by
  have hB : B = 0 := by
    simpa using hU 1 0 0
  have hC : C = 0 := by
    simpa using hV 1 0 0
  have hD : D = 0 := by
    have h1 := hU 1 1 0
    have h2 := hU 0 1 0
    have h3 := hU 1 0 0
    have hd2 : (2 : K) * D = 0 := by
      linear_combination h1 - h2 - h3
    exact (mul_eq_zero.mp hd2).resolve_left (by norm_num)
  have hE : E = 0 := by
    have h1 := hU 1 0 1
    have h2 := hU 0 0 1
    have h3 := hU 1 0 0
    linear_combination h1 - h2 - h3
  have hF : F = 0 := by
    have h1 := hV 1 0 1
    have h2 := hV 0 0 1
    have h3 := hV 1 0 0
    have hf2 : (2 : K) * F = 0 := by
      linear_combination h1 - h2 - h3
    exact (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  intro z u v
  simp [hB, hC, hD, hE, hF]

end
end HC4.Polynomial.RankThreeCubic
