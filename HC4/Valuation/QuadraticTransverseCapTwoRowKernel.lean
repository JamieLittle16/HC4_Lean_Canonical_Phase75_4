import HC4.Valuation.QuadraticTransverseCapRankTwoKernelDrift
import Mathlib.Tactic

/-!
# Exact two-row kernel-line identity for the quadratic transverse cap

The actual quadratic first layer has a finite principal transverse Hessian
pivot. Once its source-honest polynomial active 2x2 determinant is nonzero,
any two polynomial kernel vectors of the first two transverse Hessian rows
are parallel. This uses no localization and works over an integral domain.

For rank-two quadratic closure the two vectors are
  w = adj(C)b'  and  w' = derivative(w).
The latter satisfies the same two row equations after differentiating
Cw=0 and using C'w=0, which are still source-adapter obligations.

These are exact polynomial identities, not a rank-state repair.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/-- Over a domain, an active principal 2x2 pivot makes the solution space
of the first two rows of a symmetric 2x3 system at most one-dimensional.
All three wedge coordinates vanish, without passing to a fraction field. -/
theorem quadraticTransverse_twoRowPrincipalKernel_wedges
    (a b c d e : R)
    (w z : Fin 3 → R)
    (hdelta : a * d - b * b ≠ 0)
    (hw0 : a * w 0 + b * w 1 + c * w 2 = 0)
    (hw1 : b * w 0 + d * w 1 + e * w 2 = 0)
    (hz0 : a * z 0 + b * z 1 + c * z 2 = 0)
    (hz1 : b * z 0 + d * z 1 + e * z 2 = 0) :
    (w 0 * z 1 - w 1 * z 0 = 0) ∧
    (w 0 * z 2 - w 2 * z 0 = 0) ∧
    (w 1 * z 2 - w 2 * z 1 = 0) := by
  let delta : R := a * d - b * b
  let u : R := b * e - c * d
  let v : R := b * c - a * e
  have hd : delta ≠ 0 := hdelta
  have hwzero : delta * w 0 = u * w 2 := by
    dsimp [delta, u]
    linear_combination d * hw0 - b * hw1
  have hwone : delta * w 1 = v * w 2 := by
    dsimp [delta, v]
    linear_combination a * hw1 - b * hw0
  have hzzero : delta * z 0 = u * z 2 := by
    dsimp [delta, u]
    linear_combination d * hz0 - b * hz1
  have hzone : delta * z 1 = v * z 2 := by
    dsimp [delta, v]
    linear_combination a * hz1 - b * hz0
  have h02mul : delta * (w 0 * z 2 - w 2 * z 0) = 0 := by
    calc
      delta * (w 0 * z 2 - w 2 * z 0) =
          (delta * w 0) * z 2 - w 2 * (delta * z 0) := by ring
      _ = (u * w 2) * z 2 - w 2 * (u * z 2) := by
          rw [hwzero, hzzero]
      _ = 0 := by ring
  have h12mul : delta * (w 1 * z 2 - w 2 * z 1) = 0 := by
    calc
      delta * (w 1 * z 2 - w 2 * z 1) =
          (delta * w 1) * z 2 - w 2 * (delta * z 1) := by ring
      _ = (v * w 2) * z 2 - w 2 * (v * z 2) := by
          rw [hwone, hzone]
      _ = 0 := by ring
  have h01mul :
      (delta * delta) * (w 0 * z 1 - w 1 * z 0) = 0 := by
    calc
      (delta * delta) * (w 0 * z 1 - w 1 * z 0) =
          (delta * w 0) * (delta * z 1) -
            (delta * w 1) * (delta * z 0) := by ring
      _ = (u * w 2) * (v * z 2) -
            (v * w 2) * (u * z 2) := by
            rw [hwzero, hzone, hwone, hzzero]
      _ = 0 := by ring
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp h01mul).resolve_left (mul_ne_zero hd hd)
  · exact (mul_eq_zero.mp h02mul).resolve_left hd
  · exact (mul_eq_zero.mp h12mul).resolve_left hd

end

end HC4.Valuation
