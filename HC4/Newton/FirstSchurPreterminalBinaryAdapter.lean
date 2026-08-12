import HC4.Newton.FirstSchurLayerLinearization
import Mathlib.Tactic

/-!
# Preterminal first-Schur departure adapter

This file isolates the exact two-by-two algebra needed after a first
longitudinal/blocker departure has been identified with a first binary Schur
layer.

After straightening the current rank-one Schur line, the old binary block is

    B₀ = [[b, 0],
          [0, 0]],          b ≠ 0.

Write the first new symmetric Hessian layer as

    H = [[h₁₁, h₁₂],
         [h₁₂, h₂₂]].

The coefficient of the determinant which is linear in the new layer is
`b * h₂₂`.  At a genuinely preterminal order that coefficient must still
vanish.  Hence `h₂₂ = 0`.

The determinant of the new binary layer is then exactly `-h₁₂²`.  Therefore
there are only two algebraic possibilities:

* `h₁₂ ≠ 0`: a genuine mixed-curvature departure, with nonzero binary
  determinant source;
* `h₁₂ = 0`: no mixed binary curvature, the affine/separated channel.

No geometric identification of a blocker coefficient with a Schur layer is
assumed here.  This is the small algebraic adapter that such an
identification will consume.
-/

namespace HC4.Newton

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Scalar data for a first new symmetric binary Schur/Hessian layer after
the preceding rank-one block has been diagonalised to `diag(b,0)`.

`detLinear = 0` records that the determinant is still required to vanish at
this order, i.e. that the departure is preterminal rather than the
determinant-closing layer.
-/
structure PreterminalBinaryFirstDeparture where
  b : K
  h11 : K
  h12 : K
  h22 : K
  active_ne_zero : b ≠ 0
  detLinear_zero : b * h22 = 0

/-- The kernel-kernel entry of a preterminal first departure vanishes. -/
theorem PreterminalBinaryFirstDeparture.kernelKernel_zero
    (D : PreterminalBinaryFirstDeparture (K := K)) :
    D.h22 = 0 := by
  rcases mul_eq_zero.mp D.detLinear_zero with hb | h22
  · exact (D.active_ne_zero hb).elim
  · exact h22

/-- The binary determinant of the first new layer, written in scalar form. -/
def PreterminalBinaryFirstDeparture.layerDet
    (D : PreterminalBinaryFirstDeparture (K := K)) : K :=
  D.h11 * D.h22 - D.h12 * D.h12

/-- Once the preterminal linear determinant equation is imposed, the new
binary determinant is exactly minus the square of the mixed entry. -/
theorem PreterminalBinaryFirstDeparture.layerDet_eq_neg_sq
    (D : PreterminalBinaryFirstDeparture (K := K)) :
    D.layerDet = -(D.h12 ^ 2) := by
  rw [PreterminalBinaryFirstDeparture.layerDet, D.kernelKernel_zero]
  ring

/-- A nonzero mixed entry gives a genuinely nonzero binary determinant
source. -/
theorem PreterminalBinaryFirstDeparture.layerDet_ne_zero_of_mixed
    (D : PreterminalBinaryFirstDeparture (K := K))
    (hmixed : D.h12 ≠ 0) :
    D.layerDet ≠ 0 := by
  rw [D.layerDet_eq_neg_sq]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hmixed)

/-- **Preterminal adapter dichotomy.**

At the first preterminal departure there are only two scalar possibilities:

* a genuine mixed-curvature layer, whose binary determinant source is
  nonzero;
* zero mixed curvature together with the already-forced zero
  kernel-kernel entry.

This is the exact algebraic handoff needed by the existing mixed-repair
versus affine/separated classification.
-/
theorem PreterminalBinaryFirstDeparture.mixed_or_affine
    (D : PreterminalBinaryFirstDeparture (K := K)) :
    (D.h12 ≠ 0 ∧ D.layerDet ≠ 0) ∨
      (D.h12 = 0 ∧ D.h22 = 0) := by
  by_cases hmixed : D.h12 = 0
  · exact Or.inr ⟨hmixed, D.kernelKernel_zero⟩
  · exact Or.inl ⟨hmixed, D.layerDet_ne_zero_of_mixed hmixed⟩

/-- Constructor form convenient for a future Schur-linearization adapter:
if the old active coefficient `b` is nonzero and the linear determinant
coefficient `b*h₂₂` vanishes, all of the preterminal conclusions are
available immediately.
-/
theorem preterminalBinaryFirstDeparture_of_linearDet_zero
    (b h11 h12 h22 : K)
    (hb : b ≠ 0)
    (hlin : b * h22 = 0) :
    ∃ D : PreterminalBinaryFirstDeparture (K := K),
      D.b = b ∧
      D.h11 = h11 ∧
      D.h12 = h12 ∧
      D.h22 = h22 ∧
      D.h22 = 0 ∧
      D.layerDet = -(h12 ^ 2) := by
  let D : PreterminalBinaryFirstDeparture (K := K) :=
    {
      b := b
      h11 := h11
      h12 := h12
      h22 := h22
      active_ne_zero := hb
      detLinear_zero := hlin
    }
  refine ⟨D, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact D.kernelKernel_zero
  · simpa [D] using D.layerDet_eq_neg_sq

end

end HC4.Newton
