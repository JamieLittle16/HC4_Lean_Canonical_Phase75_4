import HC4.Polynomial.RankThreeCubicDetOneSourcePrincipalSchurSquare
import Mathlib.Tactic

/-!
# A denominator-free Schur coupling identity for a fixed transverse kernel

In the symmetric 2+2 chart
   [ a b | p q ]
   [ b d | r s ]
   [ p r | x y ]
   [ q s | y z ],
suppose w = (u, v, t) lies in the kernel of the transverse
3x3 block on coordinate indices 0,1,3.

Writing Δ = a*d-b², the first two kernel equations give
  Δ*(p*u + r*v + y*t) = schurB*t.

The proof is a polynomial identity, valid over any commutative ring:
no inverses, nonzero hypotheses, or rank assumptions. It identifies
the previously established Schur coupling with the longitudinal
response along the actual kernel vector.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
noncomputable section

variable {R : Type*} [CommRing R]

/-- A transverse kernel's longitudinal response is exactly the
cleared mixed Schur coefficient times its final coordinate. -/
theorem principalSchur_kernelPairing_identity
    (H : GeneralFourBlock R) (u v t : R)
    (h0 : H.a * u + H.b * v + H.q * t = 0)
    (h1 : H.b * u + H.d * v + H.s * t = 0) :
    H.activeDet * (H.p * u + H.r * v + H.y * t) =
      H.schurB * t := by
  have halg :
      H.activeDet * (H.p * u + H.r * v + H.y * t) -
          H.schurB * t =
        (H.d * H.p - H.b * H.r) *
            (H.a * u + H.b * v + H.q * t) +
          (H.a * H.r - H.b * H.p) *
            (H.b * u + H.d * v + H.s * t) := by
    unfold GeneralFourBlock.activeDet GeneralFourBlock.schurB
    ring
  rw [h0, h1] at halg
  simp only [mul_zero, add_zero] at halg
  exact sub_eq_zero.mp halg

/-- Under det=1 and zero final cleared diagonal, the fixed kernel
direction and longitudinal response satisfy a precise square relation.

This statement remains denominator-free. The active pivot must be
nonzero only to cancel a factor in the last step. -/
theorem detOne_principalSchur_kernelPairing_square
    (H : GeneralFourBlock R) (u v t : R)
    (hdet : H.determinantCore = 1)
    (hzero : H.schurC = 0)
    (hpivot : H.activeDet ≠ 0)
    (h0 : H.a * u + H.b * v + H.q * t = 0)
    (h1 : H.b * u + H.d * v + H.s * t = 0) :
    H.activeDet * (H.p * u + H.r * v + H.y * t) ^ 2 =
      -(t ^ 2) := by
  have hrel :=
    principalSchur_kernelPairing_identity H u v t h0 h1
  have hsq :=
    detOne_principalSchur_lastZero_couplingSquare H hdet hzero
  have hprod :
      H.activeDet ^ 2 * (H.p * u + H.r * v + H.y * t) ^ 2 =
        -H.activeDet * t ^ 2 := by
    calc
      H.activeDet ^ 2 * (H.p * u + H.r * v + H.y * t) ^ 2 =
        (H.activeDet * (H.p * u + H.r * v + H.y * t)) ^ 2 := by ring
      _ = (H.schurB * t) ^ 2 := by rw [hrel]
      _ = -H.activeDet * t ^ 2 := by rw [mul_pow, hsq]; ring
  have hcancel :
      H.activeDet * (H.activeDet * (H.p * u + H.r * v + H.y * t) ^ 2) =
        H.activeDet * (-(t ^ 2)) := by
    calc
      _ = H.activeDet ^ 2 * (H.p * u + H.r * v + H.y * t) ^ 2 := by ring
      _ = -H.activeDet * t ^ 2 := hprod
      _ = H.activeDet * (-(t ^ 2)) := by ring
  exact mul_left_cancel₀ hpivot hcancel

end
end HC4.Polynomial.RankThreeCubic
