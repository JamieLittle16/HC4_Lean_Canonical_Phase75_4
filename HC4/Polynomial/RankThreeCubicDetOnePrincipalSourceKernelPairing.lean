import HC4.Polynomial.RankThreeCubicDetOnePrincipalSchurKernelCoupling
import Mathlib.Tactic

/-!
# The principal Schur coupling is the actual longitudinal source pairing

For an arbitrary symmetric 4x4 matrix B on Unit ⊕ Fin3, let
T be its transverse 3x3 block and w a vector killed by T.

Reindex the original B in the principal chart of index k.
The active Schur determinant times the original longitudinal
pairing B[x,y]·w equals the mixed cleared Schur entry times w[k].

This equality is polynomial in the entries of B. In particular,
it does not assume a nonzero principal minor, or invert that
minor; it is valid over a field even for degenerate charts.

The proof transports two original transverse kernel rows to
the exact GeneralFourBlock formula and uses the mixed-partial
symmetry of B to identify the longitudinal pairing.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- The denominator-cleared mixed Schur entry in a principal
source chart is the original longitudinal response along
a transverse kernel direction, multiplied by the active minor. -/
theorem principalSourceFourBlock_schurB_kernelPairing
    (B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K)
    (hB : B.IsSymm)
    (w : Fin 3 → K)
    (hrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B (.inr i) (.inr j) * w j) = 0)
    (k : Fin 3) :
    let H := principalSourceFourBlock B k
    H.activeDet *
      (∑ j : Fin 3, B (.inl ()) (.inr j) * w j) =
        H.schurB * w k := by
  classical
  let H := principalSourceFourBlock B k
  let i0 : Fin 3 := k.succAbove 0
  let i1 : Fin 3 := k.succAbove 1
  have hi0 :
      B (.inr i0) (.inr i0) * w i0 +
        B (.inr i0) (.inr i1) * w i1 +
          B (.inr i0) (.inr k) * w k = 0 := by
    have hi := hrows i0
    rw [Fin.sum_univ_succAbove
      (fun j : Fin 3 => B (.inr i0) (.inr j) * w j) k] at hi
    simp only [Fin.sum_univ_two] at hi
    convert hi using 1 <;> ring
  have hi1 :
      B (.inr i0) (.inr i1) * w i0 +
        B (.inr i1) (.inr i1) * w i1 +
          B (.inr i1) (.inr k) * w k = 0 := by
    have hi := hrows i1
    rw [Fin.sum_univ_succAbove
      (fun j : Fin 3 => B (.inr i1) (.inr j) * w j) k] at hi
    simp only [Fin.sum_univ_two] at hi
    rw [hB.apply (.inr i0) (.inr i1)] at hi
    convert hi using 1 <;> ring
  have h0 : H.a * w i0 + H.b * w i1 + H.q * w k = 0 := by
    change
      B (.inr i0) (.inr i0) * w i0 +
        B (.inr i0) (.inr i1) * w i1 +
          B (.inr i0) (.inr k) * w k = 0
    exact hi0
  have h1 : H.b * w i0 + H.d * w i1 + H.s * w k = 0 := by
    change
      B (.inr i0) (.inr i1) * w i0 +
        B (.inr i1) (.inr i1) * w i1 +
          B (.inr i1) (.inr k) * w k = 0
    exact hi1
  have hlong :
      (∑ j : Fin 3, B (.inl ()) (.inr j) * w j) =
        H.p * w i0 + H.r * w i1 + H.y * w k := by
    rw [Fin.sum_univ_succAbove
      (fun j : Fin 3 => B (.inl ()) (.inr j) * w j) k]
    simp only [Fin.sum_univ_two]
    have h0sym : B (.inl ()) (.inr i0) =
        B (.inr i0) (.inl ()) := hB.apply (.inr i0) (.inl ())
    have h1sym : B (.inl ()) (.inr i1) =
        B (.inr i1) (.inl ()) := hB.apply (.inr i1) (.inl ())
    change
      B (.inl ()) (.inr k) * w k +
        (B (.inl ()) (.inr i0) * w i0 +
          B (.inl ()) (.inr i1) * w i1) =
      B (.inr i0) (.inl ()) * w i0 +
        B (.inr i1) (.inl ()) * w i1 +
          B (.inl ()) (.inr k) * w k
    rw [h0sym, h1sym]
    ring
  calc
    H.activeDet *
        (∑ j : Fin 3, B (.inl ()) (.inr j) * w j) =
      H.activeDet * (H.p * w i0 + H.r * w i1 + H.y * w k) := by
        rw [hlong]
    _ = H.schurB * w k :=
      principalSchur_kernelPairing_identity H (w i0) (w i1) (w k) h0 h1

end
end HC4.Polynomial.RankThreeCubic
