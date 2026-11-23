import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePoleLowJetSquareOrTriple
import HC4.Polynomial.RankThreeCubicPrincipalAdjugateDirection
import HC4.Polynomial.RankThreeCubicAdjugateRankOneMinors
import Mathlib.Tactic

/-!
# Exact rank-one adjugate normalization by the longitudinal low jet

The single principal square equation from a determinant-one 4x4
source Hessian, together with a nonzero kernel vector of its
singular symmetric transverse 3x3 block T, determines the ENTIRE
adjugate of T.

If T*w=0, det(T)=0, adj(T)[k,k] != 0, w[k] != 0, and
   adj(T)[k,k] * g^2 = -w[k]^2,
then for all i,j,
   g^2 * adj(T)[i,j] = -w[i]*w[j].

The proof is denominator-free. It uses the verified alignment
of a kernel vector with an adjugate column, the 3x3 rank-one
adjugate cross-product identity, and cancellation of the
nonzero pivot and nonzero kernel coordinate.

No source endpoint assumptions or radical extensions are needed.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

/-- The entire adjugate of a singular symmetric three-block is
normalized by one pivot square identity and its kernel vector. -/
theorem symmetricThree_kernel_adjugate_lowJet_normalized
    (T : Matrix (Fin 3) (Fin 3) K)
    (hSym : T.IsSymm)
    (w : Fin 3 → K)
    (hker : T *ᵥ w = 0)
    (hdet : T.det = 0)
    (g : K) (k : Fin 3)
    (hkk : T.adjugate k k ≠ 0)
    (hwk : w k ≠ 0)
    (hsquare : T.adjugate k k * g ^ 2 = -(w k ^ 2)) :
    ∀ i j : Fin 3,
      g ^ 2 * T.adjugate i j = -(w i * w j) := by
  classical
  have hAdjSym : T.adjugate.IsSymm := by
    change T.adjugate.transpose = T.adjugate
    rw [Matrix.adjugate_transpose, hSym]
  have halign : ∀ i : Fin 3,
      T.adjugate k k * w i = T.adjugate i k * w k :=
    principalCofactor_kernelVector_adjugate_proportional
      T w hker hdet k hkk
  have hgs : g ^ 2 * T.adjugate k k = -(w k ^ 2) := by
    calc
      g ^ 2 * T.adjugate k k = T.adjugate k k * g ^ 2 := by ring
      _ = -(w k ^ 2) := hsquare
  intro i j
  have hcross :=
    adjugate_rankOne_cross_products T hdet k i j
  have hscaled :
      T.adjugate k k * (T.adjugate i j * (w k ^ 2)) =
        T.adjugate k k *
          (T.adjugate k k * (w i * w j)) := by
    calc
      _ = (T.adjugate k k * T.adjugate i j) * w k ^ 2 := by ring
      _ = (T.adjugate i k * T.adjugate k j) * w k ^ 2 := by
            rw [hcross]
      _ = (T.adjugate i k * w k) *
          (T.adjugate j k * w k) := by
            rw [hAdjSym.apply k j]
            ring
      _ = (T.adjugate k k * w i) *
          (T.adjugate k k * w j) := by
            rw [halign i, halign j]
      _ = T.adjugate k k *
          (T.adjugate k k * (w i * w j)) := by ring
  have hcof :
      T.adjugate i j * w k ^ 2 =
        T.adjugate k k * (w i * w j) :=
    mul_left_cancel₀ hkk hscaled
  have hresult :
      (w k ^ 2) * (g ^ 2 * T.adjugate i j) =
        (w k ^ 2) * (-(w i * w j)) := by
    calc
      _ = g ^ 2 * (T.adjugate i j * w k ^ 2) := by ring
      _ = g ^ 2 * (T.adjugate k k * (w i * w j)) := by rw [hcof]
      _ = -(w k ^ 2) * (w i * w j) := by rw [← mul_assoc, hgs]
      _ = (w k ^ 2) * (-(w i * w j)) := by ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hwk) hresult

end
end HC4.Polynomial.RankThreeCubic
