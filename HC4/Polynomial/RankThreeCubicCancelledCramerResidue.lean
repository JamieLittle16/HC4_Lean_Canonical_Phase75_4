module

public import HC4.Polynomial.RankThreeCubicNormalizedPoleQuadraticResidue
public import Mathlib.Tactic

/-!
# The actual Cramer system after one repeated-pole cancellation

If D = p*s and all entries of the actual Cramer numerator
A = adj(H)*r have a common factor p, write A = p*T. Provided
p is nonzero, the polynomial vector T and denominator s still
represent the very same fractional characteristic V.

This algebraic cancellation supplies the exact Hessian equation
H*T = s*r, hence a genuine kernel modulo p whenever p divides s.

Under the source gradient-transport identity, the previously
proved normalized-residue transport lemma then gives every
quadratic gradient time coefficient on the normalized residue.

The existence of a T with nonzero reduction at p remains the
normalization/extraction obligation, not an assumed conclusion.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicCancelledCramerResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicCancelledCramerResidue

open RankThreeCubicCancelledCramerResidue (B3 F3 SB)

/-- Cancel one nonzero common polynomial factor in the actual Cramer
numerator and determinant without changing the rational solution. -/
theorem cramer_cancel_common_factor_hscale
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r T : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun j => algebraMap (B3 K) (F3 K) (r j))
    (p s : B3 K) (hp0 : p ≠ 0)
    (hdet : H.det = p * s)
    (hA :
      ∀ j : Fin 3, (H.adjugate *ᵥ r) j = p * T j) :
    ∀ j : Fin 3,
      algebraMap (B3 K) (F3 K) (T j) =
        algebraMap (B3 K) (F3 K) s * V j := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hgp : g p ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (B3 K) (F3 K)).ne hp0
  intro j
  have hcramer :=
    fractionKernel_adjugate_numerator_identity H r V hkernel j
  have heq : g p * (g s * V j) = g p * g (T j) := by
    calc
      g p * (g s * V j) = g (p * s) * V j := by rw [map_mul]; ring
      _ = g H.det * V j := by rw [hdet]
      _ = g ((H.adjugate *ᵥ r) j) := hcramer
      _ = g (p * T j) := by rw [hA j]
      _ = g p * g (T j) := map_mul g p (T j)
  exact (mul_left_cancel₀ hgp heq).symm

/-- Any normalized polynomial representation of a fractional Hessian
solution still satisfies the cleared Hessian equation H*T = s*r. -/
theorem normalized_fractionKernel_cleared
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (r T : Fin 3 → B3 K)
    (V : Fin 3 → F3 K)
    (hkernel :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ V =
        fun j => algebraMap (B3 K) (F3 K) (r j))
    (s : B3 K)
    (hscale :
      ∀ j : Fin 3,
        algebraMap (B3 K) (F3 K) (T j) =
          algebraMap (B3 K) (F3 K) s * V j) :
    H *ᵥ T = s • r := by
  classical
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hinj : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  funext j
  apply hinj
  change g ((H *ᵥ T) j) = g (s * r j)
  calc
    g ((H *ᵥ T) j) = ∑ k : Fin 3, g (H j k) * g (T k) := by
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    _ = ∑ k : Fin 3, g (H j k) * (g s * V k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hscale k]
    _ = g s * (∑ k : Fin 3, g (H j k) * V k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = g s * g (r j) := by
      have hk := congrFun hkernel j
      change (∑ k : Fin 3, g (H j k) * V k) = g (r j) at hk
      rw [hk]
    _ = g (s * r j) := (map_mul g s (r j)).symm

/-- Source-honest coefficientwise normalized repeated-pole residue.
The only normalization data required are the exact common-factor
division A = p*T and a nonzero coordinate of T modulo p. -/
theorem sourceCubic_cancelledCramer_nonzeroResidue
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (p s : B3 K)
    (hp : Irreducible p)
    (hdet : (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det = p * s)
    (hps : p ∣ s)
    (T : Fin 3 → B3 K)
    (hA : ∀ j : Fin 3,
      ((sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate *ᵥ
        sourceNegativeMixedHessian a
          (initialForm transverseCubicWeight 3 F)) j = p * T j)
    (hTnz : ∃ j : Fin 3, ¬ p ∣ T j) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (T j)
    S ≠ 0 ∧
    (H.map q) *ᵥ S = 0 ∧
    (∀ i : Fin 3,
      ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
        (∀ j k : Fin 3,
          (Q j k).map (algebraMap (B3 K) (F3 K)) =
            lineEval (transverseGenericPoint a) V
              (pderiv (.inr k) (pderiv (.inr j)
                (pderiv (.inr i) L)))) ∧
        (∀ n : ℕ,
          (∑ j : Fin 3, ∑ k : Fin 3,
            q ((Q j k).coeff n) * S j * S k) = 0)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) := fun j => q (T j)
  have hker :
      (H.map g) *ᵥ (fun j : Fin 3 => V (.inr j)) =
        fun j : Fin 3 => g (r j) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  have hscale : ∀ j : Fin 3, g (T j) = g s * V (.inr j) :=
    cramer_cancel_common_factor_hscale
      H r T (fun j : Fin 3 => V (.inr j)) hker
      p s hp.ne_zero hdet hA
  have hcleared : H *ᵥ T = s • r :=
    normalized_fractionKernel_cleared H r T
      (fun j : Fin 3 => V (.inr j)) hker s hscale
  have hqzero : q s = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hps)
  obtain ⟨j, hTj⟩ := hTnz
  have hSj : S j ≠ 0 := by
    intro hz
    exact hTj
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hS : S ≠ 0 := by
    intro hz
    exact hSj (by simpa using congrFun hz j)
  have hSker : (H.map q) *ᵥ S = 0 := by
    funext j
    change (∑ k : Fin 3, q (H j k) * q (T k)) = 0
    calc
      _ = q ((H *ᵥ T) j) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      _ = q (s * r j) := by rw [hcleared]; rfl
      _ = 0 := by rw [map_mul, hqzero, zero_mul]
  refine ⟨hS, hSker, ?_⟩
  intro i
  exact sourceCubic_normalizedPole_quadraticResidue_coefficients
    F a V hV hgrad p s hp hps T hscale i

end
end HC4.Polynomial.RankThreeCubic
