import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# A linear combined Smith/degree exposure

On the symmetric quadratic Smith face the transverse quantity

    d 1 + d 2 + 2 * d 3

is exactly `2`.  Refining this face by *minimal* ordinary degree can be
performed by the single nonnegative source weight

    (1, M+1, M+1, 2M+1).

Choosing `M` above the full source-degree bound prevents a higher Smith
level from tying the selected quadratic degree.  This is the static
initial-form identity needed before constructing a family-level Rees
exposure.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Nonnegative integral source weight combining the symmetric Smith
separator with ordinary degree. -/
def adaptivePacketExposureWeight (M : ℕ) : Fin 4 → ℤ :=
  ![(1 : ℤ), (M : ℤ) + 1, (M : ℤ) + 1,
    2 * (M : ℤ) + 1]

/-- The combined weight is ordinary degree plus `M` times the symmetric
transverse level. -/
theorem weight_adaptivePacketExposureWeight
    (M : ℕ)
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (adaptivePacketExposureWeight M) d =
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) +
        (M : ℤ) * ((d 1 : ℤ) + (d 2 : ℤ) + 2 * (d 3 : ℤ)) := by
  rw [Finsupp.weight_apply]
  simp [adaptivePacketExposureWeight, Finsupp.sum_fintype,
    HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  push_cast
  ring

/-- Sum of the four source exponents in the combined diagonal exposure. -/
theorem sum_adaptivePacketExposureWeight
    (M : ℕ) :
    ∑ i : Fin 4, adaptivePacketExposureWeight M i =
      4 * (M : ℤ) + 4 := by
  simp [adaptivePacketExposureWeight, Fin.sum_univ_four]
  ring

/-- Exact change in the Hessian-determinant exponent when the combined
source diagonal is divided by the scalar selecting degree `D` on symmetric
level two.  The scale `M` cancels completely. -/
theorem adaptivePacketExposure_hessianDefectShift
    (M D : ℕ) :
    2 * (∑ i : Fin 4, adaptivePacketExposureWeight M i) -
        4 * ((D : ℤ) + 2 * (M : ℤ)) =
      8 - 4 * (D : ℤ) := by
  rw [sum_adaptivePacketExposureWeight]
  ring

/-- The combined exposure is determinant-clock preserving exactly for a
quadratic packet. -/
theorem adaptivePacketExposure_hessianDefectShift_eq_zero_iff
    (M D : ℕ) :
    2 * (∑ i : Fin 4, adaptivePacketExposureWeight M i) -
        4 * ((D : ℤ) + 2 * (M : ℤ)) = 0 ↔
      D = 2 := by
  rw [adaptivePacketExposure_hessianDefectShift]
  constructor <;> intro h
  · omega
  · subst D
    norm_num

/-- Above degree two, an honest integral exposure necessarily spends
`4*D-8` units of the incoming (possibly ramified) determinant clock. -/
theorem adaptivePacketExposure_hessianDefectShift_of_two_le
    (M D : ℕ)
    (hD : 2 ≤ D) :
    2 * (∑ i : Fin 4, adaptivePacketExposureWeight M i) -
        4 * ((D : ℤ) + 2 * (M : ℤ)) =
      -((4 * D - 8 : ℕ) : ℤ) := by
  rw [adaptivePacketExposure_hessianDefectShift]
  push_cast
  omega

/-- A quadratic Smith subface refined by degree `D` is one genuine linear
weighted initial form, provided all supported Smith levels are at least two
and `M` dominates the complete ordinary-degree range.

The statement uses an exact characterisation of `T`; the adaptive wall
integration will discharge it from symmetric minimality after blockers have
been excluded. -/
theorem smithSubfaceDegreeComponent_eq_combinedInitialForm
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D N M : ℕ)
    (hT : ∀ d : Fin 4 →₀ ℕ, d ∈ F.support →
      (smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ↔
        d 1 + d 2 + 2 * d 3 = 2))
    (hprimary : ∀ d ∈ F.support,
      2 ≤ d 1 + d 2 + 2 * d 3)
    (hdegree : ∀ d ∈ F.support,
      HC4.Polynomial.ordinaryDegree4 d ≤ N)
    (hD : D ≤ N)
    (hM : N < M) :
    smithSubfaceDegreeComponent T F D =
      HC4.Polynomial.initialForm
        (adaptivePacketExposureWeight M)
        ((D : ℤ) + 2 * (M : ℤ)) F := by
  ext d
  rw [coeff_smithSubfaceDegreeComponent,
    HC4.Polynomial.coeff_initialForm,
    weight_adaptivePacketExposureWeight]
  by_cases hd : MvPolynomial.coeff d F = 0
  · simp [hd]
  have hdsupp : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hd
  have hk : 2 ≤ d 1 + d 2 + 2 * d 3 := hprimary d hdsupp
  have hn : HC4.Polynomial.ordinaryDegree4 d ≤ N := hdegree d hdsupp
  have hiff :
      ((smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D)) ↔
        ((HC4.Polynomial.ordinaryDegree4 d : ℤ) +
            (M : ℤ) *
              ((d 1 : ℤ) + (d 2 : ℤ) + 2 * (d 3 : ℤ)) =
          (D : ℤ) + 2 * (M : ℤ)) := by
    rw [hT d hdsupp]
    constructor
    · rintro ⟨hk2, hDegEq⟩
      have hk2z :
          (d 1 : ℤ) + (d 2 : ℤ) + 2 * (d 3 : ℤ) = 2 := by
        exact_mod_cast hk2
      have hDegEqz :
          (HC4.Polynomial.ordinaryDegree4 d : ℤ) = D := by
        exact_mod_cast hDegEq
      rw [hk2z, hDegEqz]
      ring
    · intro heq
      have heqNat :
          HC4.Polynomial.ordinaryDegree4 d +
              M * (d 1 + d 2 + 2 * d 3) =
            D + 2 * M := by
        exact_mod_cast heq
      have hkLe : d 1 + d 2 + 2 * d 3 ≤ 2 := by
        by_contra hnot
        have hk3 : 3 ≤ d 1 + d 2 + 2 * d 3 := by omega
        have hmul : 3 * M ≤ M * (d 1 + d 2 + 2 * d 3) := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hk3
        have hmulTop : M * (d 1 + d 2 + 2 * d 3) ≤ D + 2 * M := by
          omega
        have hMD : M ≤ D := by omega
        omega
      have hk2 : d 1 + d 2 + 2 * d 3 = 2 := by omega
      constructor
      · exact hk2
      · rw [hk2] at heqNat
        omega
  by_cases hleft :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
        HC4.Polynomial.ordinaryDegree4 d = D
  · rw [if_pos hleft, if_pos (hiff.mp hleft)]
  · rw [if_neg hleft, if_neg (fun h => hleft (hiff.mpr h))]

end

end HC4.Newton
