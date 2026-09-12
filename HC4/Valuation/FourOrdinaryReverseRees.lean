import HC4.Valuation.FirstKernelBreakRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.SeparatedRightWallScaleDescent
import Mathlib.Tactic

/-!
# Ordinary reverse-Rees family in four source variables

For a four-variable polynomial `F` whose ordinary source degree is bounded by
`D`, define the honest polynomial family

    R_D(F)(tau,x) = tau^D F(x/tau)

without using negative powers: a source monomial of ordinary degree `m`
receives the coefficient factor `tau^(D-m)`.

The family parameter is deliberately independent of every Smith/blocker
clock.  This file establishes the exact source coefficient and parameter
layer formulas, evaluation at `tau = 1`, and the exact determinant clock

    det Hess R_D(F) = tau^(4D-8)

when `det Hess F = 1` and `D >= 2`.

The determinant proof is source-honest.  Reinflating all four source
coordinates by `tau` turns the family into `tau^D F`; the existing
one-coordinate Hessian covariance contributes exactly two powers per source
coordinate, hence eight in total.  Injectivity of the four source inflations
then recovers the reverse-Rees determinant itself.  No relation with a Smith,
blocker, or auxiliary ray clock is asserted.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Standard reverse-Rees/homogenisation family at ordinary degree cap `D`.
A monomial `X^d` receives parameter order `D - ordinaryDegree4 d`. -/
noncomputable def fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ) : MvPolynomial (Fin 4) (Polynomial K) := by
  classical
  exact F.sum fun d c =>
    MvPolynomial.monomial d
      (Polynomial.X ^ (D - HC4.Polynomial.ordinaryDegree4 d) *
        Polynomial.C c)

/-- Exact coefficient of one source monomial in the reverse-Rees family. -/
theorem coeff_fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (fourOrdinaryReverseReesFamily F D) =
      Polynomial.X ^ (D - HC4.Polynomial.ordinaryDegree4 d) *
        Polynomial.C (MvPolynomial.coeff d F) := by
  classical
  unfold fourOrdinaryReverseReesFamily
  rw [MvPolynomial.sum_def]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hd : d ∈ F.support
  · simp [hd]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hcoeff]

/-- Scalar parameter coefficient of one source coefficient. -/
theorem coeff_coeff_fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (d : Fin 4 →₀ ℕ)
    (n : ℕ) :
    (MvPolynomial.coeff d (fourOrdinaryReverseReesFamily F D)).coeff n =
      if D - HC4.Polynomial.ordinaryDegree4 d = n then
        MvPolynomial.coeff d F
      else 0 := by
  rw [coeff_fourOrdinaryReverseReesFamily]
  rw [Polynomial.coeff_X_pow_mul']
  let m := D - HC4.Polynomial.ordinaryDegree4 d
  by_cases hmn : m = n
  · have hle : m ≤ n := by omega
    rw [if_pos hmn]
    simp [m, hle, hmn]
  · rw [if_neg hmn]
    by_cases hle : m ≤ n
    · have hsubpos : 0 < n - m := by omega
      simp [m, hle, hmn, Polynomial.coeff_C, Nat.ne_of_gt hsubpos]
    · have hlt : n < m := Nat.lt_of_not_ge hle
      simp [m, Nat.not_le.mpr hlt, hmn]

/-- **Exact reverse-Rees layer identification.**

Under an actual ordinary-degree bound `D`, parameter order `n ≤ D` is exactly
the ordinary homogeneous source layer of degree `D-n`. -/
theorem familyParameterLayer_fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D n : ℕ)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hn : n ≤ D) :
    familyParameterLayer (fourOrdinaryReverseReesFamily F D) n =
      fourOrdinaryDegreeComponent F (D - n) := by
  classical
  ext d
  rw [familyParameterLayer_coeff]
  rw [coeff_coeff_fourOrdinaryReverseReesFamily]
  unfold fourOrdinaryDegreeComponent
  rw [HC4.Polynomial.coeff_initialForm]
  rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4]
  by_cases hd : d ∈ F.support
  · have hdeg : HC4.Polynomial.ordinaryDegree4 d ≤ D := hmax d hd
    have heq :
        D - HC4.Polynomial.ordinaryDegree4 d = n ↔
          HC4.Polynomial.ordinaryDegree4 d = D - n := by
      omega
    by_cases hparam : D - HC4.Polynomial.ordinaryDegree4 d = n
    · rw [if_pos hparam]
      have hdegree : HC4.Polynomial.ordinaryDegree4 d = D - n := heq.mp hparam
      have hweight :
          (HC4.Polynomial.ordinaryDegree4 d : ℤ) = ((D - n : ℕ) : ℤ) := by
        exact_mod_cast hdegree
      simp [hweight]
    · rw [if_neg hparam]
      have hdegree : HC4.Polynomial.ordinaryDegree4 d ≠ D - n := by
        intro h
        exact hparam (heq.mpr h)
      have hweight :
          (HC4.Polynomial.ordinaryDegree4 d : ℤ) ≠ ((D - n : ℕ) : ℤ) := by
        exact_mod_cast hdegree
      simp [hweight]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hcoeff]

/-- The special parameter layer is exactly the maximal ordinary layer. -/
theorem familyParameterLayer_zero_fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D) :
    familyParameterLayer (fourOrdinaryReverseReesFamily F D) 0 =
      fourOrdinaryDegreeComponent F D := by
  simpa using
    familyParameterLayer_fourOrdinaryReverseReesFamily F D 0 hmax (Nat.zero_le D)

/-- Evaluation of the reverse-Rees parameter at `1` recovers the original
source polynomial exactly. -/
theorem map_evalOne_fourOrdinaryReverseReesFamily
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ) :
    MvPolynomial.map (Polynomial.evalRingHom (1 : K))
        (fourOrdinaryReverseReesFamily F D) = F := by
  ext d
  rw [MvPolynomial.coeff_map]
  rw [coeff_fourOrdinaryReverseReesFamily]
  simp

/-! ## Reinflating all four source coordinates -/

/-- Multiply all four source variables by the family parameter once. -/
noncomputable def fourUnitSourceInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  kernelInflateHom (K := K) (0 : Fin 4) 1
    (unitTransverseInflateFamily (K := K) P)

/-- Exact coefficient formula for simultaneous unit inflation of all four
source coordinates. -/
theorem coeff_fourUnitSourceInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (fourUnitSourceInflateFamily P) =
      Polynomial.X ^ HC4.Polynomial.ordinaryDegree4 d *
        MvPolynomial.coeff d P := by
  unfold fourUnitSourceInflateFamily
  rw [coeff_kernelInflateHom]
  rw [coeff_unitTransverseInflateFamily]
  simp only [kernelCoefficientTauPower, one_mul]
  rw [← mul_assoc, ← pow_add]
  rfl

/-- Four unit source inflations are injective. -/
theorem fourUnitSourceInflateFamily_injective :
    Function.Injective
      (fourUnitSourceInflateFamily (K := K)) := by
  intro P Q hPQ
  unfold fourUnitSourceInflateFamily at hPQ
  have h3 :
      unitTransverseInflateFamily (K := K) P =
        unitTransverseInflateFamily (K := K) Q :=
    kernelInflateHom_injective (K := K) (0 : Fin 4) 1 hPQ
  unfold unitTransverseInflateFamily at h3
  have h2 := kernelInflateHom_injective (K := K) (3 : Fin 4) 1 h3
  have h1 := kernelInflateHom_injective (K := K) (2 : Fin 4) 1 h2
  exact kernelInflateHom_injective (K := K) (1 : Fin 4) 1 h1

/-- Simultaneous source inflation fixes coefficient-ring constants. -/
theorem fourUnitSourceInflateFamily_C
    (c : Polynomial K) :
    fourUnitSourceInflateFamily
        (K := K) (MvPolynomial.C c) =
      MvPolynomial.C c := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_fourUnitSourceInflateFamily]
  by_cases hd : d = 0
  · subst d
    simp [HC4.Polynomial.ordinaryDegree4]
  · have hcoeff :
      MvPolynomial.coeff d
          (MvPolynomial.C c : MvPolynomial (Fin 4) (Polynomial K)) = 0 := by
      simp [MvPolynomial.coeff_C, hd]
    rw [hcoeff]
    simp

/-- Reinflating the reverse-Rees family recovers the scalar family
`tau^D * F`. -/
theorem fourUnitSourceInflate_reverseRees_eq
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D) :
    fourUnitSourceInflateFamily
        (fourOrdinaryReverseReesFamily F D) =
      MvPolynomial.C (Polynomial.X ^ D) *
        MvPolynomial.map Polynomial.C F := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_fourUnitSourceInflateFamily]
  rw [coeff_fourOrdinaryReverseReesFamily]
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.coeff_map]
  by_cases hd : d ∈ F.support
  · have hdeg := hmax d hd
    rw [← mul_assoc, ← pow_add]
    rw [Nat.add_sub_of_le hdeg]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hcoeff]

/-- Four source inflations raise an exact four-variable Hessian determinant
defect by eight. -/
theorem fourUnitSourceInflateFamily_hasHessianDefect_add_eight
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (fourUnitSourceInflateFamily P)
      (Delta + 8) := by
  unfold fourUnitSourceInflateFamily
  have htrans :=
    unitTransverseInflateFamily_hasHessianDefect_add_six
      (K := K) P hdef
  have hzero :=
    kernelInflateHom_unit_hasHessianDefect_add_two
      (K := K) (0 : Fin 4)
      (unitTransverseInflateFamily (K := K) P) htrans
  convert hzero using 1 <;> omega

/-- Exact determinant covariance for four simultaneous unit source
inflations, before assuming a pure determinant clock. -/
theorem hessianDeterminant_fourUnitSourceInflateFamily
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (fourUnitSourceInflateFamily P) =
      MvPolynomial.C (Polynomial.X ^ 8) *
        fourUnitSourceInflateFamily
          (HC4.Polynomial.hessianDeterminant P) := by
  unfold fourUnitSourceInflateFamily unitTransverseInflateFamily
  rw [hessianDeterminant_kernelInflateHom]
  rw [hessianDeterminant_kernelInflateHom]
  rw [hessianDeterminant_kernelInflateHom]
  rw [hessianDeterminant_kernelInflateHom]
  simp [kernelInflateHom, kernelInflateDerivativeCoefficient,
    MvPolynomial.C_pow]
  ring

/-- Coefficient extension from `K` to `K[tau]` commutes with the Hessian
determinant. -/
theorem hessianDeterminant_map_polynomialC
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant
        (MvPolynomial.map Polynomial.C F) =
      MvPolynomial.map Polynomial.C
        (HC4.Polynomial.hessianDeterminant F) := by
  let f :
      MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.map Polynomial.C
  have hmatrix :
      HC4.Polynomial.hessian (f F) =
        f.mapMatrix (HC4.Polynomial.hessian F) := by
    apply Matrix.ext
    intro i j
    simp [f, HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]
  unfold HC4.Polynomial.hessianDeterminant
  rw [hmatrix]
  exact (RingHom.map_det f (HC4.Polynomial.hessian F)).symm

/-- The fully reinflated reverse-Rees source has determinant `tau^(4D)` when
the original source has Hessian determinant one. -/
theorem hessianDeterminant_scalarMapped_eq_X_pow_four_mul
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    HC4.Polynomial.hessianDeterminant
        (MvPolynomial.C (Polynomial.X ^ D) *
          MvPolynomial.map Polynomial.C F) =
      MvPolynomial.C (Polynomial.X ^ (4 * D)) := by
  rw [hessianDeterminant_C_mul]
  rw [hessianDeterminant_map_polynomialC]
  rw [hdet]
  simp [MvPolynomial.C_pow, ← pow_mul, Nat.mul_comm]

/-- **Exact ordinary reverse-Rees Hessian clock.**

For a degree-`D` four-variable determinant-one source, the honest reverse-Rees
family has pure determinant order `4D-8 = 4(D-2)`.  This order belongs only
to this reverse-Rees construction. -/
theorem fourOrdinaryReverseReesFamily_hasHessianDefect
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hD : 2 ≤ D)
    (hmax :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (fourOrdinaryReverseReesFamily F D)
      (4 * (D - 2)) := by
  let R := fourOrdinaryReverseReesFamily F D
  have hreinflate :
      fourUnitSourceInflateFamily R =
        MvPolynomial.C (Polynomial.X ^ D) *
          MvPolynomial.map Polynomial.C F := by
    dsimp [R]
    exact fourUnitSourceInflate_reverseRees_eq F D hmax
  have hinflatedDet :
      HC4.Polynomial.hessianDeterminant
          (fourUnitSourceInflateFamily R) =
        MvPolynomial.C (Polynomial.X ^ (4 * D)) := by
    rw [hreinflate]
    exact hessianDeterminant_scalarMapped_eq_X_pow_four_mul F D hdet
  have hfactor := hessianDeterminant_fourUnitSourceInflateFamily R
  have heq :
      MvPolynomial.C (Polynomial.X ^ 8) *
          fourUnitSourceInflateFamily
            (HC4.Polynomial.hessianDeterminant R) =
        MvPolynomial.C (Polynomial.X ^ (4 * D)) := by
    rw [← hfactor]
    exact hinflatedDet
  have hexp : 8 + 4 * (D - 2) = 4 * D := by omega
  have hpow :
      MvPolynomial.C (Polynomial.X ^ 8) *
          MvPolynomial.C (Polynomial.X ^ (4 * (D - 2))) =
        (MvPolynomial.C (Polynomial.X ^ (4 * D)) :
          MvPolynomial (Fin 4) (Polynomial K)) := by
    rw [← MvPolynomial.C_mul]
    rw [← pow_add]
    rw [hexp]
  have hcancel :
      MvPolynomial.C (Polynomial.X ^ 8) *
          fourUnitSourceInflateFamily
            (HC4.Polynomial.hessianDeterminant R) =
        MvPolynomial.C (Polynomial.X ^ 8) *
          MvPolynomial.C (Polynomial.X ^ (4 * (D - 2))) := by
    calc
      MvPolynomial.C (Polynomial.X ^ 8) *
          fourUnitSourceInflateFamily
            (HC4.Polynomial.hessianDeterminant R) =
        MvPolynomial.C (Polynomial.X ^ (4 * D)) := heq
      _ = MvPolynomial.C (Polynomial.X ^ 8) *
          MvPolynomial.C (Polynomial.X ^ (4 * (D - 2))) := hpow.symm
  have hfac :
      (MvPolynomial.C (Polynomial.X ^ 8) :
        MvPolynomial (Fin 4) (Polynomial K)) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero 8 Polynomial.X_ne_zero)
  have hinflated :
      fourUnitSourceInflateFamily
          (HC4.Polynomial.hessianDeterminant R) =
        MvPolynomial.C (Polynomial.X ^ (4 * (D - 2))) := by
    have hz :
        MvPolynomial.C (Polynomial.X ^ 8) *
            (fourUnitSourceInflateFamily
                (HC4.Polynomial.hessianDeterminant R) -
              MvPolynomial.C (Polynomial.X ^ (4 * (D - 2)))) = 0 := by
      rw [mul_sub, hcancel, sub_self]
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfac hzero)
    · exact sub_eq_zero.mp hzero
  unfold HasPolynomialFamilyHessianDefect
  dsimp [R] at hinflated ⊢
  apply fourUnitSourceInflateFamily_injective (K := K)
  calc
    fourUnitSourceInflateFamily
        (HC4.Polynomial.hessianDeterminant
          (fourOrdinaryReverseReesFamily F D)) =
      MvPolynomial.C (Polynomial.X ^ (4 * (D - 2))) := hinflated
    _ = fourUnitSourceInflateFamily
        (MvPolynomial.C (Polynomial.X ^ (4 * (D - 2)))) := by
      rw [fourUnitSourceInflateFamily_C]

end

end HC4.Valuation
