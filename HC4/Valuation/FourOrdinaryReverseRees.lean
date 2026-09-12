import HC4.Valuation.FirstKernelBreakRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import HC4.Valuation.ActualParameterLayer
import Mathlib.Tactic

/-!
# Ordinary reverse-Rees family in four source variables

For a four-variable polynomial `F` whose ordinary source degree is bounded by
`D`, define the honest polynomial family

    R_D(F)(tau,x) = tau^D F(x/tau)

without using negative powers: a source monomial of ordinary degree `m`
receives the coefficient factor `tau^(D-m)`.

The family parameter is deliberately independent of every Smith/blocker
clock.  This file first establishes the exact source coefficient and parameter
layer formulas.  In particular

    [tau^q] R_D(F) = H_{D-q},

where `H_m` is the exact ordinary homogeneous component of `F`, and evaluation
at `tau = 1` recovers `F` exactly.

The Hessian determinant clock and moving-collision covariance are added as
separate theorems downstream; keeping the constructor/layer API independent
makes those calculations reusable and avoids mixing clock provenance.
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

end

end HC4.Valuation
