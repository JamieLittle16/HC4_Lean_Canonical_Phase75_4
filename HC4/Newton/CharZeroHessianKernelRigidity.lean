import HC4.Newton.TransverseSupportRigidity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Tactic

/-!
# Characteristic-zero Hessian-kernel rigidity

Phase 91.2 proved that a fixed binary Hessian-kernel direction gives
`D²F = 0`. Phase 91.3 identified the stronger support-theoretic endpoint
actually needed in the HC4 argument:

* if `D F` is independent of the two transverse variables, and
* every nonzero monomial of `D F` has positive transverse degree,

then `D F = 0`.

This file supplies the missing characteristic-zero bridge.

The pinned Mathlib version predates `MvPolynomial.coeff_pderiv`, so we
first prove the coefficient formula locally:

    coeff m (pderiv i F)
      = coeff (m + single i 1) F * (m i + 1).

From it we obtain two facts:

1. mixed formal partial derivatives commute;
2. over a characteristic-zero field, `pderiv i F = 0` forces every
   nonzero monomial of `F` to have exponent zero in variable `i`.

Applying (1) to the two Hessian-row kernel equations shows that
`pderiv i (D F)=pderiv j (D F)=0`. Applying (2) then proves that `D F`
is transversely independent. Phase 91.3 finally turns positive transverse
degree into `D F = 0`.
-/

namespace HC4.Newton

noncomputable section

open Finsupp

variable {σ K : Type*} [Field K]

/-- Backport of the coefficient formula for `MvPolynomial.pderiv`.
The pinned Mathlib used by HC4 has the required monomial derivative API but
predates this convenience theorem. -/
theorem coeff_pderiv_backport
    (i : σ)
    (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv i F) =
      MvPolynomial.coeff (m + Finsupp.single i 1) F *
        ((m i + 1 : ℕ) : K) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp [hP, hQ, add_mul]
  | monomial n a =>
      rw [MvPolynomial.pderiv_monomial,
        MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : n = m + Finsupp.single i 1
      · simp [h]
      · simp only [h, if_false, zero_mul]
        by_cases hn : n i = 0
        · simp [hn]
        · apply if_neg
          have hle : Finsupp.single i 1 ≤ n := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr hn
          intro hsub
          apply h
          exact (tsub_eq_iff_eq_add_of_le hle).mp hsub

/-- Formal mixed partial derivatives commute. -/
theorem pderiv_comm_backport
    (i j : σ)
    (F : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i F) := by
  classical
  ext m
  rw [coeff_pderiv_backport, coeff_pderiv_backport,
    coeff_pderiv_backport, coeff_pderiv_backport]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_apply, hij, hji,
      add_comm, add_left_comm, add_assoc]
    ring

/-- In characteristic zero, a vanishing partial derivative detects absence
of that variable from every nonzero monomial. -/
theorem exponent_eq_zero_of_pderiv_eq_zero
    [CharZero K]
    (i : σ)
    (F : MvPolynomial σ K)
    (hderiv : MvPolynomial.pderiv i F = 0)
    (d : σ →₀ ℕ)
    (hd : MvPolynomial.coeff d F ≠ 0) :
    d i = 0 := by
  by_contra hdi
  let m : σ →₀ ℕ := d - Finsupp.single i 1
  have hmadd : m + Finsupp.single i 1 = d := by
    dsimp [m]
    exact sub_add_single_one_cancel hdi
  have hcoeff :=
    coeff_pderiv_backport (K := K) i F m
  rw [hderiv] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  rw [hmadd] at hcoeff
  have hcast : (((m i + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (m i)
  have hzero : MvPolynomial.coeff d F = 0 :=
    (mul_eq_zero.mp hcoeff.symm).resolve_right hcast
  exact hd hzero

/-- Vanishing partials in both transverse variables imply the
support-theoretic transverse independence used in Phase 91.3. -/
theorem isTransverselyIndependent_of_pderiv_eq_zero
    [CharZero K]
    (i j : σ)
    (G : MvPolynomial σ K)
    (hi : MvPolynomial.pderiv i G = 0)
    (hj : MvPolynomial.pderiv j G = 0) :
    IsTransverselyIndependent i j G := by
  intro d hd
  exact
    ⟨exponent_eq_zero_of_pderiv_eq_zero i G hi d hd,
      exponent_eq_zero_of_pderiv_eq_zero j G hj d hd⟩

/-- Differentiating the binary directional derivative in the first
transverse variable reproduces the first Hessian-row directional
derivative. -/
theorem pderiv_binaryDirectionalDeriv_first
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K) :
    MvPolynomial.pderiv i
        (binaryDirectionalDeriv u v i j F) =
      binaryDirectionalDeriv u v i j
        (MvPolynomial.pderiv i F) := by
  unfold binaryDirectionalDeriv
  simp only [map_add, MvPolynomial.pderiv_C_mul]
  rw [pderiv_comm_backport i j F]

/-- Differentiating the binary directional derivative in the second
transverse variable reproduces the second Hessian-row directional
derivative. -/
theorem pderiv_binaryDirectionalDeriv_second
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K) :
    MvPolynomial.pderiv j
        (binaryDirectionalDeriv u v i j F) =
      binaryDirectionalDeriv u v i j
        (MvPolynomial.pderiv j F) := by
  unfold binaryDirectionalDeriv
  simp only [map_add, MvPolynomial.pderiv_C_mul]
  rw [pderiv_comm_backport j i F]

/-- **Characteristic-zero fixed-kernel independence.**
The two binary Hessian-row kernel equations force the first directional
derivative to be independent of both transverse variables. -/
theorem binaryDirectionalDeriv_independent_of_hessianKernel
    [CharZero K]
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasFixedBinaryHessianKernel u v i j F) :
    IsTransverselyIndependent i j
      (binaryDirectionalDeriv u v i j F) := by
  apply isTransverselyIndependent_of_pderiv_eq_zero i j
  · rw [pderiv_binaryDirectionalDeriv_first]
    exact hkernel.1
  · rw [pderiv_binaryDirectionalDeriv_second]
    exact hkernel.2

/-- **Fixed-kernel homogeneous rigidity.**
If the directional derivative has exact positive transverse degree, then
the Hessian-kernel equations force it to vanish. -/
theorem binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree
    [CharZero K]
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K)
    (n : ℕ)
    (hn : 0 < n)
    (hkernel : HasFixedBinaryHessianKernel u v i j F)
    (hexact :
      HasExactTransverseDegree i j n
        (binaryDirectionalDeriv u v i j F)) :
    binaryDirectionalDeriv u v i j F = 0 := by
  apply
    binaryDirectionalDeriv_eq_zero_of_exactPositiveDegree_of_independent
      u v i j F n hn hexact
  exact binaryDirectionalDeriv_independent_of_hessianKernel
    u v i j F hkernel

/-- Left-pivot specialization using the canonical kernel direction
`(-b,a)` from Phase 91.1. -/
theorem leftPivot_directionalDeriv_eq_zero_of_exactPositiveDegree
    [CharZero K]
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (i j : σ)
    (F : MvPolynomial σ K)
    (n : ℕ)
    (hn : 0 < n)
    (hkernel : HasLeftPivotHessianKernel q i j F)
    (hexact :
      HasExactTransverseDegree i j n
        (binaryDirectionalDeriv (-q.b) q.a i j F)) :
    binaryDirectionalDeriv (-q.b) q.a i j F = 0 := by
  exact
    binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree
      (-q.b) q.a i j F n hn hkernel hexact

end

end HC4.Newton
