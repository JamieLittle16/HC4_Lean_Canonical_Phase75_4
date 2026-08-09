import HC4.Newton.AxisHomogeneousNormalForm
import Mathlib.Tactic

/-!
# Coefficient recurrence from a fixed directional derivative

The cleanest route from the directional rigidity of Phase 91.4 to the
one-linear-form normal form is coefficientwise.

If

    D_{u,v} F = u * ∂ᵢF + v * ∂ⱼF = 0,

then at every lower multi-index `m` the two adjacent coefficients satisfy

    u * coeff (m + eᵢ) F * (m i + 1)
      + v * coeff (m + eⱼ) F * (m j + 1) = 0.

This is exactly the recurrence obeyed by the coefficients of a power of a
linear form.  Crucially, `m` retains all exponents in the other variables,
so the recurrence is valid separately on every frozen external slice.
That is the formal mechanism by which the eventual scalar multiple may
depend on the non-transverse variables, giving the desired shape

    a(X) * L(Y)^n.

No coordinate-change API is needed.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Coefficient of the binary directional derivative at an arbitrary
multi-index. -/
theorem coeff_binaryDirectionalDeriv
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m
        (binaryDirectionalDeriv u v i j F) =
      u *
          (MvPolynomial.coeff
              (m + Finsupp.single i 1) F *
            ((m i + 1 : ℕ) : K)) +
        v *
          (MvPolynomial.coeff
              (m + Finsupp.single j 1) F *
            ((m j + 1 : ℕ) : K)) := by
  classical
  simp [binaryDirectionalDeriv, coeff_pderiv_backport]

/-- **Directional coefficient recurrence.**
Vanishing of the fixed directional derivative imposes the adjacent
coefficient relation at every lower multi-index. -/
theorem directionalCoefficient_recurrence
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (m : σ →₀ ℕ) :
    u *
          (MvPolynomial.coeff
              (m + Finsupp.single i 1) F *
            ((m i + 1 : ℕ) : K)) +
        v *
          (MvPolynomial.coeff
              (m + Finsupp.single j 1) F *
            ((m j + 1 : ℕ) : K)) = 0 := by
  have hcoeff :=
    congrArg (MvPolynomial.coeff m) hdir
  rw [coeff_binaryDirectionalDeriv] at hcoeff
  simpa using hcoeff

/-- The same recurrence with the natural-number multiplicities moved next
to the direction scalars.  This is often the convenient form for solving
the finite homogeneous recurrence. -/
theorem directionalCoefficient_recurrence_assoc
    (u v : K)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (m : σ →₀ ℕ) :
    (u * ((m i + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single i 1) F +
      (v * ((m j + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single j 1) F = 0 := by
  have h :=
    directionalCoefficient_recurrence
      u v i j F hdir m
  calc
    (u * ((m i + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single i 1) F +
      (v * ((m j + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single j 1) F =
      u *
          (MvPolynomial.coeff
              (m + Finsupp.single i 1) F *
            ((m i + 1 : ℕ) : K)) +
        v *
          (MvPolynomial.coeff
              (m + Finsupp.single j 1) F *
            ((m j + 1 : ℕ) : K)) := by
      ring
    _ = 0 := h

/-- If the first direction scalar is nonzero, the adjacent `i`-coefficient
is explicitly determined by the adjacent `j`-coefficient. -/
theorem directionalCoefficient_solve_first
    (u v : K)
    (hu : u ≠ 0)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (m : σ →₀ ℕ)
    (hmult : (((m i + 1 : ℕ) : K)) ≠ 0) :
    MvPolynomial.coeff
          (m + Finsupp.single i 1) F =
      - (v * ((m j + 1 : ℕ) : K)) /
          (u * ((m i + 1 : ℕ) : K)) *
        MvPolynomial.coeff
          (m + Finsupp.single j 1) F := by
  have h :=
    directionalCoefficient_recurrence_assoc
      u v i j F hdir m
  have hden :
      u * ((m i + 1 : ℕ) : K) ≠ 0 :=
    mul_ne_zero hu hmult
  have hmul :
      (u * ((m i + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single i 1) F =
        - ((v * ((m j + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single j 1) F) := by
    linear_combination h
  calc
    MvPolynomial.coeff
          (m + Finsupp.single i 1) F =
      (- ((v * ((m j + 1 : ℕ) : K)) *
          MvPolynomial.coeff
            (m + Finsupp.single j 1) F)) /
        (u * ((m i + 1 : ℕ) : K)) := by
      apply (eq_div_iff hden).2
      calc
        MvPolynomial.coeff
              (m + Finsupp.single i 1) F *
            (u * ((m i + 1 : ℕ) : K)) =
          (u * ((m i + 1 : ℕ) : K)) *
            MvPolynomial.coeff
              (m + Finsupp.single i 1) F := by
          ring
        _ =
          - ((v * ((m j + 1 : ℕ) : K)) *
            MvPolynomial.coeff
              (m + Finsupp.single j 1) F) := hmul
    _ =
      - (v * ((m j + 1 : ℕ) : K)) /
          (u * ((m i + 1 : ℕ) : K)) *
        MvPolynomial.coeff
          (m + Finsupp.single j 1) F := by
      simp only [div_eq_mul_inv]
      ring

/-- Characteristic-zero specialization removes the only extra
nonvanishing hypothesis in the solved recurrence. -/
theorem directionalCoefficient_solve_first_charZero
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff
          (m + Finsupp.single i 1) F =
      - (v * ((m j + 1 : ℕ) : K)) /
          (u * ((m i + 1 : ℕ) : K)) *
        MvPolynomial.coeff
          (m + Finsupp.single j 1) F := by
  apply directionalCoefficient_solve_first
    u v hu i j F hdir m
  exact_mod_cast Nat.succ_ne_zero (m i)

end

end HC4.Newton
