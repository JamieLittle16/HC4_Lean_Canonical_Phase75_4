import HC4.RationalRigidity.ReducedFractionAssembly
import HC4.RationalRigidity.PoleRemovalAssembly

/-!
# Finite/infinity chart certificates for rational rigidity

This module packages the geometric input expected from the finite and infinity
charts into small algebraic certificates.

A chart proves denominator nonvanishing as soon as it supplies a function `u`
with

    u(s) * D(y(s)) = 1.

Two chart maps jointly cover the coefficient field when every scalar is reached
by at least one of them.  Unit certificates on the two charts then imply global
nonvanishing of `D`.  The Phase 10 pole-removal assembly consequently makes the
denominator constant, and the Phase 9 assembly classifies the numerator.

The module also records a Bezout-plus-cleared-equation certificate.  This is the
pointwise form of the reduced-fraction argument: if a Bezout combination of the
numerator and denominator is `1`, and the chart equation makes the numerator a
multiple of the denominator, then the denominator cannot vanish at that chart
point.
-/

namespace HC4.RationalRigidity

open Polynomial

/-- Two parametrised charts jointly reach every scalar of `K`. -/
def TwoChartCover
    {K SFinite SInfinity : Type*}
    (yFinite : SFinite → K) (yInfinity : SInfinity → K) : Prop :=
  ∀ t : K,
    (∃ s : SFinite, yFinite s = t) ∨
      (∃ s : SInfinity, yInfinity s = t)

section Field

variable {K : Type*} [Field K]

/-- A left unit certificate forces the evaluated denominator to be nonzero. -/
theorem eval_ne_zero_of_left_unit_certificate
    {S : Type*}
    (D : K[X]) (y u : S → K)
    (hCert : ∀ s, u s * D.eval (y s) = 1) :
    ∀ s, D.eval (y s) ≠ 0 := by
  intro s hZero
  have h := hCert s
  rw [hZero, mul_zero] at h
  exact zero_ne_one h

/-- A right unit certificate gives the same nonvanishing conclusion. -/
theorem eval_ne_zero_of_right_unit_certificate
    {S : Type*}
    (D : K[X]) (y u : S → K)
    (hCert : ∀ s, D.eval (y s) * u s = 1) :
    ∀ s, D.eval (y s) ≠ 0 := by
  intro s hZero
  have h := hCert s
  rw [hZero, zero_mul] at h
  exact zero_ne_one h

/--
A pointwise Bezout certificate together with a cleared chart identity forces
pointwise denominator nonvanishing.
-/
theorem eval_ne_zero_of_bezout_and_cleared_chart
    {S : Type*}
    (N D P : K[X]) (y A B : S → K)
    (hBezout :
      ∀ s, A s * N.eval (y s) + B s * D.eval (y s) = 1)
    (hClear :
      ∀ s, N.eval (y s) = P.eval (y s) * D.eval (y s)) :
    ∀ s, D.eval (y s) ≠ 0 := by
  intro s hZero
  have h := hBezout s
  rw [hClear s, hZero] at h
  have hFalse : (0 : K) = 1 := by simpa using h
  exact zero_ne_one hFalse

/-- Nonvanishing on two jointly covering charts is global nonvanishing. -/
theorem eval_ne_zero_of_two_chart_cover
    {SFinite SInfinity : Type*}
    (D : K[X])
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hFinite : ∀ s, D.eval (yFinite s) ≠ 0)
    (hInfinity : ∀ s, D.eval (yInfinity s) ≠ 0) :
    ∀ t : K, D.eval t ≠ 0 := by
  intro t
  rcases hCover t with ⟨s, hs⟩ | ⟨s, hs⟩
  · simpa [hs] using hFinite s
  · simpa [hs] using hInfinity s

/-- An identity holding on two jointly covering charts holds globally. -/
theorem identity_of_two_chart_cover
    {SFinite SInfinity : Type*}
    (f g : K → K)
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hFinite : ∀ s, f (yFinite s) = g (yFinite s))
    (hInfinity : ∀ s, f (yInfinity s) = g (yInfinity s)) :
    ∀ t : K, f t = g t := by
  intro t
  rcases hCover t with ⟨s, hs⟩ | ⟨s, hs⟩
  · simpa [hs] using hFinite s
  · simpa [hs] using hInfinity s

end Field

section InfiniteField

variable {K : Type*} [Field K] [Infinite K]

/--
A reduced cleared identity verified on two jointly covering charts yields the
complete unnormalised numerator-denominator classification.  This is the main
finite/infinity chart assembly theorem of Phase 11.
-/
theorem reduced_polynomial_pair_of_two_chart_cleared_identity
    {SFinite SInfinity : Type*}
    (N D P : K[X])
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hCoprime : IsCoprime N D)
    (hFinite :
      ∀ s, N.eval (yFinite s) = P.eval (yFinite s) * D.eval (yFinite s))
    (hInfinity :
      ∀ s, N.eval (yInfinity s) = P.eval (yInfinity s) * D.eval (yInfinity s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * P := by
  have hGlobal :
      ∀ t : K, N.eval t = P.eval t * D.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t)
      (fun t => P.eval t * D.eval t)
      yFinite yInfinity hCover hFinite hInfinity
  exact reduced_polynomial_pair_of_cleared_chart
    N D P (fun t : K => t) Function.surjective_id hCoprime hGlobal

/-- Monic normalisation of the two-chart reduced polynomial theorem. -/
theorem reduced_polynomial_pair_of_monic_two_chart_cleared_identity
    {SFinite SInfinity : Type*}
    (N D P : K[X])
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hCoprime : IsCoprime N D)
    (hMonic : D.Monic)
    (hFinite :
      ∀ s, N.eval (yFinite s) = P.eval (yFinite s) * D.eval (yFinite s))
    (hInfinity :
      ∀ s, N.eval (yInfinity s) = P.eval (yInfinity s) * D.eval (yInfinity s)) :
    D = 1 ∧ N = P := by
  have hGlobal :
      ∀ t : K, N.eval t = P.eval t * D.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t)
      (fun t => P.eval t * D.eval t)
      yFinite yInfinity hCover hFinite hInfinity
  exact reduced_polynomial_pair_of_monic_cleared_chart
    N D P (fun t : K => t) Function.surjective_id
      hCoprime hMonic hGlobal

/-- Power-target specialisation of the reduced two-chart theorem. -/
theorem reduced_power_pair_of_two_chart_cleared_identity
    {SFinite SInfinity : Type*}
    (N D : K[X])
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hCoprime : IsCoprime N D)
    (m : ℕ)
    (hFinite :
      ∀ s, N.eval (yFinite s) = (yFinite s) ^ m * D.eval (yFinite s))
    (hInfinity :
      ∀ s, N.eval (yInfinity s) = (yInfinity s) ^ m * D.eval (yInfinity s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * X ^ m := by
  have hGlobal :
      ∀ t : K, N.eval t = t ^ m * D.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t)
      (fun t => t ^ m * D.eval t)
      yFinite yInfinity hCover hFinite hInfinity
  exact reduced_power_pair_of_cleared_chart
    N D (fun t : K => t) Function.surjective_id hCoprime m hGlobal

/-- Fully normalised power conclusion from reduced finite/infinity charts. -/
theorem reduced_power_pair_of_monic_two_chart_cleared_identity
    {SFinite SInfinity : Type*}
    (N D : K[X])
    (yFinite : SFinite → K) (yInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hCoprime : IsCoprime N D)
    (hMonic : D.Monic)
    (m : ℕ)
    (hFinite :
      ∀ s, N.eval (yFinite s) = (yFinite s) ^ m * D.eval (yFinite s))
    (hInfinity :
      ∀ s, N.eval (yInfinity s) = (yInfinity s) ^ m * D.eval (yInfinity s)) :
    D = 1 ∧ N = X ^ m := by
  have hGlobal :
      ∀ t : K, N.eval t = t ^ m * D.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t)
      (fun t => t ^ m * D.eval t)
      yFinite yInfinity hCover hFinite hInfinity
  exact reduced_power_pair_of_monic_cleared_chart
    N D (fun t : K => t) Function.surjective_id
      hCoprime hMonic m hGlobal

end InfiniteField

section AlgebraicallyClosedField

variable {K : Type*} [Field K] [IsAlgClosed K]

/--
Finite and infinity unit certificates make the polynomial denominator a
nonzero constant.
-/
theorem constant_denominator_of_two_chart_unit_certificates
    {SFinite SInfinity : Type*}
    (D : K[X])
    (yFinite uFinite : SFinite → K)
    (yInfinity uInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hFinite : ∀ s, uFinite s * D.eval (yFinite s) = 1)
    (hInfinity : ∀ s, uInfinity s * D.eval (yInfinity s) = 1) :
    ∃ d : K, d ≠ 0 ∧ D = C d := by
  apply constant_polynomial_of_eval_ne_zero D
  apply eval_ne_zero_of_two_chart_cover
    D yFinite yInfinity hCover
  · exact eval_ne_zero_of_left_unit_certificate D yFinite uFinite hFinite
  · exact eval_ne_zero_of_left_unit_certificate D yInfinity uInfinity hInfinity

/--
A polynomial-target rational identity verified on both charts, together with
unit certificates, yields the complete unnormalised rigidity conclusion.
-/
theorem rational_identity_of_two_chart_unit_certificates
    {SFinite SInfinity : Type*}
    (N D P : K[X])
    (yFinite uFinite : SFinite → K)
    (yInfinity uInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hFiniteUnit : ∀ s, uFinite s * D.eval (yFinite s) = 1)
    (hInfinityUnit : ∀ s, uInfinity s * D.eval (yInfinity s) = 1)
    (hFiniteRat :
      ∀ s, N.eval (yFinite s) / D.eval (yFinite s) = P.eval (yFinite s))
    (hInfinityRat :
      ∀ s, N.eval (yInfinity s) / D.eval (yInfinity s) = P.eval (yInfinity s)) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * P := by
  have hD : ∀ t : K, D.eval t ≠ 0 :=
    eval_ne_zero_of_two_chart_cover
      D yFinite yInfinity hCover
      (eval_ne_zero_of_left_unit_certificate
        D yFinite uFinite hFiniteUnit)
      (eval_ne_zero_of_left_unit_certificate
        D yInfinity uInfinity hInfinityUnit)
  have hRat : ∀ t : K, N.eval t / D.eval t = P.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t / D.eval t)
      (fun t => P.eval t)
      yFinite yInfinity hCover hFiniteRat hInfinityRat
  exact rational_identity_of_nonvanishing_denominator
    N D P (fun t : K => t) Function.surjective_id hD hRat

/-- Power-target form of the two-chart rigidity theorem. -/
theorem rational_power_pair_of_two_chart_unit_certificates
    {SFinite SInfinity : Type*}
    (N D : K[X])
    (yFinite uFinite : SFinite → K)
    (yInfinity uInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (m : ℕ)
    (hFiniteUnit : ∀ s, uFinite s * D.eval (yFinite s) = 1)
    (hInfinityUnit : ∀ s, uInfinity s * D.eval (yInfinity s) = 1)
    (hFiniteRat :
      ∀ s, N.eval (yFinite s) / D.eval (yFinite s) = (yFinite s) ^ m)
    (hInfinityRat :
      ∀ s, N.eval (yInfinity s) / D.eval (yInfinity s) = (yInfinity s) ^ m) :
    ∃ d : K, d ≠ 0 ∧ D = C d ∧ N = C d * X ^ m := by
  have hD : ∀ t : K, D.eval t ≠ 0 :=
    eval_ne_zero_of_two_chart_cover
      D yFinite yInfinity hCover
      (eval_ne_zero_of_left_unit_certificate
        D yFinite uFinite hFiniteUnit)
      (eval_ne_zero_of_left_unit_certificate
        D yInfinity uInfinity hInfinityUnit)
  have hRat : ∀ t : K, N.eval t / D.eval t = t ^ m :=
    identity_of_two_chart_cover
      (fun t => N.eval t / D.eval t)
      (fun t => t ^ m)
      yFinite yInfinity hCover hFiniteRat hInfinityRat
  exact rational_power_pair_of_nonvanishing_denominator
    N D (fun t : K => t) Function.surjective_id m hD hRat

/--
Monic normalisation of the two-chart polynomial-target theorem.
-/
theorem rational_identity_of_monic_two_chart_unit_certificates
    {SFinite SInfinity : Type*}
    (N D P : K[X])
    (yFinite uFinite : SFinite → K)
    (yInfinity uInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (hMonic : D.Monic)
    (hFiniteUnit : ∀ s, uFinite s * D.eval (yFinite s) = 1)
    (hInfinityUnit : ∀ s, uInfinity s * D.eval (yInfinity s) = 1)
    (hFiniteRat :
      ∀ s, N.eval (yFinite s) / D.eval (yFinite s) = P.eval (yFinite s))
    (hInfinityRat :
      ∀ s, N.eval (yInfinity s) / D.eval (yInfinity s) = P.eval (yInfinity s)) :
    D = 1 ∧ N = P := by
  have hD : ∀ t : K, D.eval t ≠ 0 :=
    eval_ne_zero_of_two_chart_cover
      D yFinite yInfinity hCover
      (eval_ne_zero_of_left_unit_certificate
        D yFinite uFinite hFiniteUnit)
      (eval_ne_zero_of_left_unit_certificate
        D yInfinity uInfinity hInfinityUnit)
  have hRat : ∀ t : K, N.eval t / D.eval t = P.eval t :=
    identity_of_two_chart_cover
      (fun t => N.eval t / D.eval t)
      (fun t => P.eval t)
      yFinite yInfinity hCover hFiniteRat hInfinityRat
  exact rational_identity_of_monic_nonvanishing_denominator
    N D P (fun t : K => t) Function.surjective_id hMonic hD hRat

/-- Fully normalised power-target conclusion from the two chart certificates. -/
theorem rational_power_pair_of_monic_two_chart_unit_certificates
    {SFinite SInfinity : Type*}
    (N D : K[X])
    (yFinite uFinite : SFinite → K)
    (yInfinity uInfinity : SInfinity → K)
    (hCover : TwoChartCover yFinite yInfinity)
    (m : ℕ)
    (hMonic : D.Monic)
    (hFiniteUnit : ∀ s, uFinite s * D.eval (yFinite s) = 1)
    (hInfinityUnit : ∀ s, uInfinity s * D.eval (yInfinity s) = 1)
    (hFiniteRat :
      ∀ s, N.eval (yFinite s) / D.eval (yFinite s) = (yFinite s) ^ m)
    (hInfinityRat :
      ∀ s, N.eval (yInfinity s) / D.eval (yInfinity s) = (yInfinity s) ^ m) :
    D = 1 ∧ N = X ^ m := by
  have hD : ∀ t : K, D.eval t ≠ 0 :=
    eval_ne_zero_of_two_chart_cover
      D yFinite yInfinity hCover
      (eval_ne_zero_of_left_unit_certificate
        D yFinite uFinite hFiniteUnit)
      (eval_ne_zero_of_left_unit_certificate
        D yInfinity uInfinity hInfinityUnit)
  have hRat : ∀ t : K, N.eval t / D.eval t = t ^ m :=
    identity_of_two_chart_cover
      (fun t => N.eval t / D.eval t)
      (fun t => t ^ m)
      yFinite yInfinity hCover hFiniteRat hInfinityRat
  exact rational_power_pair_of_monic_nonvanishing_denominator
    N D (fun t : K => t) Function.surjective_id m hMonic hD hRat

end AlgebraicallyClosedField

end HC4.RationalRigidity
