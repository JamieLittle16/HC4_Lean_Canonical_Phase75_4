import HC4.Polynomial.RankThreeCubicSourcePoleLocalJacobi
import HC4.Polynomial.RankThreeCubicSourceLinearOrRepeated
import Mathlib.Tactic

/-!
# Cubic characteristic classification with an actual repeated pole

This strengthens the old source-level "linear or repeated factor"
result: in the nonlinear characteristic branch, the selected repeated
linear factor *is a prime of a reduced coordinate denominator*, and
does not divide that coordinate's reduced numerator.

This matches the next valuation/localization analysis much more
closely than an arbitrary repeated determinant factor does.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A *specified* repeated irreducible factor in a polynomial of
total degree at most three must itself have degree one. -/
theorem degree_one_of_specified_repeated_factor
    (D p : B3 K)
    (hD : D ≠ 0) (hdeg : D.totalDegree ≤ 3)
    (hp : Irreducible p)
    (hpp : p * p ∣ D) :
    p.totalDegree = 1 := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdegsq : (p * p).totalDegree = p.totalDegree + p.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hp0 hp0
  have hle : (p * p).totalDegree ≤ D.totalDegree := by
    obtain ⟨c, hc⟩ := hpp
    have hc0 : c ≠ 0 := by
      intro hz
      apply hD
      rw [hc, hz, mul_zero]
    have hprod : ((p * p) * c).totalDegree =
        (p * p).totalDegree + c.totalDegree :=
      MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero hp0 hp0) hc0
    calc
      (p * p).totalDegree ≤ (p * p).totalDegree + c.totalDegree := by omega
      _ = D.totalDegree := by rw [hc, hprod]
  have hpos : 0 < p.totalDegree := by
    by_contra hn
    have hzero : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hn
    have hconst : p = C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    have hc0 : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp0
      rw [hconst, hc, map_zero]
    have hu : IsUnit p :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
        ⟨isUnit_iff_ne_zero.mpr hc0, hzero⟩
    exact hp.not_isUnit hu
  omega

/-- The nonlinear full-rank cubic characteristic has a genuine reduced
coordinate denominator prime whose square divides the actual source
transverse Hessian determinant. By cubic homogeneity this prime is
necessarily of total degree one.

The same longitudinal slice and characteristic satisfy the full
gradient transport and fraction-field Hessian equation. -/
theorem exists_sourceCubic_linear_or_repeatedGenuinePole
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → F3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V (pderiv i L) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K)) *ᵥ
            (fun i : Fin 3 => V (.inr i)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (F3 K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨
        (∃ (i : Fin 3) (p : B3 K),
          Irreducible p ∧
          p * p ∣ (sourceTransverseHessian a L).det ∧
          p.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr i)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr i)))) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  obtain ⟨V, hV, hgrad⟩ :=
    exists_transverseCubic_characteristic_at a F hcap hdet ha
  have hreg : (sourceTransverseHessian a L).det ≠ 0 :=
    sourceTransverseHessian_det_ne_zero_of_generic a L ha
  have hker :
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K))) *ᵥ
            (fun i : Fin 3 => V (.inr i)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K)
            (sourceNegativeMixedHessian a L i) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  have hg : Function.Injective g :=
    IsFractionRing.injective (B3 K) (F3 K)
  have hH : ∀ i j : Fin 3,
      (sourceTransverseHessian a L i j).IsHomogeneous 1 :=
    sourceCubic_transverseHessian_homogeneous_one a F
  have hr : ∀ i : Fin 3,
      (sourceNegativeMixedHessian a L i).IsHomogeneous 2 :=
    sourceCubic_negativeMixedHessian_homogeneous_two a F
  by_cases hpoly : ∀ i : Fin 3, ∃ v : B3 K, g v = V (.inr i)
  · exact Or.inl
      (exists_linear_matrix_of_poleFree_fractionKernel g hg
        (sourceTransverseHessian a L)
        (sourceNegativeMixedHessian a L)
        (fun i : Fin 3 => V (.inr i))
        hH hr hreg hker hpoly)
  · push_neg at hpoly
    obtain ⟨j, p, hp, hpdet, hpd, hpn⟩ :=
      exists_genuinePolePrime_of_nonPolynomial_fractionKernel
        (sourceTransverseHessian a L)
        (sourceNegativeMixedHessian a L)
        (fun i : Fin 3 => V (.inr i)) hker hpoly
    have hrep : p * p ∣ (sourceTransverseHessian a L).det :=
      sourceCubic_genuinePole_is_repeatedFactor F a V hV hgrad
        j p hp hpd hpn
    have hpdeg : p.totalDegree = 1 :=
      degree_one_of_specified_repeated_factor
        (sourceTransverseHessian a L).det p hreg
        (sourceCubic_transverseHessian_det_homogeneous_three a F).totalDegree_le
        hp hrep
    exact Or.inr ⟨j, p, hp, hrep, hpdeg, hpd, hpn⟩

end
end HC4.Polynomial.RankThreeCubic
