import HC4.Polynomial.RankThreeCubicSourceResidueFixedTangentAlignment
import HC4.Polynomial.RankThreeCubicAnchoredKernel
import Mathlib.Tactic

/-!
# The longitudinal Hessian row survives source-honest pole clearing

The existing cubic source residue work has proved the three
transverse Hessian rows after clearing a genuine rational
denominator. There is a fourth row: the longitudinal derivative
of the source gradient.

This module applies the *actual full* gradient transport to that
row and clears the same normalized polynomial denominator s.
If p divides s, its reduction gives the additional longitudinal
mixed-Hessian row constraint on the actual residue T mod p.

The second lemma shows how this row constraint transports along
a nonzero collinear residue to a fixed constant tangent direction.
Together with the existing full transverse-kernel construction,
this is a bridge toward a full four-variable source Hessian
kernel on the pole plane.

It does NOT assert that the lower source layers vanish, or that
the determinant-one obstruction has yet been closed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The *longitudinal* source gradient equation, cleared using the
same polynomial s and numerator T as the transverse residue,
forces the longitudinal mixed-Hessian contraction to be divisible
by every prime divisor of s. No independent residue equation is
assumed, and the result also holds for non-prime p. -/
theorem sourceCubic_normalizedPole_longitudinalMixedRow_divisible
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
    (p s : B3 K) (hps : p ∣ s)
    (T : Fin 3 → B3 K)
    (hscale : ∀ i : Fin 3,
        algebraMap (B3 K) (F3 K) (T i) =
          algebraMap (B3 K) (F3 K) s * V (.inr i)) :
    p ∣ (∑ i : Fin 3,
      referenceSlice a
        (pderiv (.inr i)
          (pderiv (.inl ())
            (initialForm transverseCubicWeight 3 F))) * T i) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  let d : B3 K :=
    referenceSlice a (pderiv (.inl ()) (pderiv (.inl ()) L))
  let b : Fin 3 → B3 K :=
    fun i => referenceSlice a (pderiv (.inr i) (pderiv (.inl ()) L))
  have hfull :
      MvPolynomial.aeval (transverseGenericPoint a)
          (pderiv (.inl ()) (pderiv (.inl ()) L)) +
        (∑ i : Fin 3,
          MvPolynomial.aeval (transverseGenericPoint a)
            (pderiv (.inr i) (pderiv (.inl ()) L)) *
              V (.inr i)) = 0 := by
    have h := anchored_gradient_implies_hessian_kernel
      L (transverseGenericPoint a) V hgrad (.inl ())
    simpa [Fintype.sum_sum_type, hV] using h
  have hfrac :
      g d + (∑ i : Fin 3, g (b i) * V (.inr i)) = 0 := by
    dsimp only [d, b, g]
    simpa only [referenceSlice_fractionEvaluation] using hfull
  have hsum :
      (∑ i : Fin 3, g (b i) * V (.inr i)) = -g d := by
    linear_combination hfrac
  have hclear :
      g (∑ i : Fin 3, b i * T i) = g (-s * d) := by
    calc
      g (∑ i : Fin 3, b i * T i) =
          ∑ i : Fin 3, g (b i) * g (T i) := by
            simp only [map_sum, map_mul]
      _ = g s * (∑ i : Fin 3, g (b i) * V (.inr i)) := by
            simp only [Fin.sum_univ_three]
            rw [hscale 0, hscale 1, hscale 2]
            ring
      _ = g (-s * d) := by
            rw [hsum]
            simp only [map_mul, map_neg]
            ring
  have hpoly :
      (∑ i : Fin 3, b i * T i) = -s * d :=
    (IsFractionRing.injective (B3 K) (F3 K)) hclear
  change p ∣ ∑ i : Fin 3, b i * T i
  rw [hpoly]
  obtain ⟨q, hq⟩ := hps
  refine ⟨-(q * d), ?_⟩
  rw [hq]
  ring

/-- Source-residue collinearity transfers a vanishing scalar
mixed-Hessian row to its fixed tangent direction. The nonzero
pivot residue is essential: no division by an unproved kernel
coordinate occurs. This is valid in any integral domain. -/
theorem fixedTangent_mixedRow_zero_of_alignedResidue
    {R : Type*} [CommRing R] [IsDomain R]
    (b S W : Fin 3 → R) (k : Fin 3)
    (hSk : S k ≠ 0)
    (halign : ∀ i : Fin 3, S i * W k = W i * S k)
    (hrow : (∑ i : Fin 3, b i * S i) = 0) :
    (∑ i : Fin 3, b i * W i) = 0 := by
  have hrel :
      (∑ i : Fin 3, b i * W i) * S k =
        (∑ i : Fin 3, b i * S i) * W k := by
    simp only [Fin.sum_univ_three]
    linear_combination
      -(b 0) * (halign 0) -
      (b 1) * (halign 1) -
      (b 2) * (halign 2)
  have hzero : (∑ i : Fin 3, b i * W i) * S k = 0 := by
    rw [hrel, hrow, zero_mul]
  exact (mul_eq_zero.mp hzero).resolve_right hSk

end
end HC4.Polynomial.RankThreeCubic
