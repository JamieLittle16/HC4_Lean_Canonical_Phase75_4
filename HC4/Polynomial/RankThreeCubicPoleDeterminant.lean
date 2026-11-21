import HC4.Polynomial.RankThreeCubicSourceLinearOrPole
import Mathlib.Tactic

/-!
# Cramer's identity and the cubic characteristic pole divisor

For a polynomial matrix H, a solution W over the fraction field of
H W = r is polynomial whenever det H is a unit in the polynomial ring.
The adjugate identity gives the exact polynomial numerator and
ensures any genuine pole must be supported by the determinant.
The source determinant is already nonunit by cubic homogeneity, so the
nonunit corollary alone is not a new exclusion. No irreducible prime
or terminal contradiction is claimed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev P3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev FF3 (K : Type*) [Field K] := FractionRing (P3 K)

/-- Exact Cramer's numerator identity for any polynomial transverse
matrix equation solved by a rational characteristic. This is the
denominator control needed in the pole branch: every coordinate of
the velocity is the adjugate numerator divided by `det H`. -/
theorem fractionKernel_adjugate_numerator_identity
    (H : Matrix (Fin 3) (Fin 3) (P3 K))
    (r : Fin 3 → P3 K)
    (V : Fin 3 → FF3 K)
    (hkernel : (H.map (algebraMap (P3 K) (FF3 K))) *ᵥ V =
      fun i => algebraMap (P3 K) (FF3 K) (r i))
    (i : Fin 3) :
    algebraMap (P3 K) (FF3 K) H.det * V i =
      algebraMap (P3 K) (FF3 K) ((H.adjugate *ᵥ r) i) := by
  classical
  let g : P3 K →+* FF3 K := algebraMap (P3 K) (FF3 K)
  have hk : (H.map g) *ᵥ V = fun j => g (r j) := hkernel
  have hadj :
      (H.map g).det • V =
        (H.map g).adjugate *ᵥ (fun j => g (r j)) := by
    have h := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) (FF3 K) => M *ᵥ V)
      (Matrix.adjugate_mul (H.map g))
    have hh : (H.map g).det • V =
        (H.map g).adjugate *ᵥ ((H.map g) *ᵥ V) := by
      simpa only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec] using h.symm
    rw [hk] at hh
    exact hh
  have hmapadj :
      ((H.map g).adjugate *ᵥ (fun j => g (r j))) i =
        g ((H.adjugate *ᵥ r) i) := by
    have hm : (H.map g).adjugate = (H.adjugate).map g := by
      simpa only [RingHom.mapMatrix] using (g.map_adjugate H).symm
    rw [hm]
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hdetmap : (H.map g).det = g H.det := by
    simpa only [RingHom.mapMatrix] using (RingHom.map_det g H).symm
  have hi := congrFun hadj i
  simpa only [Pi.smul_apply, smul_eq_mul, hdetmap, hmapadj] using hi

/-- A non-polynomial solution to a polynomial matrix equation cannot
occur when the matrix determinant is a unit. This holds without any
homogeneity assumptions. -/
theorem det_not_isUnit_of_nonPolynomial_fractionKernel
    (H : Matrix (Fin 3) (Fin 3) (P3 K))
    (r : Fin 3 → P3 K)
    (V : Fin 3 → FF3 K)
    (hkernel : (H.map (algebraMap (P3 K) (FF3 K))) *ᵥ V =
      fun i => algebraMap (P3 K) (FF3 K) (r i))
    (hnonpolynomial : ∃ i : Fin 3, ∀ p : P3 K,
      algebraMap (P3 K) (FF3 K) p ≠ V i) :
    ¬ IsUnit H.det := by
  classical
  intro hunit
  obtain ⟨u, hu⟩ := hunit
  let g : P3 K →+* FF3 K := algebraMap (P3 K) (FF3 K)
  let c : P3 K := (u⁻¹ : (P3 K)ˣ)
  have hc : c * H.det = 1 := by
    change (↑(u⁻¹) : P3 K) * H.det = 1
    rw [← hu]
    simp
  have hgunit : g c * g H.det = 1 := by
    calc
      g c * g H.det = g (c * H.det) := (map_mul g c H.det).symm
      _ = g 1 := by rw [hc]
      _ = 1 := by simp
  have hscalar (i : Fin 3) :
      g H.det * V i = g ((H.adjugate *ᵥ r) i) :=
    fractionKernel_adjugate_numerator_identity H r V hkernel i
  obtain ⟨i, hi⟩ := hnonpolynomial
  let p : P3 K := c * (H.adjugate *ᵥ r) i
  have hp : g p = V i := by
    calc
      g p = g c * g ((H.adjugate *ᵥ r) i) := by simp [p]
      _ = g c * (g H.det * V i) := by rw [hscalar i]
      _ = V i := by rw [← mul_assoc, hgunit, one_mul]
  exact hi p hp

/-- At cubic cap and full transverse Hessian rank, the actual source
characteristic is either constant-linear, or the specialized
transverse Hessian determinant is a nonunit polynomial.

In the latter case its zero divisor is now a necessary obstruction,
not merely an arbitrary denominator appearing in a fraction. -/
theorem exists_sourceCubic_linear_or_nonunit_determinant [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FF3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (P3 K) (FF3 K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          (algebraMap (P3 K) (FF3 K))
            (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              (algebraMap (P3 K) (FF3 K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ ¬ IsUnit (sourceTransverseHessian a L).det) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linearVelocity_or_nonPolynomial F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnon
  · exact Or.inl hlin
  · right
    exact det_not_isUnit_of_nonPolynomial_fractionKernel
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F))
      (sourceNegativeMixedHessian a
        (initialForm transverseCubicWeight 3 F))
      (fun i => V (.inr i)) heq hnon


/-- A genuine pole cannot have all Cramer's numerators divisible by the
transverse Hessian determinant.  This preserves the *exact* denominator,
rather than just proving that it is a nonunit. -/
theorem exists_adjugate_numerator_not_dvd_of_nonPolynomial_fractionKernel
    (H : Matrix (Fin 3) (Fin 3) (P3 K))
    (r : Fin 3 → P3 K)
    (V : Fin 3 → FF3 K)
    (hdet : H.det ≠ 0)
    (hkernel : (H.map (algebraMap (P3 K) (FF3 K))) *ᵥ V =
      fun i => algebraMap (P3 K) (FF3 K) (r i))
    (hnonpolynomial : ∃ i : Fin 3, ∀ p : P3 K,
      algebraMap (P3 K) (FF3 K) p ≠ V i) :
    ∃ i : Fin 3, ¬ H.det ∣ (H.adjugate *ᵥ r) i := by
  classical
  let g : P3 K →+* FF3 K := algebraMap (P3 K) (FF3 K)
  have hg : Function.Injective g :=
    IsFractionRing.injective (P3 K) (FF3 K)
  have hdet' : g H.det ≠ 0 := fun hz => hdet (hg (by simpa using hz))
  obtain ⟨i, hi⟩ := hnonpolynomial
  refine ⟨i, ?_⟩
  rintro ⟨p, hp⟩
  have hnum : g H.det * V i = g ((H.adjugate *ᵥ r) i) :=
    fractionKernel_adjugate_numerator_identity H r V hkernel i
  have hcancel : g H.det * V i = g H.det * g p := by
    calc
      g H.det * V i = g ((H.adjugate *ᵥ r) i) := hnum
      _ = g (H.det * p) := by rw [hp]
      _ = g H.det * g p := map_mul g _ _
  have hV : V i = g p := mul_left_cancel₀ hdet' hcancel
  exact hi p hV.symm

/-- A genuinely non-polynomial rational Hessian characteristic supplies
a nonzero kernel vector over the *entire determinantal quotient*.

Unlike a naive reduction modulo one irreducible factor, this statement
does not lose information when the determinant has repeated factors.
It is a scheme-level kernel, not yet a nonzero kernel over a residue
field of a height-one prime; extracting that is a separate task. -/
theorem exists_determinantalQuotient_kernel_of_nonPolynomial_fractionKernel
    (H : Matrix (Fin 3) (Fin 3) (P3 K))
    (r : Fin 3 → P3 K)
    (V : Fin 3 → FF3 K)
    (hdet : H.det ≠ 0)
    (hkernel : (H.map (algebraMap (P3 K) (FF3 K))) *ᵥ V =
      fun i => algebraMap (P3 K) (FF3 K) (r i))
    (hnonpolynomial : ∃ i : Fin 3, ∀ p : P3 K,
      algebraMap (P3 K) (FF3 K) p ≠ V i) :
    ∃ S : Fin 3 → (P3 K ⧸ Ideal.span {H.det}),
      S ≠ 0 ∧
      (H.map (Ideal.Quotient.mk (Ideal.span {H.det}))) *ᵥ S = 0 := by
  classical
  let I : Ideal (P3 K) := Ideal.span {H.det}
  let q : P3 K →+* (P3 K ⧸ I) := Ideal.Quotient.mk I
  let S : Fin 3 → (P3 K ⧸ I) :=
    fun i => q ((H.adjugate *ᵥ r) i)
  obtain ⟨i, hi⟩ :=
    exists_adjugate_numerator_not_dvd_of_nonPolynomial_fractionKernel
      H r V hdet hkernel hnonpolynomial
  have hSi : S i ≠ 0 := by
    intro hz
    apply hi
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hS : S ≠ 0 := by
    intro hz
    exact hSi (by simpa using congrFun hz i)
  have hdetzero : q H.det = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self _
  have hadj : H *ᵥ (H.adjugate *ᵥ r) = H.det • r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hker : (H.map q) *ᵥ S = 0 := by
    funext j
    change (∑ k : Fin 3, q (H j k) * q ((H.adjugate *ᵥ r) k)) = 0
    calc
      _ = q ((H *ᵥ (H.adjugate *ᵥ r)) j) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      _ = q (H.det * r j) := by
        rw [hadj]
        rfl
      _ = 0 := by rw [map_mul, hdetzero, zero_mul]
  exact ⟨S, hS, hker⟩

/-- The actual full-rank cubic source gives either a constant-linear
characteristic or a nonzero vector in the determinantal quotient killed
by its actual transverse Hessian.  No independent pole divisor,
residue-field kernel, or endpoint hypothesis is introduced. -/
theorem exists_sourceCubic_linear_or_determinantalQuotient_kernel [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FF3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (P3 K) (FF3 K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          (algebraMap (P3 K) (FF3 K))
            (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              (algebraMap (P3 K) (FF3 K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨
        (∃ S : Fin 3 → (P3 K ⧸ Ideal.span {
              (sourceTransverseHessian a L).det}),
          S ≠ 0 ∧
          ((sourceTransverseHessian a L).map
              (Ideal.Quotient.mk
                (Ideal.span {(sourceTransverseHessian a L).det}))) *ᵥ S = 0)) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linearVelocity_or_nonPolynomial F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnon
  · exact Or.inl hlin
  · exact Or.inr
      (exists_determinantalQuotient_kernel_of_nonPolynomial_fractionKernel
        (sourceTransverseHessian a
          (initialForm transverseCubicWeight 3 F))
        (sourceNegativeMixedHessian a
          (initialForm transverseCubicWeight 3 F))
        (fun i => V (.inr i)) hreg heq hnon)

end
end HC4.Polynomial.RankThreeCubic
