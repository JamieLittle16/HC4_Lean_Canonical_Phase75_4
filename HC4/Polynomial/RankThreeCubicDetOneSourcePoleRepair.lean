import HC4.Polynomial.RankThreeCubicSourceFourHessianKernelPole
import HC4.Polynomial.RankThreeCubicSourceUnconditionalRankTwoTransport
import HC4.Polynomial.HessianDeterminant
import Mathlib.Tactic

/-!
# Determinant-one forces genuine lower-layer repair of a cubic pole residue

A genuine reduced denominator pole p of a source cubic characteristic
comes with a nonzero, denominator-normalized residue S in the prime
quotient K[y]/(p). The source gradient transport implies that the
full FOUR-variable Hessian of the cubic initial form kills (0,S)
modulo p. This statement does not depend on whether p is exactly
double or triple in the transverse Hessian determinant.

If the ORIGINAL source F has Hessian determinant one, its full
Hessian remains invertible after the same longitudinal slice and
prime-quotient reduction. Hence the complementary lower transverse
source layers MUST act nontrivially on (0,S).

The theorem below uses one and the same F, a, V, p, S and quotient.
It is a necessary repair condition, not yet a contradiction: the
remaining work is to constrain the correction's weighted layers
and show that no compatible repair can occur.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

/-- A determinant-one matrix cannot retain a nonzero kernel vector
after a correction if the correction also kills that vector.
This works over any commutative ring, including a prime quotient. -/
theorem detOne_matrix_correction_nonzero_on_kernel
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A E : Matrix ι ι R) (w : ι → R)
    (hdet : (A + E).det = 1)
    (hAw : A *ᵥ w = 0)
    (hw : w ≠ 0) :
    E *ᵥ w ≠ 0 := by
  intro hEw
  have hsum : (A + E) *ᵥ w = 0 := by
    rw [Matrix.add_mulVec, hAw, hEw]
    simp
  have hadj : (A + E).adjugate * (A + E) = 1 := by
    rw [Matrix.adjugate_mul, hdet]
    simp
  have h := congrArg (fun M : Matrix ι ι R => M *ᵥ w) hadj
  rw [Matrix.mulVec_mulVec, hsum] at h
  have hzero : w = 0 := by simpa using h.symm
  exact hw hzero

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- On EVERY genuine rank-two cubic denominator pole, including the
exact-triple case, the nonzero normalized source residue is killed by
the full cubic Hessian. But under determinant one it is NOT killed
by the difference of the full original and cubic Hessians.

All matrices are evaluated at the source's same longitudinal
anchor and then reduced modulo its actual denominator prime.
No source-layer compatibility is assumed beyond the original
determinant-one equation. -/
theorem sourceCubic_genuinePole_detOne_forces_lowerLayerRepair
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hdetOne : hessianDeterminant F = 1)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (u : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u))) :
    let L := initialForm transverseCubicWeight 3 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) :=
      fun i j => q (referenceSlice a (pderiv j (pderiv i L)))
    let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) :=
      fun i j => q (referenceSlice a (pderiv j (pderiv i F)))
    ∃ (k : Fin 3) (S : Fin 3 → (B3 K ⧸ Ideal.span {p})),
      S k ≠ 0 ∧
      A *ᵥ (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) = 0 ∧
      (B - A) *ᵥ
        (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) ≠ 0 := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    fun i j => q (referenceSlice a (pderiv j (pderiv i L)))
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    fun i j => q (referenceSlice a (pderiv j (pderiv i F)))
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨k, s, T, hk, hps, hscale, hSk, hSker, halign, htime⟩ :=
    sourceCubic_genuinePole_unconditionalRankTwo_allTimeContractions
      F a V hV hgrad hregular u p hp hpd hpn
  let S : Fin 3 → R := fun j => q (T j)
  let w : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) S
  have hrowDiv : p ∣ ∑ j : Fin 3,
      referenceSlice a (pderiv (.inr j) (pderiv (.inl ()) L)) * T j :=
    sourceCubic_normalizedPole_longitudinalMixedRow_divisible
      F a V hV hgrad p s hps T hscale
  have hmixed : (∑ j : Fin 3, A (.inl ()) (.inr j) * S j) = 0 := by
    have hz : q (∑ j : Fin 3,
        referenceSlice a (pderiv (.inr j) (pderiv (.inl ()) L)) * T j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr hrowDiv)
    simpa only [A, S, map_sum, map_mul] using hz
  have htrans (i : Fin 3) :
      (∑ j : Fin 3, A (.inr i) (.inr j) * S j) = 0 := by
    have hh := congrFun hSker i
    change (∑ j : Fin 3, q (H i j) * S j) = 0 at hh
    change (∑ j : Fin 3, q (H i j) * S j) = 0
    exact hh
  have hAw : A *ᵥ w = 0 :=
    fourHessian_zeroLongitudinalVector_of_rows A S hmixed htrans
  have hw : w ≠ 0 := by
    intro hz
    have hkzero := congrFun hz (.inr k)
    change S k = 0 at hkzero
    exact hSk hkzero
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  have hBmap : B = (hessian F).map φ := by
    ext i j
    rfl
  have hdetB : B.det = 1 := by
    rw [hBmap, ← RingHom.map_det]
    change φ (hessianDeterminant F) = 1
    rw [hdetOne]
    simp
  have hsum : A + (B - A) = B := by abel
  have hdetSum : (A + (B - A)).det = 1 := by
    rw [hsum]
    exact hdetB
  refine ⟨k, S, hSk, hAw, ?_⟩
  exact detOne_matrix_correction_nonzero_on_kernel
    A (B - A) w hdetSum hAw hw

end
end HC4.Polynomial.RankThreeCubic
