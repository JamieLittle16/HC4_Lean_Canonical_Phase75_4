import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicPoleQuotientPointEvaluation
import Mathlib.Tactic

/-!
# The rank-three leading-Hessian subcase has isotropic quadratic transverse repair

The genuine cubic pole classification supplies a fixed nonzero
transverse vector w annihilated by the FULL cubic Hessian modulo p,
and a nonzero quadratic transverse repair T2*w.

On the subcase where this full cubic Hessian has a one-dimensional
kernel and a surviving full 4x4 principal cofactor, the source's
weight-five adjugate trace equation forces

   wᵀ T2 w = 0.

The transverse repair T2*w can nevertheless be nonzero:
isotropy does not mean annihilation. In particular the theorem
below deliberately keeps the rank-three/line-kernel premises
explicit. We do NOT assert them from rank two of the transverse
3x3 Hessian, nor infer a contradiction from this equation alone.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- Source-honest isotropy of the quadratic transverse correction
in the rank-three full cubic-Hessian pole chart. -/
theorem sourceCubic_rankThreePoleKernel_quadraticTransverse_isotropic
    (F : SB K) (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hp : Irreducible p)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w : Fin 3 → K) (k : Fin 3) :
    let L3 : SB K := initialForm transverseCubicWeight 3 F
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A := φ.mapMatrix (hessian L3)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    let T2 : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (referenceSlice a
        (hessian L2 (.inr i) (.inr j))).coeff 0
    A *ᵥ v = 0 →
    (∀ z : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}),
      A *ᵥ z = 0 →
        ∃ c : (B3 K ⧸ Ideal.span {p}),
          ∀ i, z i = c * v i) →
    A.adjugate (.inr k) (.inr k) ≠ 0 →
    (∑ i : Fin 3, ∑ j : Fin 3,
      w i * T2 i j * w j) = 0 := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  change A *ᵥ v = 0 → _ → A.adjugate (.inr k) (.inr k) ≠ 0 → _
  intro hAker hline hkk
  have hSym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change φ (pderiv i (pderiv j L3)) =
      φ (pderiv j (pderiv i L3))
    rw [HC4.Newton.pderiv_comm_backport i j L3]
  have htrace : (A.adjugate * C).trace = 0 :=
    sourceCubic_detOne_slicedPole_firstCorrection_trace_zero
      F hcap hdetOne a p
  have hfull :
      (∑ i : Unit ⊕ Fin 3,
        ∑ j : Unit ⊕ Fin 3, v i * C i j * v j) = 0 :=
    symmetric_kernelLine_adjugateTrace_zero_implies_isotropic
      A C hSym v hAker hline (.inr k) hkk htrace
  have htrans :
      (∑ i : Fin 3,
        ∑ j : Fin 3, W i * C (.inr i) (.inr j) * W j) = 0 := by
    simpa [v, Fintype.sum_sum_type] using hfull
  have hCij (i j : Fin 3) :
      C (.inr i) (.inr j) = q (MvPolynomial.C (T2 i j)) := by
    change q (referenceSlice a (hessian L2 (.inr i) (.inr j))) =
      q (MvPolynomial.C
        ((referenceSlice a (hessian L2 (.inr i) (.inr j))).coeff 0))
    rw [sourceCubic_secondLayer_transverseSlice_eq_C F a i j]
    simp only [MvPolynomial.coeff_zero_C]
  let scalar : K :=
    ∑ i : Fin 3, ∑ j : Fin 3, w i * T2 i j * w j
  have hscalarq :
      q (MvPolynomial.C scalar) =
        (∑ i : Fin 3,
          ∑ j : Fin 3, W i * C (.inr i) (.inr j) * W j) := by
    dsimp [scalar]
    simp only [map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hCij]
  have hzeroq : q (MvPolynomial.C scalar) = 0 :=
    hscalarq.trans htrans
  have hpzero : MvPolynomial.aeval
      (fun _ : Fin 3 => (0 : K)) p = 0 :=
    linearPole_originEval_eq_zero p ell hlin
  have hz : MvPolynomial.aeval
      (fun _ : Fin 3 => (0 : K)) (MvPolynomial.C scalar) = 0 :=
    poleQuotient_zero_implies_pointEval_zero
      p (MvPolynomial.C scalar) (fun _ => 0) hpzero hzeroq
  simpa only [MvPolynomial.aeval_C] using hz

end
end HC4.Polynomial.RankThreeCubic
