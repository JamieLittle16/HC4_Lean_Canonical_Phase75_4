import HC4.Polynomial.RankThreeCubicDetOneSourceRankThreeIsotropicFromCofactor
import Mathlib.Tactic

/-!
# Source rank-three isotropy without an assumed kernel-line interface

The prior source isotropy lemma required that the full cubic Hessian
kernel be a line. At a genuine pole we have a fixed nonzero transverse
kernel v with a ground-field coefficient, and a rank-three principal
cofactor pivot supplies that line property automatically.

Crucially, the principal cofactor hypothesis remains explicit: it is
the actual rank-three branch and must not be inferred solely from the
rank-two transverse 3x3 Hessian.
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

/-- A source pole's genuine nonzero full cubic kernel and a surviving
full principal cofactor already imply ground-field quadratic isotropy.
No separate full-kernel-line premise is required. -/
theorem sourceCubic_rankThreePoleKernel_quadraticTransverse_isotropic_of_cofactor
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
    W ≠ 0 →
    A *ᵥ v = 0 →
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
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  change W ≠ 0 → A *ᵥ v = 0 →
    A.adjugate (.inr k) (.inr k) ≠ 0 → _
  intro hW hAker hkk
  have hv : v ≠ 0 := by
    intro hz
    apply hW
    funext j
    have hj := congrFun hz (.inr j)
    simpa [v] using hj
  have hvk : v (.inr k) ≠ 0 :=
    principalCofactor_kernel_coordinate_ne_zero
      A v (.inr k) hkk hAker hv
  have hwk : w k ≠ 0 := by
    intro hz
    apply hvk
    change q (MvPolynomial.C (w k)) = 0
    simp [hz]
  exact sourceCubic_rankThreePoleKernel_isotropic_of_cofactor
    F a p ell hlin hp hcap hdetOne w k hwk hAker hkk

end
end HC4.Polynomial.RankThreeCubic
