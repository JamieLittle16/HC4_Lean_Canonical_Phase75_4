import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import Mathlib.Tactic

/-!
# Source rank-three isotropy without an assumed kernel-line certificate

The generic principal-cofactor theorem proves the previously
conditional one-dimensional kernel statement directly in the
actual irreducible pole quotient.

The only extra witness needed is a nonzero K-rational transverse
coordinate at the surviving principal cofactor. Its image in
K[y]/(p) is a unit because it is a nonzero ground-field constant.
This is an algebraic fact, not an additional source endpoint.

The result still imposes isotropy, not annihilation of the
genuine nonzero quadratic transverse repair.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- Under a genuine irreducible linear pole, a nonzero
transverse coordinate and surviving principal cofactor
make the kernel line automatic. The weight-five trace
identity therefore gives isotropy without that assumption. -/
theorem sourceCubic_rankThreePoleKernel_isotropic_of_cofactor
    (F : SB K) (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hp : Irreducible p)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w : Fin 3 → K) (k : Fin 3) (hwk : w k ≠ 0) :
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
    A.adjugate (.inr k) (.inr k) ≠ 0 →
    (∑ i : Fin 3, ∑ j : Fin 3, w i * T2 i j * w j) = 0 := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
    q.comp (referenceSlice a).toRingHom
  let A := φ.mapMatrix (hessian L3)
  let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    Sum.elim (fun _ : Unit => 0) W
  change A *ᵥ v = 0 → A.adjugate (.inr k) (.inr k) ≠ 0 → _
  intro hAker hkk
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hunitK : IsUnit (w k) :=
    isUnit_iff_ne_zero.mpr hwk
  have hunit : IsUnit (v (.inr k)) := by
    change IsUnit (q (MvPolynomial.C (w k)))
    exact hunitK.map (q.comp (MvPolynomial.C : K →+* B3 K))
  have hline : ∀ z : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}),
      A *ᵥ z = 0 →
        ∃ c : (B3 K ⧸ Ideal.span {p}),
          ∀ i, z i = c * v i :=
    principalCofactor_kernelLine_of_unitCoordinate
      A v (.inr k) hkk hAker hunit
  exact sourceCubic_rankThreePoleKernel_quadraticTransverse_isotropic
    F a p ell hlin hp hcap hdetOne w k hAker hline hkk

end
end HC4.Polynomial.RankThreeCubic
