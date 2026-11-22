import HC4.Polynomial.RankThreeCubicDetOneAlignedMixedPairing
import HC4.Polynomial.RankThreeCubicSourceFourHessianKernelPole
import Mathlib.Tactic

/-!
# A nonzero constant tangent vector survives the genuine pole quotient

Let p be the genuine irreducible denominator prime of the transverse
source polynomial ring. An invertible constant frame M takes a
nonzero constant tangent vector (0,r,t) to a nonzero vector W.
Since K embeds in the prime quotient K[y]/(p), W remains nonzero
after reduction modulo p.

This allows applying the determinant-one matrix repair theorem to
the fixed tangent vector itself, avoiding any need to identify
two independently selected normalized residue witnesses.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- A source-derived constant tangent kernel vector remains
nonzero in the quotient by any irreducible transverse prime. -/
theorem fixedTangent_nonzero_in_irreducibleQuotient
    (p : B3 K) (hp : Irreducible p)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (r t : K) (hrt : r ≠ 0 ∨ t ≠ 0) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    (fun i : Fin 3 =>
        q (MvPolynomial.C
          ((M.mulVec ![(0 : K), r, t]) i))) ≠ 0 := by
  classical
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R :=
    Ideal.Quotient.mk (Ideal.span {p})
  let ψ : K →+* R := q.comp MvPolynomial.C
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hψ : Function.Injective ψ :=
    RingHom.injective ψ
  let v : Fin 3 → K := ![(0 : K), r, t]
  intro hW
  have hMv : M *ᵥ v = 0 := by
    funext i
    apply hψ
    have hi := congrFun hW i
    simpa only [ψ, q, v, Pi.zero_apply] using hi
  have hv : v = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hM hMv
  have hr : r = 0 := by
    have hi := congrFun hv (1 : Fin 3)
    simpa [v] using hi
  have ht : t = 0 := by
    have hi := congrFun hv (2 : Fin 3)
    simpa [v] using hi
  rcases hrt with hrt | hrt
  · exact hrt hr
  · exact hrt ht

end
end HC4.Polynomial.RankThreeCubic
