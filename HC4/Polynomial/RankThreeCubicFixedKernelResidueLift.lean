import HC4.Polynomial.RankThreeCubicFixedKernelPolynomialLift
import Mathlib.Tactic

/-!
# Polynomial tangent-kernel lifting into the genuine residue quotient

The polynomial row-divisibility theorem immediately produces a
kernel in K[y]/(p): a fixed vector in the original base field,
obtained by applying the adapted invertible frame to (0,r,t).

This is an exact quotient identity, not a pointwise equation in
the base field. It makes comparison with the actual normalized
source characteristic residue possible over the same ring.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- A fixed tangent kernel of a homogeneous-linear Hessian
on the pole plane becomes a kernel of its reduction modulo p. -/
theorem homogeneousLinearMatrix_fixedTangentKernel_modPole
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hhom : ∀ i j : Fin 3, (H i j).IsHomogeneous 1)
    (p : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (r t : K)
    (hfixed : ∀ u v : K,
      let A := H.map
        (MvPolynomial.aeval (M.mulVec ![(0 : K), u, v])).toRingHom
      (M.transpose * A * M) *ᵥ ![(0 : K), r, t] = 0) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun i => q (MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i))
    (H.map q) *ᵥ W = 0 := by
  classical
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let W : Fin 3 → R :=
    fun i => q (MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i))
  have hrows := homogeneousLinearMatrix_tangentKernel_rows_divisible
    H hhom p ell hpoly hell M hM hM1 hM2 r t hfixed
  have hqp : q p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (dvd_refl p))
  funext i
  obtain ⟨z, hz⟩ := hrows i
  have hzero :
      q (∑ j : Fin 3, H i j *
        MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) j)) = 0 := by
    rw [hz, map_mul, hqp, zero_mul]
  change (∑ j : Fin 3,
    q (H i j) *
      q (MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) j))) = 0
  simpa only [map_sum, map_mul] using hzero

end
end HC4.Polynomial.RankThreeCubic
