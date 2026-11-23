import HC4.Polynomial.RankThreeCubicLinearHyperplaneVanishingDivisibility
import HC4.Polynomial.RankThreeCubicPrincipalKernelPivot
import Mathlib.Tactic

/-!
# Elimination of the fixed-kernel no-transverse-repair pole by all cofactors

The three-scale determinant-one argument shows that on the actual
pole plane every cubic principal cofactor indexed by k with
w[k]!=0 vanishes.

If w[k]=0 instead, the very same fixed nonzero vector is in
the cubic transverse Hessian kernel on the plane. A nonzero
principal cofactor at k would force w[k]!=0, contradicting
the zero-coordinate hypothesis. Thus the cubic principal
cofactor vanishes on the plane for EVERY k.

The proved linear-hyperplane vanishing lemma upgrades this to
the exact polynomial statement

    p | adj(H3)[k,k]  for every k,

where H3 is the actual cubic source transverse Hessian.

No extra condition on a preferred cofactor index is needed.
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

/-- In the genuine fixed-kernel no-quadratic-transverse-repair
configuration, EVERY principal cofactor of the ORIGINAL cubic
Hessian is divisible by the genuine pole's linear equation. -/
theorem sourceCubic_fixedPoleKernel_allCubicPrincipalCofactors_dvd
    (F : SB K) (a : K) (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w : Fin 3 → K) (hw : w ≠ 0) :
    let L3 : SB K := initialForm transverseCubicWeight 3 F
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A := φ.mapMatrix (hessian L3)
    let C := φ.mapMatrix (hessian L2)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) →
    p ∣ (∑ j : Fin 3,
      referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
        MvPolynomial.C (w j)) →
    ∀ k : Fin 3,
      p ∣ (sourceTransverseHessian a L3).adjugate k k := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let H3 : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L3
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
  change A *ᵥ v = 0 →
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) → _ → _
  intro hAker hCrows hdvd k
  apply linearHyperplane_dvd_of_vanishes_on_plane
    p (H3.adjugate k k) ell hlin hell
  intro z hpz
  by_cases hwk : w k = 0
  · let evalz : B3 K →+* K :=
      (MvPolynomial.aeval z).toRingHom
    have hqrows (i : Fin 3) :
        q (∑ j : Fin 3, H3 i j * MvPolynomial.C (w j)) = 0 := by
      have hi := congrFun hAker (.inr i)
      have hrow :
          (∑ j : Fin 3,
            q (H3 i j) * q (MvPolynomial.C (w j))) = 0 := by
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          A, φ, v, W, H3, sourceTransverseHessian] using hi
      simpa only [map_sum, map_mul] using hrow
    have hkerRows (i : Fin 3) :
        (∑ j : Fin 3, (H3.map evalz) i j * w j) = 0 := by
      have hz := poleQuotient_zero_implies_pointEval_zero
        p (∑ j : Fin 3, H3 i j * MvPolynomial.C (w j))
        z hpz (hqrows i)
      simpa only [map_sum, map_mul, MvPolynomial.aeval_C,
        Matrix.map_apply] using hz
    have hker : (H3.map evalz) *ᵥ w = 0 := by
      funext i
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using
        hkerRows i
    by_contra hcof
    have hmap : (H3.map evalz).adjugate =
        H3.adjugate.map evalz := (evalz.map_adjugate H3).symm
    have hnonzero : (H3.map evalz).adjugate k k ≠ 0 := by
      rw [hmap]
      exact hcof
    exact (principalCofactor_kernelVector_pivot_ne_zero
      (H3.map evalz) w hker hw k hnonzero) hwk
  · exact sourceCubic_fixedPoleKernel_cubicCofactor_vanishes_on_plane
      F a p ell hlin hcap hdetOne w hw k hwk
      hAker hCrows hdvd z hpz

end
end HC4.Polynomial.RankThreeCubic
