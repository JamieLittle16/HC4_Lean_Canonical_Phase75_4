import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePoleTransverseRepairOrTriple
import HC4.Polynomial.RankThreeCubicDetOneSourceTransverseThreeScale
import Mathlib.Tactic

/-!
# The surviving transverse quadratic repair has a ground-field source witness

A nonzero transverse component of the quadratic source Hessian
acting on a constant pole-plane kernel in K[y]/(p) already comes
from a nonzero scalar in K.

This is because the transverse Hessian of the actual source
weight-two layer is independent of transverse coordinates.
We thereby upgrade the nontriple conclusion to the original
quadratic transverse source matrix acting nontrivially on a
nonzero tangent vector over K, with no new endpoint assumptions.

The transverse repair and exact-triple alternatives are not
claimed to be impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] :=
  FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- In the genuine quadratic source layer, the quotient
transverse response along a constant vector is exactly the
quotient of an ORIGINAL ground-field scalar coefficient. -/
theorem sourceCubic_quadraticTransverseRepair_quotient_eq_C
    (F : SB K) (a : K) (p : B3 K)
    (w : Fin 3 → K) (i : Fin 3) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let C2 := φ.mapMatrix (hessian L2)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    let T2 : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (referenceSlice a
        (hessian L2 (.inr i) (.inr j))).coeff 0
    (C2 *ᵥ v) (.inr i) =
      q (MvPolynomial.C (∑ j : Fin 3, T2 i j * w j)) := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let C2 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  have hP (j : Fin 3) :
      referenceSlice a (hessian L2 (.inr i) (.inr j)) =
        MvPolynomial.C (T2 i j) :=
    sourceCubic_secondLayer_transverseSlice_eq_C F a i j
  have hsum :
      (∑ j : Fin 3,
        referenceSlice a (hessian L2 (.inr i) (.inr j)) *
          MvPolynomial.C (w j)) =
        MvPolynomial.C (∑ j : Fin 3, T2 i j * w j) := by
    calc
      _ = ∑ j : Fin 3,
            MvPolynomial.C (T2 i j) * MvPolynomial.C (w j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hP j]
      _ = _ := by
          simp only [← map_mul, ← map_sum]
  have hresp : (C2 *ᵥ v) (.inr i) =
      q (∑ j : Fin 3,
        referenceSlice a (hessian L2 (.inr i) (.inr j)) *
          MvPolynomial.C (w j)) := by
    simp [C2, v, W, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, φ, q, map_sum, map_mul]
  exact hresp.trans (congrArg q hsum)

/-- For every genuine denominator pole, either the actual
quadratic source transverse Hessian at the transverse origin
has a nonzero response to a fixed nonzero tangent direction,
or the cubic transverse Hessian determinant has the exact
scalar-triple factor. -/
theorem sourceCubic_genuinePole_detOne_originQuadraticTransverseRepair_or_exactTriple
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
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
    let L3 := initialForm transverseCubicWeight 3 F
    let L2 := initialForm transverseCubicWeight 2 F
    let H := sourceTransverseHessian a L3
    (∃ (ell : Fin 3 → K)
        (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
      let T2 : Matrix (Fin 3) (Fin 3) K :=
        fun i j => (referenceSlice a
          (hessian L2 (.inr i) (.inr j))).coeff 0
      ∃ i : Fin 3, (∑ j : Fin 3, T2 i j * w0 j) ≠ 0)
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, htrace, ⟨i, hi⟩⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_exactTriple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    have hresponse :=
      sourceCubic_quadraticTransverseRepair_quotient_eq_C
        F a p w0 i
    have hnonzero :
        (∑ j : Fin 3, T2 i j * w0 j) ≠ 0 := by
      intro hz
      apply hi
      rw [hresponse, hz]
      simp
    exact Or.inl ⟨ell, M, r, t, hlin, hM, hrt, ⟨i, hnonzero⟩⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
