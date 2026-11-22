import HC4.Polynomial.RankThreeCubicDetOneSourcePoleRepair
import HC4.Polynomial.DerivativeBounds
import Mathlib.Tactic

/-!
# Exact lower-weight profile of the determinant-one cubic pole repair

The preceding theorem showed that determinant one forces the original
source Hessian to repair the full cubic characteristic's nonzero pole
residue. We now identify the correcting Hessian as the Hessian of
the ACTUAL strictly-lower transverse-weight remainder

  E = F - initialForm transverseCubicWeight 3 F.

The true cubic source cap gives weight(E) < 3. Thus each correcting
Hessian entry has strict bound 3-w_i-w_j. In particular:
  longitudinal / longitudinal: transverse weight < 3;
  longitudinal / transverse: transverse weight < 2;
  transverse / transverse: transverse weight < 1.

We retain the very same source F, longitudinal anchor a, genuine
denominator pole p, nonzero residue S, and quotient map. Crucially,
the nonzero correction is an exact matrix-vector statement for
Hess(E), not an independently chosen lower-order perturbation.

No extra closing hypothesis or exclusion of the exact-triple
pole branch is introduced. The missing work is to show that such
a strictly lower-weight repair cannot coexist with the complete
determinant-one and integrability constraints.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The genuine cubic pole residue is repaired by the Hessian of
the original source's STRICTLY lower transverse-weight remainder.
Its complete Hessian entrywise weight profile is source-derived,
and the repair is nonzero on the same actual residue in the
same prime quotient. -/
theorem sourceCubic_genuinePole_detOne_strictLowerWeightRepair
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
    let L := initialForm transverseCubicWeight 3 F
    let E := F - L
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L)
    ∃ (k : Fin 3) (S : Fin 3 → (B3 K ⧸ Ideal.span {p})),
      S k ≠ 0 ∧
      (∀ i j : Unit ⊕ Fin 3,
        IsWeightLT transverseCubicWeight
          (3 - transverseCubicWeight i - transverseCubicWeight j)
          (hessian E i j)) ∧
      A *ᵥ (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) = 0 ∧
      (φ.mapMatrix (hessian E)) *ᵥ
        (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) ≠ 0 := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let E : SB K := F - L
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  have hEweight : IsWeightLT transverseCubicWeight 3 E :=
    sub_initialForm_isWeightLT hcap
  have hprofile (i j : Unit ⊕ Fin 3) :
      IsWeightLT transverseCubicWeight
        (3 - transverseCubicWeight i - transverseCubicWeight j)
        (hessian E i j) :=
    hEweight.hessian_entry i j
  obtain ⟨k, S, hSk, hAw, hrepair⟩ :=
    sourceCubic_genuinePole_detOne_forces_lowerLayerRepair
      F a V hdetOne hV hgrad hregular u p hp hpd hpn
  have hHess (i j : Unit ⊕ Fin 3) :
      hessian E i j = hessian F i j - hessian L i j := by
    simp [E, hessian_apply]
  have hmatrix : φ.mapMatrix (hessian E) = B - A := by
    ext i j
    change φ (hessian E i j) =
      φ (hessian F i j) - φ (hessian L i j)
    rw [hHess i j, map_sub]
  refine ⟨k, S, hSk, hprofile, hAw, ?_⟩
  rw [hmatrix]
  exact hrepair

end
end HC4.Polynomial.RankThreeCubic
