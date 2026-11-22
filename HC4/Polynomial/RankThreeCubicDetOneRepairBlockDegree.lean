import HC4.Polynomial.RankThreeCubicDetOneWeightedRepair
import Mathlib.Tactic

/-!
# Transverse Hessian repair is constant in the transverse variables

The determinant-one theorem has isolated a genuinely nonzero
lower-weight Hessian correction E=F-L₃ acting on the same
genuine-pole residue S. Because the original source has transverse
weight at most three, E has transverse weight strictly below three.

Three transverse derivatives of E therefore have strictly negative
transverse weight and are ZERO. In particular, every
transverse-transverse Hessian correction is independent of the
transverse variables, even before the longitudinal slice.

These source-derived equalities make the next determinant-weight
calculation finite and exact. They are NOT yet the weight-five
adjugate-trace identity or a contradiction to the pole.
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

/-- No monomial of an actual polynomial has negative transverse weight:
the longitudinal variable has weight zero and the other three
variables have weight one. -/
theorem transverseCubicWeight_nonnegative
    (d : (Unit ⊕ Fin 3) →₀ ℕ) :
    0 ≤ Finsupp.weight transverseCubicWeight d := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro i hi
  cases i with
  | inl v =>
      cases v
      simp [transverseCubicWeight]
  | inr j =>
      simp [transverseCubicWeight]

/-- Strictly negative transverse weight is impossible for a
nonzero polynomial. No finite-field evaluation argument is used. -/
theorem transverseCubicWeight_lt_zero_implies_zero
    (P : SB K)
    (hP : IsWeightLT transverseCubicWeight 0 P) :
    P = 0 := by
  classical
  ext d
  by_cases hz : MvPolynomial.coeff d P = 0
  · simp [hz]
  · have hd : d ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr hz
    have hlt : Finsupp.weight transverseCubicWeight d < 0 := hP hd
    have hge := transverseCubicWeight_nonnegative d
    omega

/-- After removing the cubic initial form, every third transverse
derivative of the actual source remainder vanishes identically.
This does not assume determinant one: it is an exact consequence
of the original transverse-degree cap. -/
theorem sourceCubic_lowerRemainder_threeTransverseDerivatives_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (i j k : Fin 3) :
    pderiv (.inr k)
      (hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j)) = 0 := by
  let E : SB K := F - initialForm transverseCubicWeight 3 F
  have hE : IsWeightLT transverseCubicWeight 3 E :=
    sub_initialForm_isWeightLT hcap
  have hder :
      IsWeightLT transverseCubicWeight 0
        (pderiv (.inr k) (hessian E (.inr i) (.inr j))) := by
    have h := (hE.hessian_entry (.inr i) (.inr j)).pderiv (.inr k)
    simpa [transverseCubicWeight] using h
  exact transverseCubicWeight_lt_zero_implies_zero
    (pderiv (.inr k) (hessian E (.inr i) (.inr j))) hder

/-- Every transverse derivative of the sliced correcting
transverse-transverse Hessian entry vanishes. Thus the correction
is constant as a transverse polynomial on every longitudinal slice. -/
theorem sourceCubic_lowerRemainder_slicedTransverseHessian_pderiv_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (i j k : Fin 3) :
    pderiv k (referenceSlice a
      (hessian (F - initialForm transverseCubicWeight 3 F)
        (.inr i) (.inr j))) = 0 := by
  rw [← referenceSlice_pderiv a k]
  rw [sourceCubic_lowerRemainder_threeTransverseDerivatives_zero F hcap i j k]
  simp

/-- The repair required by determinant one has a nonzero action on
the actual pole residue, AND its transverse-transverse block has
no dependence on transverse variables.

The same source F, anchor a, prime p and nonzero residue S are
retained from the source-honest theorem. -/
theorem sourceCubic_genuinePole_detOne_repairTransverseBlock_constant
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
      (∀ i j k : Fin 3,
        pderiv k (referenceSlice a (hessian E (.inr i) (.inr j))) = 0) ∧
      A *ᵥ (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) = 0 ∧
      (φ.mapMatrix (hessian E)) *ᵥ
        (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) ≠ 0 := by
  classical
  obtain ⟨k, S, hk, hdegree, hkernel, hrepair⟩ :=
    sourceCubic_genuinePole_detOne_strictLowerWeightRepair
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  refine ⟨k, S, hk, ?_, hkernel, hrepair⟩
  intro i j l
  exact sourceCubic_lowerRemainder_slicedTransverseHessian_pderiv_zero
    F hcap a i j l

end
end HC4.Polynomial.RankThreeCubic
