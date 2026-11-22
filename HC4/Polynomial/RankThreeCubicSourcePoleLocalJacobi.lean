import HC4.Polynomial.RankThreeCubicSimplePoleNumerator
import HC4.Polynomial.RankThreeCubicSquarefreePoleFinal
import Mathlib.Tactic

/-!
# Local Jacobi obstruction at a genuine cubic characteristic pole

The squarefree determinant argument previously extracted a nonzero
Cramer residue only after imposing *global* squarefreeness. Here the
same source identities are used at a selected irreducible factor p
with a surviving actual Cramer numerator. The resulting Jacobi
derivative divisibility is componentwise, independent of factors
elsewhere in the determinant.

Combined with the reduced-denominator numerator lemma, this forces
every genuine irreducible characteristic pole to occur at least twice
in the transverse Hessian determinant.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A nonzero *actual Cramer numerator* on an irreducible
transverse determinant factor forces all three determinant
derivatives to vanish modulo that factor. No global squarefreeness
or independent residue-vector hypothesis is used. -/
theorem sourceCubic_survivingCramer_implies_JacobiDivisibility
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (p : B3 K) (hp : Irreducible p)
    (hpdet : p ∣ (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det)
    (j : Fin 3)
    (hAnz : ¬ p ∣
      ((sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).adjugate *ᵥ
        sourceNegativeMixedHessian a
          (initialForm transverseCubicWeight 3 F)) j) :
    ∀ i : Fin 3,
      p ∣ pderiv i (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun n => q ((H.adjugate *ᵥ r) n)
  have hSj : S j ≠ 0 := by
    intro hz
    exact hAnz
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hS : S ≠ 0 := by
    intro hz
    exact hSj (by simpa using congrFun hz j)
  have hSvec :
      (H.adjugate.map q) *ᵥ (fun n : Fin 3 => q (r n)) = S := by
    funext n
    change (∑ l : Fin 3, q (H.adjugate n l) * q (r l)) =
      q ((H.adjugate *ᵥ r) n)
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hSnonzero :
      (H.adjugate.map q) *ᵥ (fun n : Fin 3 => q (r n)) ≠ 0 := by
    rw [hSvec]
    exact hS
  have hcof : ∃ j k : Fin 3, ¬ p ∣ H.adjugate j k :=
    exists_cofactor_not_dvd_of_cramer_numerator_not_dvd
      H r p ⟨j, hAnz⟩
  obtain ⟨k, hkpivot⟩ :=
    exists_principal_cofactor_not_dvd H
      (sourceTransverseHessian_isSymm a L) p hp.prime hpdet hcof
  have hk : q (H.adjugate k k) ≠ 0 := by
    intro hz
    exact hkpivot
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hdetzero : q H.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr hpdet)
  have hquadratic (i : Fin 3) :
      (∑ n : Fin 3, ∑ l : Fin 3,
        q (pderiv i (H n l)) *
          ((H.adjugate.map q) *ᵥ
            (fun v : Fin 3 => q (r v))) n *
          ((H.adjugate.map q) *ᵥ
            (fun v : Fin 3 => q (r v))) l) = 0 := by
    obtain ⟨Q, hQ, hres⟩ :=
      exists_sourceCubic_cramerQuadraticResidue
        F a V hV hgrad q hdetzero i
    have hcoeff :=
      quadraticFamilyEval_zero_coefficients
        (fun n l : Fin 3 => (Q n l).map q)
        S hres 0
    have hQzero (n l : Fin 3) :
        (Q n l).coeff 0 = pderiv i (H n l) :=
      cubic_sourceThirdDerivative_timeZero a L V i n l
        (Q n l) (hQ n l)
    have hzero :
        (∑ n : Fin 3, ∑ l : Fin 3,
          q (pderiv i (H n l)) * S n * S l) = 0 := by
      simpa only [_root_.Polynomial.coeff_map, hQzero] using hcoeff
    simpa only [← hSvec] using hzero
  have hvanish :=
    cubic_rankOneCramer_Jacobi_zero H
      (sourceTransverseHessian_isSymm a L)
      q hdetzero r k hk hSnonzero hquadratic
  intro i
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (hvanish i))

/-- The derivative criterion is also *local*: if p occurs only once
in D, then some first derivative of D is nonzero modulo p. -/
theorem simple_irreducible_factor_has_nonzero_derivative
    (D p : B3 K)
    (hp : Irreducible p)
    (hpD : p ∣ D)
    (hsimple : ¬ p * p ∣ D) :
    ∃ i : Fin 3, ¬ p ∣ pderiv i D := by
  classical
  obtain ⟨i, hpi⟩ := exists_pderiv_not_dvd_of_irreducible p hp
  refine ⟨i, ?_⟩
  intro hd
  obtain ⟨h, hh⟩ := hpD
  have hnot : ¬ p ∣ h := by
    intro hph
    apply hsimple
    rw [hh]
    exact mul_dvd_mul (dvd_refl p) hph
  have hpder : p ∣ pderiv i (p * h) := by
    simpa only [hh] using hd
  rw [pderiv_mul] at hpder
  have hpsecond : p ∣ p * pderiv i h := by
    exact ⟨pderiv i h, rfl⟩
  have hpdiff := dvd_sub hpder hpsecond
  have hprod : p ∣ (pderiv i p) * h := by
    convert hpdiff using 1 <;> ring
  exact (hp.prime.not_dvd_mul hpi hnot) hprod

/-- Every *genuine reduced denominator pole* of the actual
characteristic must be a repeated factor of the same source
transverse Hessian determinant. Unlike the earlier two-way
classification, this witness is tied to the actual fraction's
denominator, not an unrelated repeated divisor. -/
theorem sourceCubic_genuinePole_is_repeatedFactor
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (j : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j))) :
    p * p ∣ (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  have hk :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ
        (fun n : Fin 3 => V (.inr n)) =
      fun n : Fin 3 => algebraMap (B3 K) (F3 K) (r n) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  have hpdet : p ∣ H.det :=
    dvd_trans hpd
      (reduced_denominator_dvd_hessianDet H r
        (fun n : Fin 3 => V (.inr n)) hk j)
  by_contra hsimple
  have hAnz : ¬ p ∣ (H.adjugate *ᵥ r) j :=
    cramerNumerator_not_dvd_of_simplePole
      H r (fun n : Fin 3 => V (.inr n)) hk j p hp hpd hpn hsimple
  have hall :=
    sourceCubic_survivingCramer_implies_JacobiDivisibility
      F a V hV hgrad p hp hpdet j hAnz
  obtain ⟨i, hder⟩ :=
    simple_irreducible_factor_has_nonzero_derivative
      H.det p hp hpdet hsimple
  exact hder (hall i)

end
end HC4.Polynomial.RankThreeCubic
