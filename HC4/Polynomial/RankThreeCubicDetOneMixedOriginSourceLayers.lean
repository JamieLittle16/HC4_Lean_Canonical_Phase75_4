import HC4.Polynomial.RankThreeCubicDetOneFixedTangentOriginRepairOrTriple
import HC4.Polynomial.RankThreeCubicSourceDegrees
import Mathlib.Tactic

/-!
# Source-honest mixed origin jet comes exclusively from the subquadratic layer

The actual weight-three and weight-two source components have mixed
longitudinal/transverse Hessian entries of weights two and one,
respectively. After specializing x=a, these are homogeneous
polynomials of positive transverse degree, and hence vanish at
the transverse origin.

Thus the full source's mixed Hessian at (a,0) equals that of
R=F-L3-L2. This is a literal source identity, before imposing
the determinant-one or pole hypotheses.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- Any positive-degree homogeneous transverse polynomial has
zero constant coefficient, hence vanishes at the origin. -/
theorem homogeneous_positive_origin_zero
    (P : B3 K) (n : ℕ)
    (hP : P.IsHomogeneous (n + 1)) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) P = 0 := by
  have hcoeff :
      MvPolynomial.coeff (0 : Fin 3 →₀ ℕ) P = 0 :=
    hP.coeff_eq_zero (by simp [Finsupp.degree])
  have hconst : MvPolynomial.constantCoeff P = 0 := hcoeff
  simp [MvPolynomial.aeval_zero', hconst]

/-- A weighted-homogeneous source layer of transverse weight
n+1 has a mixed source Hessian entry of transverse degree n;
for n>0 the mixed entry vanishes at the transverse origin. -/
theorem positiveSourceLayer_mixedOrigin_zero
    (P : SB K) (a : K) (n : ℕ)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight ((n + 1 : ℕ) : ℤ))
    (i : Fin 3) (hn : 0 < n) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (referenceSlice a (hessian P (.inl ()) (.inr i))) = 0 := by
  have hW :
      (hessian P (.inl ()) (.inr i)).IsWeightedHomogeneous
        transverseCubicWeight (n : ℤ) := by
    have h := pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hP (.inl ())) (.inr i)
    simpa [hessian_apply, transverseCubicWeight] using h
  have hh : (referenceSlice a
      (hessian P (.inl ()) (.inr i))).IsHomogeneous n :=
    referenceSlice_isHomogeneous_of_transverseWeight a _ n hW
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst n
  exact homogeneous_positive_origin_zero _ m (by simpa using hh)

/-- Each actual positive transverse source layer contributes
zero to the longitudinal/transverse Hessian at y=0. -/
theorem sourceCubic_topTwo_mixedOrigin_zero
    (F : SB K) (a : K) (i : Fin 3) :
    (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (referenceSlice a
        (hessian (initialForm transverseCubicWeight 3 F)
          (.inl ()) (.inr i))) = 0) ∧
    (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (referenceSlice a
        (hessian (initialForm transverseCubicWeight 2 F)
          (.inl ()) (.inr i))) = 0) := by
  constructor
  · exact positiveSourceLayer_mixedOrigin_zero
      (initialForm transverseCubicWeight 3 F) a 2
      (by simpa using
        (initialForm_isWeightedHomogeneous transverseCubicWeight 3 F))
      i (by decide)
  · exact positiveSourceLayer_mixedOrigin_zero
      (initialForm transverseCubicWeight 2 F) a 1
      (by simpa using
        (initialForm_isWeightedHomogeneous transverseCubicWeight 2 F))
      i (by decide)

/-- The mixed source Hessian origin jet is exactly the strictly
subquadratic layer's mixed origin jet. No pole or determinant
assumption is needed for this identity. -/
theorem sourceCubic_mixedOrigin_eq_subTwo_mixedOrigin
    (F : SB K) (a : K) (j : Fin 3) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (referenceSlice a (hessian F (.inl ()) (.inr j))) =
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (referenceSlice a (hessian Rlow (.inl ()) (.inr j))) := by
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  have hh :
      hessian F (.inl ()) (.inr j) =
        hessian L3 (.inl ()) (.inr j) +
        hessian L2 (.inl ()) (.inr j) +
        hessian Rlow (.inl ()) (.inr j) := by
    have hx := sourceCubic_hessian_three_two_lower_decomposition F
    exact congrFun (congrFun hx (.inl ())) (.inr j)
  obtain ⟨hL3, hL2⟩ := sourceCubic_topTwo_mixedOrigin_zero F a j
  rw [hh]
  simp only [map_add, hL3, hL2, zero_add]

/-- The same equality holds after pairing with any constant
transverse vector, without assuming that vector is a pole kernel. -/
theorem sourceCubic_mixedOrigin_directional_eq_subTwo
    (F : SB K) (a : K) (w0 : Fin 3 → K) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (∑ j : Fin 3,
        referenceSlice a (hessian F (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)) =
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)) := by
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceCubic_mixedOrigin_eq_subTwo_mixedOrigin F a j]

end
end HC4.Polynomial.RankThreeCubic
