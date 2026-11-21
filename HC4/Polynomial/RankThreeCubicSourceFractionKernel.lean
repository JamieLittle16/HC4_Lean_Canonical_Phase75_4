import HC4.Polynomial.RankThreeCubicAnchoredKernel
import HC4.Polynomial.RankThreeCubicPoleFreeLinear
import Mathlib.Tactic

/-!
# The actual cubic source supplies its fraction-field Hessian equation

The straight characteristic already constructed from the cubic initial
form has longitudinal velocity one. This module derives the transverse
Hessian linear system over the fraction field, with its coefficients
pulled back honestly from the original polynomial source.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev CubicB (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev CubicF (K : Type*) [Field K] := FractionRing (CubicB K)

/-- The transverse Hessian of the actual cubic source, restricted to a
ground-field longitudinal slice. -/
def sourceTransverseHessian (a : K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (CubicB K) :=
  fun i j => referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L))

/-- Minus the mixed longitudinal/transverse Hessian of the actual source
at the longitudinal slice. -/
def sourceNegativeMixedHessian (a : K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K) : Fin 3 → CubicB K :=
  fun i => - referenceSlice a (pderiv (.inl ()) (pderiv (.inr i) L))

/-- Evaluating the source at the polynomial fraction field's generic
transverse point is the same as specializing longitudinally to a and
then including the resulting polynomial in the fraction field. -/
theorem referenceSlice_fractionEvaluation
    (a : K) (p : MvPolynomial (Unit ⊕ Fin 3) K) :
    (algebraMap (CubicB K) (CubicF K)) (referenceSlice a p) =
      MvPolynomial.aeval (transverseGenericPoint a) p := by
  let f : CubicB K →ₐ[K] CubicF K :=
    IsScalarTower.toAlgHom K (CubicB K) (CubicF K)
  let z : Unit ⊕ Fin 3 → CubicB K :=
    Sum.elim (fun _ : Unit => MvPolynomial.C a) X
  have hz (i : Unit ⊕ Fin 3) : f (z i) = transverseGenericPoint a i := by
    cases i with
    | inl u =>
      cases u
      exact f.commutes a
    | inr j => rfl
  change f (MvPolynomial.aeval z p) =
    MvPolynomial.aeval (transverseGenericPoint a) p
  have hz' : (fun i : Unit ⊕ Fin 3 => f (z i)) =
      transverseGenericPoint a := by
    funext i
    exact hz i
  rw [MvPolynomial.comp_aeval_apply, hz']

/-- The Hessian equation for the actual source's anchored
characteristic, in fraction-field coordinates. There is no independent
kernel hypothesis: it is derived from the gradient-transport identity. -/
theorem sourceFractionHessianEquation_of_gradientTransport
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (V : Unit ⊕ Fin 3 → CubicF K)
    (hV : V (.inl ()) = 1)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C
        (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) :
    (sourceTransverseHessian a L).map
        (algebraMap (CubicB K) (CubicF K)) *ᵥ
          (fun j : Fin 3 => V (.inr j)) =
      fun i : Fin 3 =>
        (algebraMap (CubicB K) (CubicF K))
          (sourceNegativeMixedHessian a L i) := by
  classical
  let z := transverseGenericPoint a
  let f := algebraMap (CubicB K) (CubicF K)
  funext i
  have hk := anchored_gradient_implies_hessian_kernel L z V hgrad (.inr i)
  have hsplit :
      MvPolynomial.aeval z (pderiv (.inl ()) (pderiv (.inr i) L)) +
        ∑ j : Fin 3,
          MvPolynomial.aeval z (pderiv (.inr j) (pderiv (.inr i) L)) *
            V (.inr j) = 0 := by
    simpa [Fintype.sum_sum_type, hV] using hk
  have hrow :
      (∑ j : Fin 3,
        f (referenceSlice a
          (pderiv (.inr j) (pderiv (.inr i) L))) * V (.inr j)) =
        ∑ j : Fin 3,
          MvPolynomial.aeval z (pderiv (.inr j) (pderiv (.inr i) L)) *
            V (.inr j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [referenceSlice_fractionEvaluation]
  change (∑ j : Fin 3,
    f (referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L))) *
      V (.inr j)) =
    f (- referenceSlice a (pderiv (.inl ()) (pderiv (.inr i) L)))
  rw [hrow, map_neg, referenceSlice_fractionEvaluation]
  linear_combination hsplit

/-- Generic nonsingularity of the source transverse Hessian on a
longitudinal slice descends to the polynomial transverse Hessian after
that specialization. -/
theorem sourceTransverseHessian_det_ne_zero_of_generic
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      (((hessian L).submatrix Sum.inr Sum.inr).det) ≠ 0) :
    (sourceTransverseHessian a L).det ≠ 0 := by
  let f := algebraMap (CubicB K) (CubicF K)
  let e : MvPolynomial (Unit ⊕ Fin 3) K →ₐ[K] CubicF K :=
    MvPolynomial.aeval (transverseGenericPoint a)
  have hMat : f.mapMatrix (sourceTransverseHessian a L) =
      e.toRingHom.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr) := by
    ext i j
    change f (referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L))) =
      e (pderiv (.inr j) (pderiv (.inr i) L))
    exact referenceSlice_fractionEvaluation a _
  have hdet : f ((sourceTransverseHessian a L).det) =
      e (((hessian L).submatrix Sum.inr Sum.inr).det) := by
    have h := congrArg Matrix.det hMat
    simpa only [← RingHom.map_det] using h
  intro hz
  apply hreg
  rw [hz, map_zero] at hdet
  exact hdet.symm

/-- The genuine cubic grade of a source with constant Hessian
determinant and a generically nonsingular transverse Hessian admits
a normalized characteristic satisfying its *source-derived* fraction
field Hessian equation. -/
theorem exists_sourceCubic_fractionHessianEquation [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans :
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → CubicF K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (sourceTransverseHessian a L).map
          (algebraMap (CubicB K) (CubicF K)) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          (algebraMap (CubicB K) (CubicF K))
            (sourceNegativeMixedHessian a L i) := by
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  obtain ⟨V, hV, hgrad⟩ :=
    exists_transverseCubic_characteristic_at a F hcap hdet ha
  exact ⟨a, V,
    sourceTransverseHessian_det_ne_zero_of_generic a
      (initialForm transverseCubicWeight 3 F) ha,
    hV, sourceFractionHessianEquation_of_gradientTransport a
      (initialForm transverseCubicWeight 3 F) V hV hgrad⟩

end
end HC4.Polynomial.RankThreeCubic
