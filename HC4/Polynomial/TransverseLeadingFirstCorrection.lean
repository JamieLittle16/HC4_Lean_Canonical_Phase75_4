import HC4.Polynomial.TransverseLeadingFixedPower
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import Mathlib.Tactic

/-!
# First lower transverse grade: arbitrary-degree source constraint

For the original constant-Hessian source of transverse cap m >= 2,
the coefficient one weight below the maximum determinant weight
4m-6 is the adjugate pairing of the genuine adjacent source grades.
It vanishes because 4m-7 is positive.

At a regular leading-Hessian anchor the normalized characteristic
kernel consequently makes the first lower source Hessian isotropic.
No polynomial characteristic assumption is needed for this result.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

theorem sourceLeading_firstLower_det_eq_adjugate_pairing
    (F : S K) (m : ℤ)
    (hcap : IsWeightLE transverseCubicWeight m F) :
    initialForm transverseCubicWeight (4 * m - 7) (hessianDeterminant F) =
      ((hessian (initialForm transverseCubicWeight m F)).adjugate *
        hessian (initialForm transverseCubicWeight (m - 1) F)).trace := by
  classical
  let w := transverseCubicWeight
  have hc : (Fintype.card (Unit ⊕ Fin 3) : ℤ) = 4 := by decide
  have hs : (∑ i : Unit ⊕ Fin 3, w i) = 3 := by decide
  have hweights (π : Equiv.Perm (Unit ⊕ Fin 3)) :
      (∑ i : Unit ⊕ Fin 3, (m - w (π i) - w i : ℤ)) = 4 * m - 6 := by
    have h := hessianTermWeight_eq w m π
    rw [hc, hs] at h
    convert h using 1 <;> ring
  have hA (i j : Unit ⊕ Fin 3) :
      hessian (initialForm w m F) i j =
        initialForm w (m - w i - w j) (hessian F i j) :=
    hessian_initialForm_entry w m F i j
  have hB (i j : Unit ⊕ Fin 3) :
      hessian (initialForm w (m - 1) F) i j =
        initialForm w ((m - w i - w j) - 1) (hessian F i j) := by
    have h := hessian_initialForm_entry w (m - 1) F i j
    convert h using 1 <;> ring
  have hfirst := initialForm_det_first_lower_eq_adjugate_trace
    (σ := Unit ⊕ Fin 3) (ι := Unit ⊕ Fin 3)
    w (4 * m - 6) (fun i j : Unit ⊕ Fin 3 => m - w i - w j)
    (hessian F)
    (hessian (initialForm w m F))
    (hessian (initialForm w (m - 1) F))
    hweights (fun i j => hcap.hessian_entry i j) hA hB
  change initialForm w (4 * m - 7) (hessian F).det =
    ((hessian (initialForm w m F)).adjugate *
      hessian (initialForm w (m - 1) F)).trace
  simpa only [show 4 * m - 6 - 1 = 4 * m - 7 by ring] using hfirst

theorem sourceLeading_constantDet_firstCorrection_trace_zero
    (F : S K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    ((hessian (initialForm transverseCubicWeight m F)).adjugate *
      hessian (initialForm transverseCubicWeight (m - 1) F)).trace = 0 := by
  rw [← sourceLeading_firstLower_det_eq_adjugate_pairing F m hcap, hdet]
  exact initialForm_eq_zero_of_isWeightedHomogeneous
    (MvPolynomial.isWeightedHomogeneous_C transverseCubicWeight δ)
    (4 * m - 7) (by omega)

/-- The longitudinal principal cofactor is exactly the transverse
determinant, in the actual sum-indexed matrix (without a change of frame). -/
theorem longitudinal_principalCofactor_eq_transverseDet
    {R : Type*} [CommRing R]
    (A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R) :
    A.adjugate (.inl ()) (.inl ()) =
      (A.submatrix Sum.inr Sum.inr).det := by
  classical
  let B := A.updateRow (.inl ()) (Pi.single (.inl ()) (1 : R))
  have hB : B = Matrix.fromBlocks
      (1 : Matrix Unit Unit R) (0 : Matrix Unit (Fin 3) R)
      (A.submatrix Sum.inr Sum.inl) (A.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i with
    | inl u =>
      cases u
      cases j with
      | inl v => cases v; simp [B, Matrix.updateRow_apply, Matrix.one_apply]
      | inr v => simp [B, Matrix.updateRow_apply, Pi.single_apply]
    | inr i =>
      cases j <;> simp [B, Matrix.updateRow_apply]
  change B.det = _
  rw [hB, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-- The first adjacent source grade has zero directional Hessian
quadratic form at every regular leading-Hessian characteristic anchor. -/
theorem sourceLeading_firstCorrection_isotropic_at_anchor
    [CharZero K] {E : Type*} [Field E] [Algebra K E]
    (F : S K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hV : V (.inl ()) = 1)
    (hgrad : ∀ i, lineEval z V
        (pderiv i (initialForm transverseCubicWeight m F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight m F)))) :
    ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3,
      V i * MvPolynomial.aeval z
        (hessian (initialForm transverseCubicWeight (m - 1) F) i j) * V j = 0 := by
  classical
  let L := initialForm transverseCubicWeight m F
  let Q := initialForm transverseCubicWeight (m - 1) F
  let φ := (MvPolynomial.aeval z : S K →ₐ[K] E).toRingHom
  let A := φ.mapMatrix (hessian L)
  let C := φ.mapMatrix (hessian Q)
  have hsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change φ (pderiv i (pderiv j L)) = φ (pderiv j (pderiv i L))
    rw [HC4.Newton.pderiv_comm_backport i j L]
  have hker : A *ᵥ V = 0 := by
    funext i
    exact anchored_gradient_implies_hessian_kernel L z V hgrad i
  have htrans : (A.submatrix Sum.inr Sum.inr).det ≠ 0 := by
    change (φ.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)).det ≠ 0
    rw [← RingHom.map_det]
    exact hz
  have hkk : A.adjugate (.inl ()) (.inl ()) ≠ 0 := by
    rw [longitudinal_principalCofactor_eq_transverseDet]
    exact htrans
  have hline : ∀ u : Unit ⊕ Fin 3 → E, A *ᵥ u = 0 →
      ∃ c : E, ∀ i, u i = c * V i :=
    principalCofactor_kernelLine_of_unitCoordinate A V (.inl ()) hkk hker
      (by rw [hV]; exact isUnit_one)
  have htrace : (A.adjugate * C).trace = 0 := by
    change ((φ.mapMatrix (hessian L)).adjugate * φ.mapMatrix (hessian Q)).trace = 0
    rw [ringHom_map_adjugate_trace,
      sourceLeading_constantDet_firstCorrection_trace_zero F m hm hcap hdet, map_zero]
  exact symmetric_kernelLine_adjugateTrace_zero_implies_isotropic
    A C hsym V hker hline (.inl ()) hkk htrace

end
end HC4.Polynomial.RankThreeCubic
