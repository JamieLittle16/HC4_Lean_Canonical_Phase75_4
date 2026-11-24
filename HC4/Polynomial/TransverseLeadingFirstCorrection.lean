import HC4.Polynomial.TransverseLeadingFixedPower
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import HC4.Polynomial.RankThreeCubicPoleJacobiBridge
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.ParameterGapSecondJet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
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
  rw [Matrix.adjugate_apply]
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


/-- Differentiation in characteristic time is the directional derivative
of the original polynomial, evaluated by the same affine substitution. -/
theorem transverse_lineEval_derivative
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Field E] [Algebra K E]
    (z V : ι → E) (P : MvPolynomial ι K) :
    (lineEval z V P).derivative =
      ∑ i : ι, _root_.Polynomial.C (V i) * lineEval z V (pderiv i P) := by
  classical
  let e := lineEval (K := K) z V
  have hprod (p q : MvPolynomial ι K) :
      (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i (p * q))) =
        e p * (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i q)) +
        e q * (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i p)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    ring
  change (e P).derivative = _
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [show e (MvPolynomial.C a) =
        _root_.Polynomial.C (algebraMap K E a) by
      simp [e, lineEval, IsScalarTower.algebraMap_apply K E (_root_.Polynomial E),
        _root_.Polynomial.algebraMap_eq]]
    simp [e]
  | add p q hp hq =>
    simp only [map_add, _root_.Polynomial.derivative_add, hp, hq,
      mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hx : (e (X i)).derivative =
        ∑ j : ι, _root_.Polynomial.C (V j) * e (pderiv j (X i)) := by
      rw [show e (X i) = _root_.Polynomial.C (z i) +
          _root_.Polynomial.C (V i) * _root_.Polynomial.X by
        simp [e, lineEval]]
      rw [Finset.sum_eq_single i]
      · simp [pderiv_X]
      · intro j _ hji
        simp [pderiv_X, hji, Ne.symm hji]
      · simp
    change (e (p * X i)).derivative =
      ∑ j : ι, _root_.Polynomial.C (V j) * e (pderiv j (p * X i))
    rw [hprod, map_mul, _root_.Polynomial.derivative_mul, hp, hx]
    ring

/-- The first lower source Hessian is isotropic along the ENTIRE
characteristic, not just its anchor. Work in the time polynomial
domain: the principal cofactor has a nonzero constant coefficient,
so no specialization or assumption of a pole-free velocity is needed. -/
theorem sourceLeading_firstCorrection_isotropic_along_line
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
      _root_.Polynomial.C (V i) *
        lineEval z V (hessian (initialForm transverseCubicWeight (m - 1) F) i j) *
        _root_.Polynomial.C (V j) = 0 := by
  classical
  let L := initialForm transverseCubicWeight m F
  let Q := initialForm transverseCubicWeight (m - 1) F
  let φ := (lineEval (K := K) z V).toRingHom
  let A := φ.mapMatrix (hessian L)
  let B := φ.mapMatrix (hessian Q)
  let W : Unit ⊕ Fin 3 → _root_.Polynomial E :=
    fun i => _root_.Polynomial.C (V i)
  have hsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change φ (pderiv i (pderiv j L)) = φ (pderiv j (pderiv i L))
    rw [HC4.Newton.pderiv_comm_backport i j L]
  have hker : A *ᵥ W = 0 := by
    funext i
    have hd := transverse_lineEval_derivative z V (pderiv i L)
    rw [hgrad i, _root_.Polynomial.derivative_C] at hd
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    change (∑ j, φ (pderiv j (pderiv i L)) * W j) = 0
    calc
      _ = ∑ j, _root_.Polynomial.C (V j) * lineEval z V (pderiv j (pderiv i L)) := by
        apply Finset.sum_congr rfl
        intro j _
        change φ (pderiv j (pderiv i L)) * _root_.Polynomial.C (V j) =
          _root_.Polynomial.C (V j) * φ (pderiv j (pderiv i L))
        exact mul_comm _ _
      _ = 0 := hd.symm
  have htrans : (A.submatrix Sum.inr Sum.inr).det ≠ 0 := by
    change (φ.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)).det ≠ 0
    rw [← RingHom.map_det]
    intro h
    have hc := congrArg (fun p : _root_.Polynomial E => p.coeff 0) h
    change (lineEval z V ((hessian L).submatrix Sum.inr Sum.inr).det).coeff 0 =
      (0 : _root_.Polynomial E).coeff 0 at hc
    rw [cubic_lineEval_coeff_zero, _root_.Polynomial.coeff_zero] at hc
    exact hz hc
  have hkk : A.adjugate (.inl ()) (.inl ()) ≠ 0 := by
    rw [longitudinal_principalCofactor_eq_transverseDet]
    exact htrans
  have hline : ∀ u : Unit ⊕ Fin 3 → _root_.Polynomial E, A *ᵥ u = 0 →
      ∃ c : _root_.Polynomial E, ∀ i, u i = c * W i :=
    principalCofactor_kernelLine_of_unitCoordinate A W (.inl ()) hkk hker
      (by simp [W, hV])
  have htrace : (A.adjugate * B).trace = 0 := by
    change ((φ.mapMatrix (hessian L)).adjugate * φ.mapMatrix (hessian Q)).trace = 0
    rw [ringHom_map_adjugate_trace,
      sourceLeading_constantDet_firstCorrection_trace_zero F m hm hcap hdet, map_zero]
  exact symmetric_kernelLine_adjugateTrace_zero_implies_isotropic
    A B hsym W hker hline (.inl ()) hkk htrace

/-- In characteristic zero the actual adjacent source grade is affine
in characteristic time, even for a genuinely rational characteristic.
This is a transport constraint, not a nonlinear coordinate change
of the full determinant-one source. -/
theorem sourceLeading_firstCorrection_affine_along_line
    [CharZero K] {E : Type*} [Field E] [CharZero E] [Algebra K E]
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
    let P := lineEval z V (initialForm transverseCubicWeight (m - 1) F)
    P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X := by
  classical
  let Q := initialForm transverseCubicWeight (m - 1) F
  let P := lineEval z V Q
  have hsecond : P.derivative.derivative = 0 := by
    change (lineEval z V Q).derivative.derivative = 0
    rw [transverse_lineEval_derivative]
    simp only [_root_.Polynomial.derivative_sum, _root_.Polynomial.derivative_mul,
      _root_.Polynomial.derivative_C, zero_mul, zero_add]
    simp_rw [transverse_lineEval_derivative, Finset.mul_sum]
    have hi := sourceLeading_firstCorrection_isotropic_along_line
      F m hm hcap hdet z V hz hV hgrad
    calc
      _ = ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3,
          _root_.Polynomial.C (V i) * lineEval z V (hessian Q i j) *
            _root_.Polynomial.C (V j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change _root_.Polynomial.C (V i) *
          (_root_.Polynomial.C (V j) * lineEval z V (pderiv j (pderiv i Q))) =
          _root_.Polynomial.C (V i) * lineEval z V (pderiv j (pderiv i Q)) *
            _root_.Polynomial.C (V j)
        ring
      _ = 0 := hi
  have hzero (n : ℕ) : P.coeff (n + 2) = 0 := by
    have h := congrArg (fun p : _root_.Polynomial E => p.coeff n) hsecond
    simp only [_root_.Polynomial.coeff_derivative, _root_.Polynomial.coeff_zero] at h
    have h1 : ((n + 1 : ℕ) : E) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : ((n + 1 + 1 : ℕ) : E) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hh : (P.coeff (n + 2) * ((n + 1 + 1 : ℕ) : E)) *
        ((n + 1 : ℕ) : E) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right h1)).resolve_right h2
  change P = _root_.Polynomial.C (P.coeff 0) +
    _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X
  ext n
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      simp [_root_.Polynomial.coeff_C, _root_.Polynomial.coeff_C_mul_X, hzero n]


end
end HC4.Polynomial.RankThreeCubic

/-!
# Arbitrary-order cleared transverse Schur recurrence

All calculations below are on a single actual reverse-Rees Hessian.
The frame change is a congruence of matrices at the reference point,
not a nonlinear change of source potential.  The recurrence is
denominator-free and retains all lower-layer mixed corrections.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton HC4.Valuation
open scoped BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- Determinant of the three transverse directions, with the first
direction reserved for the longitudinal characteristic. -/
def transverseSchurDet (H : GeneralFourBlock R) : R :=
  H.d * (H.x * H.z - H.y * H.y) -
    H.r * (H.r * H.z - H.s * H.y) +
    H.s * (H.r * H.y - H.s * H.x)

/-- The exact adjugate quadratic correction of the mixed row.  Write
cross terms as two copies so the coefficient formula is ring-generic. -/
def transverseSchurMixed (H : GeneralFourBlock R) : R :=
  H.b * H.b * (H.x * H.z - H.y * H.y) -
  H.b * H.p * ((H.r * H.z - H.s * H.y) + (H.r * H.z - H.s * H.y)) +
  H.b * H.q * ((H.r * H.y - H.s * H.x) + (H.r * H.y - H.s * H.x)) +
  H.p * H.p * (H.d * H.z - H.s * H.s) -
  H.p * H.q * ((H.d * H.y - H.r * H.s) + (H.d * H.y - H.r * H.s)) +
  H.q * H.q * (H.d * H.x - H.r * H.r)

theorem transverseSchur_det_identity (H : GeneralFourBlock R) :
    H.determinantCore = H.a * transverseSchurDet H - transverseSchurMixed H := by
  unfold GeneralFourBlock.determinantCore transverseSchurDet transverseSchurMixed
  ring

/-- Replace the longitudinal basis vector by (1,u,v,w), fixing all three
transverse basis vectors.  This is a determinant-one congruence. -/
def transverseCharacteristicFrame (H : GeneralFourBlock R) (u v w : R) :
    GeneralFourBlock R where
  a := H.a + 2 * u * H.b + 2 * v * H.p + 2 * w * H.q +
    u ^ 2 * H.d + v ^ 2 * H.x + w ^ 2 * H.z +
    2 * u * v * H.r + 2 * u * w * H.s + 2 * v * w * H.y
  b := H.b + u * H.d + v * H.r + w * H.s
  p := H.p + u * H.r + v * H.x + w * H.y
  q := H.q + u * H.s + v * H.y + w * H.z
  d := H.d
  r := H.r
  s := H.s
  x := H.x
  y := H.y
  z := H.z

theorem transverseCharacteristicFrame_det (H : GeneralFourBlock R) (u v w : R) :
    (transverseCharacteristicFrame H u v w).determinantCore = H.determinantCore := by
  unfold transverseCharacteristicFrame GeneralFourBlock.determinantCore
  ring

/-- Every coefficient of the longitudinal Hessian is constrained by
the same convolution equation. Isolate (n,0), retaining all earlier
longitudinal coefficients and the full adjugate correction. -/
theorem transverseSchur_coeff_recurrence
    (H : GeneralFourBlock (_root_.Polynomial R)) (n : ℕ) :
    H.a.coeff n * (transverseSchurDet H).coeff 0 =
      H.determinantCore.coeff n + (transverseSchurMixed H).coeff n -
        ∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
          H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2 := by
  classical
  have h := congrArg (fun p : _root_.Polynomial R => p.coeff n)
    (transverseSchur_det_identity H)
  change H.determinantCore.coeff n =
    (H.a * transverseSchurDet H - transverseSchurMixed H).coeff n at h
  rw [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_mul] at h
  let f : ℕ × ℕ → R := fun ij =>
    H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2
  have hm : (n, 0) ∈ Finset.antidiagonal n := by
    simp [Finset.mem_antidiagonal]
  have hs := Finset.add_sum_erase (Finset.antidiagonal n) f hm
  change H.determinantCore.coeff n =
    (∑ ij ∈ Finset.antidiagonal n, f ij) -
      (transverseSchurMixed H).coeff n at h
  rw [← hs] at h
  change H.a.coeff n * (transverseSchurDet H).coeff 0 =
    H.determinantCore.coeff n + (transverseSchurMixed H).coeff n -
      ∑ ij ∈ (Finset.antidiagonal n).erase (n, 0), f ij
  change H.determinantCore.coeff n =
    H.a.coeff n * (transverseSchurDet H).coeff 0 +
      (∑ ij ∈ (Finset.antidiagonal n).erase (n, 0), f ij) -
      (transverseSchurMixed H).coeff n at h
  linear_combination -h

/-- At order one there is no positive-order gap hypothesis at all. -/
private theorem transverse_coeff_mul_one (p q : _root_.Polynomial R) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  have hgap (f : _root_.Polynomial R) :
      HasNoPositiveParameterCoeffBelow 1 f := by
    intro n hn hlt
    omega
  simpa using coeff_mul_at_gap_endpoint_commRing (R := R)
    (j := 1) (by decide) (hgap p) (hgap q)

/-- Order two is exactly the three-term product convolution. -/
private theorem transverse_coeff_mul_two (p q : _root_.Polynomial R) :
    (p * q).coeff 2 =
      p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  have hgap (f : _root_.Polynomial R) :
      HasNoPositiveParameterCoeffBelow 1 f := by
    intro n hn hlt
    omega
  simpa using coeff_mul_at_twice_gap_endpoint_commRing (R := R)
    (j := 1) (by decide) (hgap p) (hgap q)

private theorem transverse_coeff_triple_two
    (p q r : _root_.Polynomial R) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    (p * q * r).coeff 2 = p.coeff 1 * q.coeff 1 * r.coeff 0 := by
  rw [transverse_coeff_mul_two, transverse_coeff_mul_two, transverse_coeff_mul_one,
    _root_.Polynomial.mul_coeff_zero, hp, hq]
  ring

/-- At order two, the adjugate term uses only the first mixed
coefficients and the constant transverse block. -/
theorem transverseSchurMixed_coeff_two
    (H : GeneralFourBlock (_root_.Polynomial R))
    (hb : H.b.coeff 0 = 0) (hp : H.p.coeff 0 = 0) (hq : H.q.coeff 0 = 0) :
    (transverseSchurMixed H).coeff 2 =
      transverseSchurMixed
        ({ a := H.a.coeff 2, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock R) := by
  simp only [transverseSchurMixed, _root_.Polynomial.coeff_add,
    _root_.Polynomial.coeff_sub,
    transverse_coeff_triple_two _ _ _ hb hb,
    transverse_coeff_triple_two _ _ _ hb hp,
    transverse_coeff_triple_two _ _ _ hb hq,
    transverse_coeff_triple_two _ _ _ hp hp,
    transverse_coeff_triple_two _ _ _ hp hq,
    transverse_coeff_triple_two _ _ _ hq hq,
    _root_.Polynomial.mul_coeff_zero]

/-- The second Schur constraint at a leading-kernel frame with vanishing
first longitudinal correction.  It is a genuine mixed correction,
not a claim that the next layer is again isotropic. -/
theorem transverseSchur_second_constraint
    (H : GeneralFourBlock (_root_.Polynomial R))
    (ha0 : H.a.coeff 0 = 0) (ha1 : H.a.coeff 1 = 0)
    (hb : H.b.coeff 0 = 0) (hp : H.p.coeff 0 = 0) (hq : H.q.coeff 0 = 0)
    (hdet : H.determinantCore.coeff 2 = 0) :
    H.a.coeff 2 * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := H.a.coeff 2, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock R) := by
  have h := congrArg (fun p : _root_.Polynomial R => p.coeff 2)
    (transverseSchur_det_identity H)
  change H.determinantCore.coeff 2 =
    (H.a * transverseSchurDet H - transverseSchurMixed H).coeff 2 at h
  rw [_root_.Polynomial.coeff_sub, transverse_coeff_mul_two,
    ha0, ha1, transverseSchurMixed_coeff_two H hb hp hq, hdet] at h
  simp only [zero_mul, zero_add] at h
  exact sub_eq_zero.mp h.symm

/-! The actual Fin 4 source adapter uses the existing marked-axis
reverse-Rees source directly, preserving its exact Hessian clock and
every original parameter layer. -/

variable {K : Type*} [Field K] [CharZero K]

/-- The exact Rees Hessian determinant and all source layer coefficients,
before any change of frame, for an arbitrary transverse cap. -/
theorem sourceTransverseRees_clock_and_layers
    (F : MvPolynomial (Fin 4) K) (m : ℕ) (hm : 2 ≤ m)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight m F)
    (hdet : hessianDeterminant F = 1) :
    let P := reverseWeightedReesFamily topKernelMarkedAxisNatWeight m F hbound
    (parameterFirstHessian P).det =
      (_root_.Polynomial.X : _root_.Polynomial (MvPolynomial (Fin 4) K)) ^ (4*m-6) ∧
    ∀ n : ℕ, n ≤ m → ∀ i j : Fin 4,
      (parameterFirstHessian P i j).coeff n =
        hessian (initialForm (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          ((m - n : ℕ) : ℤ) F) i j := by
  let P := reverseWeightedReesFamily topKernelMarkedAxisNatWeight m F hbound
  have hnonneg : 2 * ∑ i : Fin 4, topKernelMarkedAxisNatWeight i ≤ 4 * m := by
    simp [Fin.sum_univ_four, topKernelMarkedAxisNatWeight]
    omega
  have hclock : HasPolynomialFamilyHessianDefect (K := K) P (4*m-6) := by
    have h := reverseWeightedReesFamily_hasHessianDefect
      topKernelMarkedAxisNatWeight m F hbound hdet hnonneg
    simpa [P, Fin.sum_univ_four, topKernelMarkedAxisNatWeight] using h
  refine ⟨parameterFirstHessian_det_eq_X_pow P hclock, ?_⟩
  intro n hn i j
  rw [parameterFirstHessian_coeff]
  rw [reverseWeightedReesFamily_parameterLayer_eq_initialForm
    topKernelMarkedAxisNatWeight m n F hbound hn]

/-- Evaluate the actual source Hessian series and apply a constant
normalized characteristic frame.  The velocity may be in any extension
field (including a fraction field); no nonlinear source substitution. -/
def sourceTransverseSchurFrame
    {E : Type*} [Field E]
    (F : MvPolynomial (Fin 4) K) (m : ℕ)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight m F)
    (φ : MvPolynomial (Fin 4) K →+* E) (u v w : E) :
    GeneralFourBlock (_root_.Polynomial E) :=
  transverseCharacteristicFrame
    ((familyHessianFourBlock
      (reverseWeightedReesFamily topKernelMarkedAxisNatWeight m F hbound)).map
        (_root_.Polynomial.mapRingHom φ))
    (_root_.Polynomial.C u) (_root_.Polynomial.C v) (_root_.Polynomial.C w)

/-- The normalized frame retains the entire source determinant clock. -/
theorem sourceTransverseSchurFrame_det
    {E : Type*} [Field E]
    (F : MvPolynomial (Fin 4) K) (m : ℕ) (hm : 2 ≤ m)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight m F)
    (hdet : hessianDeterminant F = 1)
    (φ : MvPolynomial (Fin 4) K →+* E) (u v w : E) :
    (sourceTransverseSchurFrame F m hbound φ u v w).determinantCore =
      (_root_.Polynomial.X : _root_.Polynomial E) ^ (4*m-6) := by
  let P := reverseWeightedReesFamily topKernelMarkedAxisNatWeight m F hbound
  have h := (sourceTransverseRees_clock_and_layers F m hm hbound hdet).1
  have hc : (familyHessianFourBlock P).determinantCore =
      (_root_.Polynomial.X : _root_.Polynomial (MvPolynomial (Fin 4) K)) ^ (4*m-6) := by
    rw [← GeneralFourBlock.matrix_det, familyHessianFourBlock_matrix]
    exact h
  unfold sourceTransverseSchurFrame
  rw [transverseCharacteristicFrame_det, GeneralFourBlock.determinantCore_map]
  change _root_.Polynomial.map φ (familyHessianFourBlock P).determinantCore = _
  rw [hc]
  change (_root_.Polynomial.mapRingHom φ)
    ((_root_.Polynomial.X : _root_.Polynomial (MvPolynomial (Fin 4) K)) ^ (4*m-6)) = _
  rw [map_pow]
  change (_root_.Polynomial.map φ _root_.Polynomial.X) ^ (4*m-6) = _
  rw [_root_.Polynomial.map_X]

/-- Every preclock coefficient satisfies one and the same exact
source Schur recurrence.  This is not yet a degree reduction. -/
theorem sourceTransverseSchurFrame_preclock_recurrence
    {E : Type*} [Field E]
    (F : MvPolynomial (Fin 4) K) (m : ℕ) (hm : 2 ≤ m)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight m F)
    (hdet : hessianDeterminant F = 1)
    (φ : MvPolynomial (Fin 4) K →+* E) (u v w : E)
    (n : ℕ) (hn : n < 4*m-6) :
    let H := sourceTransverseSchurFrame F m hbound φ u v w
    H.a.coeff n * (transverseSchurDet H).coeff 0 =
      (transverseSchurMixed H).coeff n -
        ∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
          H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2 := by
  let H := sourceTransverseSchurFrame F m hbound φ u v w
  have hd : H.determinantCore.coeff n = 0 := by
    change (sourceTransverseSchurFrame F m hbound φ u v w).determinantCore.coeff n = 0
    rw [sourceTransverseSchurFrame_det F m hm hbound hdet φ u v w]
    have hne : 4*m-6 ≠ n := Ne.symm (Nat.ne_of_lt hn)
    simp [_root_.Polynomial.coeff_X_pow, hne, Ne.symm hne]
  have h := transverseSchur_coeff_recurrence H n
  rw [hd, zero_add] at h
  exact h



/-! ## All-order reverse Hessian coefficients

A time polynomial is reverse graded if its coefficient at k has
source weight b-k. Evaluation at time one then recovers each
coefficient by exact source-weight extraction. The grading is
multiplicative, hence it survives the full Leibniz determinant.
This avoids an order-by-order expansion or a new endpoint premise.
-/

section ReverseGrading

variable {σ : Type*}

/-- The coefficient at time k has source weight b-k. -/
def reverseTimeGraded (w : σ → ℤ) (b : ℤ)
    (p : _root_.Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ k : ℕ, (p.coeff k).IsWeightedHomogeneous w (b - (k : ℤ))

theorem reverseTimeGraded_one (w : σ → ℤ) :
    reverseTimeGraded w 0 (1 : _root_.Polynomial (MvPolynomial σ K)) := by
  intro k
  cases k with
  | zero =>
    simpa using (MvPolynomial.isWeightedHomogeneous_one K w)
  | succ k =>
    rw [_root_.Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact MvPolynomial.isWeightedHomogeneous_zero K w _

theorem reverseTimeGraded_mul
    {w : σ → ℤ} {b c : ℤ}
    {p q : _root_.Polynomial (MvPolynomial σ K)}
    (hp : reverseTimeGraded w b p) (hq : reverseTimeGraded w c q) :
    reverseTimeGraded w (b + c) (p * q) := by
  classical
  intro k
  rw [_root_.Polynomial.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  have hh := (hp ij.1).mul (hq ij.2)
  have hw : (b - (ij.1 : ℤ)) + (c - (ij.2 : ℤ)) = b + c - (k : ℤ) := by
    omega
  rw [hw] at hh
  exact hh

theorem reverseTimeGraded_prod
    {ι : Type*} (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (p : ι → _root_.Polynomial (MvPolynomial σ K))
    (hp : ∀ i ∈ s, reverseTimeGraded w (b i) (p i)) :
    reverseTimeGraded w (∑ i ∈ s, b i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Finset.prod_empty] using
      (reverseTimeGraded_one (K := K) w)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact reverseTimeGraded_mul (hp a (Finset.mem_insert_self a s))
      (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

/-- Every time coefficient is recovered from evaluation at one by
taking the appropriate exact source-weight component. -/
theorem reverseTimeGraded_extract
    {w : σ → ℤ} {b : ℤ}
    {p : _root_.Polynomial (MvPolynomial σ K)}
    (hp : reverseTimeGraded w b p) (k : ℕ) :
    initialForm w (b - (k : ℤ)) (p.eval 1) = p.coeff k := by
  classical
  rw [_root_.Polynomial.eval_eq_sum, _root_.Polynomial.sum_def]
  simp only [one_pow, mul_one, map_sum]
  rw [Finset.sum_eq_single k]
  · exact initialForm_eq_self_of_isWeightedHomogeneous (hp k)
  · intro j _ hj
    exact initialForm_eq_zero_of_isWeightedHomogeneous (hp j) _ (by omega)
  · intro hk
    have hzero : p.coeff k = 0 :=
      _root_.Polynomial.notMem_support_iff.mp hk
    rw [hzero, initialForm_zero]

/-- Reverse grading survives the entire determinant, including at a
singular leading coefficient. The entry grades need only have a common
sum on permutation terms. -/
theorem reverseTimeGraded_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : σ → ℤ) (b : ι → ι → ℤ) (d : ℤ)
    (M : Matrix ι ι (_root_.Polynomial (MvPolynomial σ K)))
    (hM : ∀ i j, reverseTimeGraded w (b i j) (M i j))
    (hweights : ∀ π : Equiv.Perm ι, (∑ j : ι, b (π j) j) = d) :
    reverseTimeGraded w d M.det := by
  classical
  intro k
  rw [Matrix.det_apply', _root_.Polynomial.finset_sum_coeff]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro π _
  let c : K := ↑↑(Equiv.Perm.sign π)
  change ((_root_.Polynomial.C (MvPolynomial.C c) *
    ∏ j : ι, M (π j) j).coeff k).IsWeightedHomogeneous w (d - (k : ℤ))
  rw [_root_.Polynomial.coeff_C_mul]
  have hprod := reverseTimeGraded_prod (Finset.univ : Finset ι)
    w (fun j => b (π j) j) (fun j => M (π j) j)
    (fun j _ => hM (π j) j)
  rw [hweights π] at hprod
  simpa only [zero_add] using
    (MvPolynomial.isWeightedHomogeneous_C w c).mul (hprod k)

end ReverseGrading

/-- An actual bounded source is exactly the sum of its transverse
grades, ordered from the nominal cap down to zero. -/
theorem sourceLeading_reverseLayerSum_eq
    (F : S K) (m : ℕ) (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F) :
    (∑ k ∈ Finset.range (m + 1),
      initialForm transverseCubicWeight ((m : ℤ) - (k : ℤ)) F) = F := by
  classical
  ext d
  simp only [MvPolynomial.coeff_sum, coeff_initialForm]
  by_cases hc : MvPolynomial.coeff d F = 0
  · simp [hc]
  · have hle := hcap (MvPolynomial.mem_support_iff.mpr hc)
    have hnonneg : 0 ≤ Finsupp.weight transverseCubicWeight d := by
      rw [transverseCubicWeight_eq_transverseSum]
      positivity
    let k : ℕ := ((m : ℤ) - Finsupp.weight transverseCubicWeight d).toNat
    have hk : (k : ℤ) = (m : ℤ) - Finsupp.weight transverseCubicWeight d :=
      Int.toNat_of_nonneg (by omega)
    have hkr : k < m + 1 := by omega
    rw [Finset.sum_eq_single k]
    · rw [if_pos (by omega)]
    · intro j _ hj
      rw [if_neg (by omega)]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hkr)).elim

/-- Hessian of the actual reverse layer family, with a new univariate
time variable which is NOT differentiated by the source Hessian. -/
def sourceLeading_reverseHessian
    (F : S K) (m : ℕ) :
    Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) (_root_.Polynomial (S K)) :=
  fun i j => ∑ k ∈ Finset.range (m + 1),
    _root_.Polynomial.monomial k
      (hessian (initialForm transverseCubicWeight ((m : ℤ) - (k : ℤ)) F) i j)

theorem sourceLeading_reverseHessian_coeff
    (F : S K) (m r : ℕ) (i j : Unit ⊕ Fin 3) :
    (sourceLeading_reverseHessian F m i j).coeff r =
      if r ≤ m then
        hessian (initialForm transverseCubicWeight ((m : ℤ) - (r : ℤ)) F) i j
      else 0 := by
  classical
  unfold sourceLeading_reverseHessian
  rw [_root_.Polynomial.finset_sum_coeff]
  simp only [_root_.Polynomial.coeff_monomial]
  by_cases hr : r ≤ m
  · rw [if_pos hr, Finset.sum_eq_single r]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro k hk
    have hkm := Finset.mem_range.mp hk
    rw [if_neg (by omega)]

/-- At time one the exact reverse Hessian is the original source
Hessian, not a repaired or truncated surrogate. -/
theorem sourceLeading_reverseHessian_eval_one
    (F : S K) (m : ℕ) (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F) :
    (_root_.Polynomial.evalRingHom (1 : S K)).mapMatrix
      (sourceLeading_reverseHessian F m) = hessian F := by
  classical
  apply Matrix.ext
  intro i j
  change (_root_.Polynomial.evalRingHom (1 : S K))
      (∑ k ∈ Finset.range (m + 1), _root_.Polynomial.monomial k
        (hessian (initialForm transverseCubicWeight ((m : ℤ) - (k : ℤ)) F) i j)) =
    hessian F i j
  rw [map_sum]
  simp only [_root_.Polynomial.coe_evalRingHom, _root_.Polynomial.eval_monomial,
    one_pow, mul_one]
  calc
    _ = hessian (∑ k ∈ Finset.range (m + 1),
        initialForm transverseCubicWeight ((m : ℤ) - (k : ℤ)) F) i j := by
      simp only [hessian_apply, map_sum]
    _ = _ := by rw [sourceLeading_reverseLayerSum_eq F m hcap]

/-- All coefficients of the actual reverse Hessian determinant are
the corresponding exact weighted components of the original source
determinant. Valid at every transverse cap, without rank assumptions. -/
theorem sourceLeading_reverseHessian_det_coeff
    (F : S K) (m : ℕ) (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    (r : ℕ) :
    (sourceLeading_reverseHessian F m).det.coeff r =
      initialForm transverseCubicWeight (4 * (m : ℤ) - 6 - (r : ℤ))
        (hessianDeterminant F) := by
  classical
  let w := transverseCubicWeight
  let M := sourceLeading_reverseHessian F m
  let b := fun i j : Unit ⊕ Fin 3 => (m : ℤ) - w i - w j
  have hM (i j : Unit ⊕ Fin 3) : reverseTimeGraded w (b i j) (M i j) := by
    intro k
    change ((sourceLeading_reverseHessian F m i j).coeff k).IsWeightedHomogeneous
      w (b i j - (k : ℤ))
    rw [sourceLeading_reverseHessian_coeff]
    split_ifs with hk
    · have hh := hessian_entry_isWeightedHomogeneous
        (initialForm_isWeightedHomogeneous w ((m : ℤ) - (k : ℤ)) F) i j
      have he : (m : ℤ) - (k : ℤ) - w i - w j = b i j - (k : ℤ) := by
        dsimp [b]
        ring
      rw [he] at hh
      exact hh
    · exact MvPolynomial.isWeightedHomogeneous_zero K w _
  have hweights (π : Equiv.Perm (Unit ⊕ Fin 3)) :
      (∑ j : Unit ⊕ Fin 3, b (π j) j) = 4 * (m : ℤ) - 6 := by
    have hh := hessianTermWeight_eq w (m : ℤ) π
    have hc : (Fintype.card (Unit ⊕ Fin 3) : ℤ) = 4 := by decide
    have hs : (∑ i : Unit ⊕ Fin 3, w i) = 3 := by decide
    rw [hc, hs] at hh
    simpa only [b, hessianTermWeight, show (2 : ℤ) * 3 = 6 by norm_num] using hh
  have hgraded := reverseTimeGraded_det w b (4 * (m : ℤ) - 6) M hM hweights
  have heval : M.det.eval 1 = hessianDeterminant F := by
    change (_root_.Polynomial.evalRingHom (1 : S K)) M.det = (hessian F).det
    rw [RingHom.map_det]
    change ((_root_.Polynomial.evalRingHom (1 : S K)).mapMatrix
      (sourceLeading_reverseHessian F m)).det = (hessian F).det
    rw [sourceLeading_reverseHessian_eval_one F m hcap]
  have he := reverseTimeGraded_extract hgraded r
  rw [heval] at he
  exact he.symm

/-- The full reverse Hessian determinant is a single time monomial
when the ORIGINAL source has constant Hessian determinant. This is
an arbitrary-order source identity; it imposes no regular-leading-rank
or polynomial-characteristic hypothesis. -/
theorem sourceLeading_reverseHessian_constantDet
    (F : S K) (m : ℕ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    (sourceLeading_reverseHessian F m).det =
      _root_.Polynomial.monomial (4 * m - 6) (MvPolynomial.C δ) := by
  classical
  apply _root_.Polynomial.ext
  intro r
  rw [sourceLeading_reverseHessian_det_coeff F m hcap r, hdet,
    _root_.Polynomial.coeff_monomial]
  have hclock : ((4 * m - 6 : ℕ) : ℤ) = 4 * (m : ℤ) - 6 := by
    rw [Nat.cast_sub (by omega : 6 ≤ 4 * m)]
    push_cast <;> ring
  by_cases hr : 4 * m - 6 = r
  · rw [if_pos hr]
    have hw : 4 * (m : ℤ) - 6 - (r : ℤ) = 0 := by
      rw [← hclock, hr, sub_self]
    rw [hw]
    exact initialForm_eq_self_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C transverseCubicWeight δ)
  · rw [if_neg hr]
    have hw : 4 * (m : ℤ) - 6 - (r : ℤ) ≠ 0 := by
      intro he
      apply hr
      have he' : ((4 * m - 6 : ℕ) : ℤ) = (r : ℤ) := by
        rw [hclock]
        exact sub_eq_zero.mp he
      exact_mod_cast he'
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C transverseCubicWeight δ) _ hw



section LeadingKernel

variable [IsDomain R]

private theorem transverse_coeff_triple_one
    (p q r : _root_.Polynomial R) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    (p * q * r).coeff 1 = 0 := by
  rw [transverse_coeff_mul_one, transverse_coeff_mul_one,
    _root_.Polynomial.mul_coeff_zero, hp, hq]
  simp

/-- In a genuine leading kernel frame the first longitudinal correction
is forced to vanish by the determinant clock, rather than assumed. -/
theorem transverseSchur_longitudinal_zero_one
    (H : GeneralFourBlock (_root_.Polynomial R))
    (hb : H.b.coeff 0 = 0) (hp : H.p.coeff 0 = 0) (hq : H.q.coeff 0 = 0)
    (hregular : (transverseSchurDet H).coeff 0 ≠ 0)
    (hdet0 : H.determinantCore.coeff 0 = 0)
    (hdet1 : H.determinantCore.coeff 1 = 0) :
    H.a.coeff 0 = 0 ∧ H.a.coeff 1 = 0 := by
  have hm0 : (transverseSchurMixed H).coeff 0 = 0 := by
    simp [transverseSchurMixed, _root_.Polynomial.mul_coeff_zero, hb, hp, hq]
  have hm1 : (transverseSchurMixed H).coeff 1 = 0 := by
    simp only [transverseSchurMixed, _root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_sub,
      transverse_coeff_triple_one _ _ _ hb hb,
      transverse_coeff_triple_one _ _ _ hb hp,
      transverse_coeff_triple_one _ _ _ hb hq,
      transverse_coeff_triple_one _ _ _ hp hp,
      transverse_coeff_triple_one _ _ _ hp hq,
      transverse_coeff_triple_one _ _ _ hq hq,
      sub_self, zero_add]
  have h0 := congrArg (fun p : _root_.Polynomial R => p.coeff 0)
    (transverseSchur_det_identity H)
  change H.determinantCore.coeff 0 =
    (H.a * transverseSchurDet H - transverseSchurMixed H).coeff 0 at h0
  rw [_root_.Polynomial.coeff_sub, _root_.Polynomial.mul_coeff_zero,
    hdet0, hm0, sub_zero] at h0
  have ha0 := (mul_eq_zero.mp h0.symm).resolve_right hregular
  have h1 := congrArg (fun p : _root_.Polynomial R => p.coeff 1)
    (transverseSchur_det_identity H)
  change H.determinantCore.coeff 1 =
    (H.a * transverseSchurDet H - transverseSchurMixed H).coeff 1 at h1
  rw [_root_.Polynomial.coeff_sub, transverse_coeff_mul_one,
    hdet1, hm1, ha0, zero_mul, zero_add, sub_zero] at h1
  exact ⟨ha0, (mul_eq_zero.mp h1.symm).resolve_right hregular⟩

end LeadingKernel

/-- Actual second source correction in the full-rank transverse chart,
given the leading mixed-kernel equations.  No extra first- or second-layer
condition is postulated: both longitudinal vanishing coefficients and
the second adjugate correction follow from the original source clock. -/
theorem sourceTransverseSchurFrame_second_constraint
    {E : Type*} [Field E]
    (F : MvPolynomial (Fin 4) K) (m : ℕ) (hm : 3 ≤ m)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight m F)
    (hdet : hessianDeterminant F = 1)
    (φ : MvPolynomial (Fin 4) K →+* E) (u v w : E) :
    let H := sourceTransverseSchurFrame F m hbound φ u v w
    H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 →
    H.a.coeff 2 * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := H.a.coeff 2, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock E) := by
  let H := sourceTransverseSchurFrame F m hbound φ u v w
  change H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 → _
  intro hb hp hq hregular
  have hd : H.determinantCore =
      (_root_.Polynomial.X : _root_.Polynomial E) ^ (4*m-6) :=
    sourceTransverseSchurFrame_det F m (by omega) hbound hdet φ u v w
  have hz (n : ℕ) (hn : n < 4*m-6) : H.determinantCore.coeff n = 0 := by
    rw [hd]
    have hne : 4*m-6 ≠ n := Ne.symm (Nat.ne_of_lt hn)
    simp [_root_.Polynomial.coeff_X_pow, hne, Ne.symm hne]
  obtain ⟨ha0, ha1⟩ := transverseSchur_longitudinal_zero_one
    H hb hp hq hregular (hz 0 (by omega)) (hz 1 (by omega))
  exact transverseSchur_second_constraint H ha0 ha1 hb hp hq (hz 2 (by omega))




/-! ## Stationary regular anchors and Newton-edge rigidity

A regular transverse Hessian on a longitudinal slice, with no mixed
row, forces the normalized characteristic of a singular Hessian to
be stationary. If the longitudinal first derivative also vanishes on
that slice, it vanishes as an original source polynomial. This applies
to ANY singular polynomial Hessian, not merely the top transverse
layer; in particular it can be used on a differently weighted initial
form. No change of source coordinates is made.
-/

open MvPolynomial

/-- A singular full Hessian with a regular stationary anchor and
zero longitudinal derivative on that slice is independent of the
longitudinal variable (in the derivative sense). -/
theorem sourceStationary_regularAnchor_longitudinal_pderiv_zero
    (L : MvPolynomial (Unit ⊕ Fin 3) K) (a : K)
    (hdet : (hessian L).det = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hmix : ∀ i : Fin 3, sourceNegativeMixedHessian a L i = 0)
    (hfirst : referenceSlice a (pderiv (.inl ()) L) = 0) :
    pderiv (.inl ()) L = 0 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let E := FractionRing B
  let g : B →+* E := algebraMap B E
  obtain ⟨V, hV, hgrad⟩ :=
    exists_anchored_lineEval_gradient_eq L hdet (transverseGenericPoint a) hreg
  have hregular := sourceTransverseHessian_det_ne_zero_of_generic a L hreg
  let A := (sourceTransverseHessian a L).map g
  let W : Fin 3 → E := fun i => V (.inr i)
  have hA : A.det ≠ 0 := by
    change (g.mapMatrix (sourceTransverseHessian a L)).det ≠ 0
    rw [← RingHom.map_det]
    intro hz
    apply hregular
    exact IsFractionRing.injective B E (by simpa only [map_zero] using hz :
      g (sourceTransverseHessian a L).det = g 0)
  have hker : A *ᵥ W = 0 := by
    have hh := sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
    change A *ᵥ W = (fun i : Fin 3 => g (sourceNegativeMixedHessian a L i)) at hh
    rw [hh]
    funext i
    simp [hmix i]
  have hW : W = 0 := by
    by_contra hne
    exact hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨W, hne, hker⟩)
  let N : Matrix (Fin 3) (Fin 3) K := 0
  have hN (i : Fin 3) :
      V (.inr i) = g (∑ j : Fin 3, MvPolynomial.C (N i j) * X j) := by
    have hi := congrFun hW i
    change V (.inr i) = 0 at hi
    simp [N, hi]
  have htransport :=
    linearGradientTransport_of_fractionCharacteristic a L V N hV hN hgrad
  have hN3 : N ^ 3 = 0 := by simp [N]
  have hinj := linearLineEval_injective_of_cube_zero a N hN3
  apply hinj
  rw [htransport (.inl ()), hfirst]
  simp




/-! ## Supporting-edge exclusion in the stationary branch

The new weight (a,b,b,b), with 0<a<b, is chosen to touch both the
old pure transverse top and an offending longitudinal monomial.
On x=0 both exact source faces have identical restrictions. The
new face has no x-linear term since a is strictly between 0 and b.
The stationary-anchor theorem therefore forbids every longitudinal
monomial on this face. The final support argument chooses the
maximal offending slope from the finite actual source support.
-/

private abbrev StationarySource (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

private abbrev StationaryExponent := (Unit ⊕ Fin 3) →₀ ℕ

/-- The longitudinal exponent is detected without cancellation by
the coefficient of X₀ times the longitudinal partial derivative. -/
theorem stationary_coeff_X_mul_pderiv
    (P : StationarySource K) (d : StationaryExponent) :
    MvPolynomial.coeff d (X (.inl ()) * pderiv (.inl ()) P) =
      (d (.inl ()) : K) * MvPolynomial.coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul]
    by_cases h : e = d
    · subst e
      simp [nsmul_eq_mul]
    · simp [MvPolynomial.coeff_monomial, h]
  | add p q hp hq =>
    simp only [map_add, mul_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem stationary_support_longitudinal_zero
    (P : StationarySource K) (hP : pderiv (.inl ()) P = 0)
    (d : StationaryExponent) (hd : MvPolynomial.coeff d P ≠ 0) :
    d (.inl ()) = 0 := by
  have h := stationary_coeff_X_mul_pderiv P d
  rw [hP, mul_zero, MvPolynomial.coeff_zero] at h
  have hz : (d (.inl ()) : K) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_right hd
  exact_mod_cast hz

/-- Positive longitudinal powers disappear at the honest source slice. -/
theorem stationary_referenceSlice_zero_of_support
    (P : StationarySource K)
    (h : ∀ d : StationaryExponent, MvPolynomial.coeff d P ≠ 0 →
      d (.inl ()) ≠ 0) :
    referenceSlice 0 P = 0 := by
  classical
  change MvPolynomial.aeval
    (Sum.elim (fun _ : Unit => MvPolynomial.C (0 : K)) X) P = 0
  apply MvPolynomial.aeval_eq_zero
  intro d hd
  refine ⟨.inl (), Finsupp.mem_support_iff.mpr (h d hd), ?_⟩
  simp

/-- Supporting edge weight, without clearing or changing the source. -/
def stationaryEdgeWeight (a b : ℤ) : Unit ⊕ Fin 3 → ℤ :=
  Sum.elim (fun _ => a) (fun _ => b)

theorem stationaryEdge_weight_eq (a b : ℤ) (d : StationaryExponent) :
    Finsupp.weight (stationaryEdgeWeight a b) d =
      a * (d (.inl ()) : ℤ) + b * Finsupp.weight transverseCubicWeight d := by
  rw [transverseCubicWeight_eq_transverseSum, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · simp [stationaryEdgeWeight, Fintype.sum_sum_type, Fin.sum_univ_three,
      nsmul_eq_mul] <;> ring
  · intro i
    simp

/-- An actual supporting face of slope b/a>1 retains the old
transverse top exactly on the longitudinal-zero slice. -/
theorem stationaryEdge_referenceSlice_eq
    (F : StationarySource K) (m a b : ℤ) (hb : 0 < b) :
    referenceSlice 0 (initialForm (stationaryEdgeWeight a b) (b*m) F) =
      referenceSlice 0 (initialForm transverseCubicWeight m F) := by
  classical
  let G := initialForm (stationaryEdgeWeight a b) (b*m) F
  let L := initialForm transverseCubicWeight m F
  have hz : referenceSlice 0 (G - L) = 0 := by
    apply stationary_referenceSlice_zero_of_support
    intro d hd h0
    apply hd
    have hw := stationaryEdge_weight_eq a b d
    rw [h0, Nat.cast_zero, mul_zero, zero_add] at hw
    have he : Finsupp.weight (stationaryEdgeWeight a b) d = b*m ↔
        Finsupp.weight transverseCubicWeight d = m := by
      rw [hw]
      constructor
      · intro h
        exact (mul_left_cancel₀ (ne_of_gt hb) h)
      · intro h
        rw [h]
    change MvPolynomial.coeff d (G - L) = 0
    simp only [G, L, MvPolynomial.coeff_sub, coeff_initialForm, he, sub_self]
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- No longitudinal linear term survives on a face of slope >1:
a/b is strictly between zero and one, whereas transverse weights
are integers. This is a statement about the original polynomial. -/
theorem stationaryEdge_firstDerivative_slice_zero
    (F : StationarySource K) (m a b : ℤ) (ha : 0 < a) (hab : a < b) :
    referenceSlice 0
      (pderiv (.inl ()) (initialForm (stationaryEdgeWeight a b) (b*m) F)) = 0 := by
  classical
  let G := initialForm (stationaryEdgeWeight a b) (b*m) F
  have hhom := pderiv_isWeightedHomogeneous
    (initialForm_isWeightedHomogeneous (stationaryEdgeWeight a b) (b*m) F)
    (Sum.inl ())
  change (pderiv (.inl ()) G).IsWeightedHomogeneous
    (stationaryEdgeWeight a b) (b*m-a) at hhom
  apply stationary_referenceSlice_zero_of_support
  intro d hd h0
  have he := hhom hd
  rw [stationaryEdge_weight_eq, h0, Nat.cast_zero, mul_zero, zero_add] at he
  have hprod : b * (m - Finsupp.weight transverseCubicWeight d) = a := by
    nlinarith only [he]
  have hb : 0 < b := ha.trans hab
  by_cases h : 1 ≤ m - Finsupp.weight transverseCubicWeight d
  · have hh := mul_le_mul_of_nonneg_left h (le_of_lt hb)
    nlinarith only [hh, hprod, hab]
  · have hh : m - Finsupp.weight transverseCubicWeight d ≤ 0 := by omega
    have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) hh
    linarith

/-- A steep supporting face of a constant-Hessian source with a
regular transverse top cannot depend on the longitudinal variable.
The full face is singular by the actual maximal-weight identity,
not by an additional endpoint premise. -/
theorem sourceStationary_supportingEdge_longitudinal_zero
    (F : StationarySource K) (m a b : ℤ) (hm : 2 ≤ m)
    (ha : 0 < a) (hab : a < b)
    (hcap : IsWeightLE (stationaryEdgeWeight a b) (b*m) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hreg : MvPolynomial.aeval (transverseGenericPoint (0 : K))
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    pderiv (.inl ()) (initialForm (stationaryEdgeWeight a b) (b*m) F) = 0 := by
  classical
  let w := stationaryEdgeWeight a b
  let G := initialForm w (b*m) F
  let L := initialForm transverseCubicWeight m F
  have hb : 0 < b := ha.trans hab
  have hclock : (Fintype.card (Unit ⊕ Fin 3) : ℤ) * (b*m) -
      2 * ∑ i : Unit ⊕ Fin 3, w i = 4*(b*m)-2*(a+3*b) := by
    have hc : (Fintype.card (Unit ⊕ Fin 3) : ℤ) = 4 := by decide
    rw [hc]
    simp [w, stationaryEdgeWeight, Fintype.sum_sum_type, Fin.sum_univ_three] <;> ring
  have hpos : 0 < 4*(b*m)-2*(a+3*b) := by
    have hh := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hm)
    nlinarith only [hh, hab]
  have hsing : (hessian G).det = 0 := by
    have h := initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      w (b*m) F hcap
    rw [hclock, hdet, initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C w δ) _ (ne_of_gt hpos)] at h
    exact h.symm
  have hs : referenceSlice 0 G = referenceSlice 0 L :=
    stationaryEdge_referenceSlice_eq F m a b hb
  let φ := (MvPolynomial.aeval (transverseGenericPoint (0 : K))).toRingHom
  have hMat :
      φ.mapMatrix ((hessian G).submatrix Sum.inr Sum.inr) =
      φ.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr) := by
    apply Matrix.ext
    intro i j
    change MvPolynomial.aeval (transverseGenericPoint (0 : K))
        (pderiv (.inr j) (pderiv (.inr i) G)) =
      MvPolynomial.aeval (transverseGenericPoint (0 : K))
        (pderiv (.inr j) (pderiv (.inr i) L))
    rw [← referenceSlice_fractionEvaluation, ← referenceSlice_fractionEvaluation]
    simp only [← referenceSlice_pderiv, hs]
  have hregG : MvPolynomial.aeval (transverseGenericPoint (0 : K))
      ((hessian G).submatrix Sum.inr Sum.inr).det ≠ 0 := by
    intro hz
    apply hreg
    have h := congrArg Matrix.det hMat
    rw [← RingHom.map_det, ← RingHom.map_det] at h
    exact h.symm.trans hz
  have hfirst : referenceSlice 0 (pderiv (.inl ()) G) = 0 :=
    stationaryEdge_firstDerivative_slice_zero F m a b ha hab
  have hmix (i : Fin 3) : sourceNegativeMixedHessian 0 G i = 0 := by
    unfold sourceNegativeMixedHessian
    rw [HC4.Newton.pderiv_comm_backport (.inl ()) (.inr i) G,
      ← referenceSlice_pderiv, hfirst, map_zero, neg_zero]
  exact sourceStationary_regularAnchor_longitudinal_pderiv_zero
    G 0 hsing hregG hmix hfirst

/-- Stationary regular transverse top implies the full source support
lies below total degree m. The supporting weight is selected by a
maximum over the finite ORIGINAL support, so no slope or edge
existence assumption is added. -/
theorem sourceStationary_totalDegree_support_bound
    (F : StationarySource K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hstationary : pderiv (.inl ()) (initialForm transverseCubicWeight m F) = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint (0 : K))
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    ∀ d ∈ F.support, (d (.inl ()) : ℤ) +
      Finsupp.weight transverseCubicWeight d ≤ m := by
  classical
  let p : StationaryExponent → ℤ := fun d => d (.inl ())
  let q : StationaryExponent → ℤ := Finsupp.weight transverseCubicWeight
  have htop (d : StationaryExponent) (hd : d ∈ F.support) (hq : q d = m) :
      p d = 0 := by
    have hc : MvPolynomial.coeff d (initialForm transverseCubicWeight m F) ≠ 0 := by
      rw [coeff_initialForm, if_pos hq]
      exact MvPolynomial.mem_support_iff.mp hd
    have hz := stationary_support_longitudinal_zero _ hstationary d hc
    simp [p, hz]
  intro d hd
  change p d + q d ≤ m
  by_contra hn
  have hqd : q d ≤ m := hcap hd
  have hlt : q d < m := by
    by_contra hnot
    have he : q d = m := by omega
    have hz := htop d hd he
    omega
  let s := F.support.filter (fun e => q e < m)
  have hds : d ∈ s := Finset.mem_filter.mpr ⟨hd, hlt⟩
  let score : StationaryExponent → ℚ := fun e =>
    (p e : ℚ) / ((m-q e : ℤ) : ℚ)
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image s score ⟨d, hds⟩
  have he' : e ∈ F.support ∧ q e < m := Finset.mem_filter.mp he
  let a : ℤ := m-q e
  let b : ℤ := p e
  have ha : 0 < a := by dsimp [a]; omega
  have hdpos : 0 < m-q d := by omega
  have hscore : (1 : ℚ) < score d := by
    change (1 : ℚ) < (p d : ℚ) / ((m-q d : ℤ) : ℚ)
    apply (lt_div_iff₀ (show (0 : ℚ) < ((m-q d : ℤ) : ℚ) by
      exact_mod_cast hdpos)).2
    rw [one_mul]
    exact_mod_cast (show m-q d < p d by omega)
  have hab : a < b := by
    have hh := hscore.trans_le (hmax d hds)
    change (1 : ℚ) < (b : ℚ) / (a : ℚ) at hh
    have hh' := (lt_div_iff₀ (show (0 : ℚ) < (a : ℚ) by exact_mod_cast ha)).mp hh
    rw [one_mul] at hh'
    exact_mod_cast hh'
  have hedge : IsWeightLE (stationaryEdgeWeight a b) (b*m) F := by
    intro f hf
    rw [stationaryEdge_weight_eq]
    change a * p f + b * q f ≤ b*m
    have hqf : q f ≤ m := hcap hf
    by_cases heq : q f = m
    · simp only [htop f hf heq, heq, mul_zero, zero_add, le_refl]
    · have hflt : q f < m := by omega
      have hfs : f ∈ s := Finset.mem_filter.mpr ⟨hf, hflt⟩
      have hh := hmax f hfs
      change (p f : ℚ) / ((m-q f : ℤ) : ℚ) ≤ (b : ℚ) / (a : ℚ) at hh
      have hpos : 0 < m-q f := by omega
      have hc := (div_le_div_iff₀
        (show (0 : ℚ) < ((m-q f : ℤ) : ℚ) by exact_mod_cast hpos)
        (show (0 : ℚ) < (a : ℚ) by exact_mod_cast ha)).mp hh
      have hc' : p f * a ≤ b * (m-q f) := by exact_mod_cast hc
      nlinarith only [hc']
  have htouch : Finsupp.weight (stationaryEdgeWeight a b) e = b*m := by
    rw [stationaryEdge_weight_eq]
    change a * b + b * q e = b*m
    dsimp [a]
    ring
  have hcoef : MvPolynomial.coeff e
      (initialForm (stationaryEdgeWeight a b) (b*m) F) ≠ 0 := by
    rw [coeff_initialForm, if_pos htouch]
    exact MvPolynomial.mem_support_iff.mp he'.1
  have hzero := sourceStationary_supportingEdge_longitudinal_zero
    F m a b hm ha hab hedge hdet hreg
  have hezero := stationary_support_longitudinal_zero _ hzero e hcoef
  have hbzero : b = 0 := by simp [b, p, hezero]
  omega


end
end HC4.Polynomial.RankThreeCubic
