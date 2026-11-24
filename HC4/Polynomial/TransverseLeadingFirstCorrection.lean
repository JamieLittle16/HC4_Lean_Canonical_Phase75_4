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
    [CommRing E] [Algebra K E]
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
  let φ : StationarySource K →+* FractionRing (MvPolynomial (Fin 3) K) :=
    (MvPolynomial.aeval (transverseGenericPoint (0 : K)) :
      StationarySource K →ₐ[K] FractionRing (MvPolynomial (Fin 3) K)).toRingHom
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




/-! ## Stationary cubic endpoint

The stationary Newton bound gives total degree at most three at
transverse cap three. A quadratic gradient has its exact marked
secant equal to the Hessian at the midpoint applied to the marked
axis. This proves an actual collision obstruction in that branch.
No general homogeneous-Hessian classification is needed.
-/

def stationaryAxisEval (t : K) : StationarySource K →ₐ[K] K :=
  MvPolynomial.aeval (Sum.elim (fun _ : Unit => t) (fun _ : Fin 3 => 0))

private theorem stationaryAxisEval_monomial_zero (t c : K)
    (d : StationaryExponent) (j : Fin 3) (hj : d (.inr j) ≠ 0) :
    stationaryAxisEval t (MvPolynomial.monomial d c) = 0 := by
  classical
  unfold stationaryAxisEval
  apply MvPolynomial.aeval_eq_zero
  intro e he
  rw [MvPolynomial.coeff_monomial] at he
  have hde : d = e := by
    by_contra hn
    simp [hn] at he
  subst e
  exact ⟨.inr j, Finsupp.mem_support_iff.mpr hj, rfl⟩

private theorem stationaryAxisEval_monomial_midpoint
    (d : StationaryExponent) (c : K)
    (hd : Finsupp.weight (stationaryEdgeWeight 1 1) d ≤ 2) :
    stationaryAxisEval 1 (MvPolynomial.monomial d c) -
      stationaryAxisEval 0 (MvPolynomial.monomial d c) =
      stationaryAxisEval (1/2) (pderiv (.inl ()) (MvPolynomial.monomial d c)) := by
  classical
  by_cases ht : ∃ j : Fin 3, d (.inr j) ≠ 0
  · obtain ⟨j, hj⟩ := ht
    rw [stationaryAxisEval_monomial_zero 1 c d j hj,
      stationaryAxisEval_monomial_zero 0 c d j hj, sub_self, pderiv_monomial]
    symm
    apply stationaryAxisEval_monomial_zero (j := j)
    simpa [Finsupp.sub_apply, Finsupp.single_apply] using hj
  · push_neg at ht
    have hsingle : d = Finsupp.single (Sum.inl ()) (d (.inl ())) := by
      apply Finsupp.ext
      intro i
      cases i with
      | inl u => cases u; simp
      | inr j => simp [ht j]
    have hwt := stationaryEdge_weight_eq 1 1 d
    rw [transverseCubicWeight_eq_transverseSum] at hwt
    simp only [ht, Nat.cast_zero, add_zero, one_mul, mul_zero] at hwt
    have hn : d (.inl ()) ≤ 2 := by omega
    let n := d (.inl ())
    have hns : n = 0 ∨ n = 1 ∨ n = 2 := by dsimp [n]; omega
    rw [hsingle]
    change stationaryAxisEval 1 (MvPolynomial.monomial (Finsupp.single (.inl ()) n) c) -
      stationaryAxisEval 0 (MvPolynomial.monomial (Finsupp.single (.inl ()) n) c) =
      stationaryAxisEval (1/2)
        (pderiv (.inl ()) (MvPolynomial.monomial (Finsupp.single (.inl ()) n) c))
    rw [pderiv_monomial_single]
    rcases hns with h | h | h <;> rw [h] <;>
      simp [← MvPolynomial.C_mul_X_pow_eq_monomial, stationaryAxisEval] <;>
      ring

/-- The exact marked secant for any polynomial of total degree ≤2. -/
theorem stationaryAxisEval_quadratic_midpoint
    (P : StationarySource K)
    (hcap : IsWeightLE (stationaryEdgeWeight 1 1) 2 P) :
    stationaryAxisEval 1 P - stationaryAxisEval 0 P =
      stationaryAxisEval (1/2) (pderiv (.inl ()) P) := by
  classical
  have hsum := P.as_sum
  calc
    _ = ∑ d ∈ P.support,
        (stationaryAxisEval 1 (MvPolynomial.monomial d (MvPolynomial.coeff d P)) -
         stationaryAxisEval 0 (MvPolynomial.monomial d (MvPolynomial.coeff d P))) := by
      rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← hsum]
    _ = ∑ d ∈ P.support, stationaryAxisEval (1/2)
        (pderiv (.inl ()) (MvPolynomial.monomial d (MvPolynomial.coeff d P))) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact stationaryAxisEval_monomial_midpoint d _ (hcap hd)
    _ = _ := by rw [← map_sum, ← map_sum, ← hsum]

/-- Any total-degree-three determinant-one source excludes the
marked gradient collision, by its actual midpoint Hessian. -/
theorem totalDegreeThree_markedCollision_impossible
    (F : StationarySource K)
    (hcap : IsWeightLE (stationaryEdgeWeight 1 1) 3 F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    False := by
  classical
  let e := (stationaryAxisEval (1/2 : K)).toRingHom
  let A := e.mapMatrix (hessian F)
  have hcol (i : Unit ⊕ Fin 3) : A i (.inl ()) = 0 := by
    have hp := hcap.pderiv i
    have hi : stationaryEdgeWeight 1 1 i = 1 := by cases i <;> rfl
    rw [hi] at hp
    have hp' : IsWeightLE (stationaryEdgeWeight 1 1) 2 (pderiv i F) := by
      simpa only [show (3 : ℤ) - 1 = 2 by norm_num] using hp
    have h := stationaryAxisEval_quadratic_midpoint (pderiv i F) hp'
    rw [hcoll i, sub_self] at h
    exact h.symm
  have hz : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero (.inl ()) hcol
  change (e.mapMatrix (hessian F)).det = 0 at hz
  rw [← RingHom.map_det] at hz
  change e (hessianDeterminant F) = 0 at hz
  rw [hdet] at hz
  apply hδ
  change stationaryAxisEval (1/2 : K) (MvPolynomial.C δ) = 0 at hz
  simpa using hz

/-- The actual stationary regular cap-three branch is closed, with
no auxiliary total-degree assumption: the Newton support bound
supplies that bound for the original source. -/
theorem sourceStationary_cubic_markedCollision_impossible
    (F : StationarySource K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hstationary : pderiv (.inl ()) (initialForm transverseCubicWeight 3 F) = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint (0 : K))
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    False := by
  apply totalDegreeThree_markedCollision_impossible F _ hδ hdet hcoll
  intro d hd
  rw [stationaryEdge_weight_eq, one_mul, one_mul]
  exact sourceStationary_totalDegree_support_bound F 3 (by norm_num)
    hcap hdet hstationary hreg d hd




/-! ## Pull the nilpotent characteristic back to the actual source

The inverse shear is polynomial. In the original coordinates the
characteristic velocity is (1, Ny-(x-a)N²y). Its Hessian kernel is
an exact source polynomial identity; it is not a claim that the
shear preserves the Hessian determinant of the full source.
-/

/-- The transverse linear vector associated to a constant matrix. -/
def sourceLinearVector (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    StationarySource K :=
  ∑ j : Fin 3, MvPolynomial.C (M i j) * X (.inr j)

def referenceLinearVector (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    MvPolynomial (Fin 3) K :=
  ∑ j : Fin 3, MvPolynomial.C (M i j) * X j

/-- Linear matrix forms transform by the actual characteristic pencil. -/
theorem linearLineEval_sourceLinearVector
    (a : K) (M N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    linearLineEval a N (sourceLinearVector M i) =
      _root_.Polynomial.C (referenceLinearVector M i) +
        _root_.Polynomial.C (referenceLinearVector (M * N) i) *
          _root_.Polynomial.X := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hC (c : K) :
      linearLineEval a N (MvPolynomial.C c) =
        _root_.Polynomial.C (MvPolynomial.C c) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have hX (j : Fin 3) :
      linearLineEval a N (X (.inr j)) =
        _root_.Polynomial.C (X j : B) +
        _root_.Polynomial.C (referenceLinearVector N j) * _root_.Polynomial.X := by
    simp [linearLineEval, lineEval, referenceLinearVector]
  have hprod :
      (∑ j : Fin 3, MvPolynomial.C (M i j) * referenceLinearVector N j) =
        referenceLinearVector (M * N) i := by
    unfold referenceLinearVector
    calc
      _ = ∑ j : Fin 3, ∑ k : Fin 3,
          MvPolynomial.C (M i j * N j k) * (X k : B) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← mul_assoc, ← map_mul]
      _ = ∑ k : Fin 3, ∑ j : Fin 3,
          MvPolynomial.C (M i j * N j k) * (X k : B) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_mul, Matrix.mul_apply, map_sum]
  calc
    _ = ∑ j : Fin 3, _root_.Polynomial.C (MvPolynomial.C (M i j)) *
        (_root_.Polynomial.C (X j : B) +
          _root_.Polynomial.C (referenceLinearVector N j) * _root_.Polynomial.X) := by
        simp only [sourceLinearVector, map_sum, map_mul, hC, hX]
    _ = _root_.Polynomial.C (referenceLinearVector M i) +
        _root_.Polynomial.C
          (∑ j : Fin 3, MvPolynomial.C (M i j) * referenceLinearVector N j) *
            _root_.Polynomial.X := by
        simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← map_mul, ← map_sum, referenceLinearVector]
    _ = _ := by rw [hprod]

/-- The source velocity of a nilpotent straight characteristic. -/
def sourceNilpotentVelocity (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (i : Fin 3) : StationarySource K :=
  sourceLinearVector N i -
    (X (.inl ()) - MvPolynomial.C a) * sourceLinearVector (N ^ 2) i

theorem linearLineEval_sourceNilpotentVelocity
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (i : Fin 3) :
    linearLineEval a N (sourceNilpotentVelocity a N i) =
      _root_.Polynomial.C (referenceLinearVector N i) := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hx : linearLineEval a N (X (.inl ()) - MvPolynomial.C a) =
      (_root_.Polynomial.X : _root_.Polynomial B) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have h2 : N * N = N ^ 2 := (pow_two N).symm
  have h3 : N ^ 2 * N = 0 := by rw [← pow_succ, hN]
  have hz : referenceLinearVector (0 : Matrix (Fin 3) (Fin 3) K) i = 0 := by
    simp [referenceLinearVector]
  rw [sourceNilpotentVelocity, map_sub, map_mul, hx,
    linearLineEval_sourceLinearVector, linearLineEval_sourceLinearVector, h2, h3, hz,
    map_zero, zero_mul, add_zero]
  ring

/-- The exact gradient-transport identity gives a polynomial kernel
equation in the ORIGINAL source, simultaneously for all gradient
components. This is a first-order system with no rational denominators. -/
theorem sourceNilpotent_gradient_kernel
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    ∀ i : Unit ⊕ Fin 3,
      pderiv (.inl ()) (pderiv i L) +
        ∑ j : Fin 3, sourceNilpotentVelocity a N j * pderiv (.inr j) (pderiv i L) = 0 := by
  classical
  intro i
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  have he : lineEval (K := K) z V = linearLineEval a N := rfl
  have h := transverse_lineEval_derivative z V (pderiv i L)
  rw [he, hgrad i, _root_.Polynomial.derivative_C] at h
  have h' : linearLineEval a N (pderiv (.inl ()) (pderiv i L)) +
      ∑ j : Fin 3, _root_.Polynomial.C (referenceLinearVector N j) *
        linearLineEval a N (pderiv (.inr j) (pderiv i L)) = 0 := by
    simpa [Fintype.sum_sum_type, V] using h.symm
  apply linearLineEval_injective_of_cube_zero a N hN
  simp only [map_add, map_sum, map_mul, linearLineEval_sourceNilpotentVelocity a N hN,
    map_zero]
  exact h'




/-! ## Source-wide self-adjointness and nilpotent gradient evolution

The differentiated transport equation T(I+tN)=M, with both Hessians
symmetric, makes TN symmetric at EVERY characteristic time (not only
at the reference slice). Injective pullback gives the same identity
on the original leading source. Euler homogeneity then turns the
source kernel equation into a nilpotent matrix ODE for its transverse
gradient. Neither identity asserts that the full source Hessian is
preserved by the nonlinear characteristic substitution.
-/

/-- Self-adjointness at all characteristic times, pulled back to
the actual source transverse Hessian. -/
theorem sourceNilpotent_hessian_selfAdjoint
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let A := N.map MvPolynomial.C
    (H * A).transpose = H * A := by
  classical
  let B := MvPolynomial (Fin 3) K
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  let C := (N.map (MvPolynomial.C : K →+* B)).map _root_.Polynomial.C
  have hT (i j : Fin 3) : T i j = T j i := by
    change linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) L)) =
      linearLineEval a N (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have hM (i j : Fin 3) : M i j = M j i := by
    change referenceSlice a (pderiv (.inr j) (pderiv (.inr i) L)) =
      referenceSlice a (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have ht := transverseHessian_transport_of_linear_gradient a N L hgrad
  change T * (1 + (_root_.Polynomial.X : _root_.Polynomial B) • C) =
    M.map _root_.Polynomial.C at ht
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at ht
  have he (i j : Fin 3) :
      T i j + (_root_.Polynomial.X : _root_.Polynomial B) * (T * C) i j =
        _root_.Polynomial.C (M i j) := by
    have h := congrArg (fun Q : Matrix (Fin 3) (Fin 3) (_root_.Polynomial B) =>
      Q i j) ht
    exact h
  have hTC (i j : Fin 3) : (T * C) i j = (T * C) j i := by
    apply mul_left_cancel₀ (_root_.Polynomial.X_ne_zero (R := B))
    have h₁ := he i j
    rw [hT i j, hM i j] at h₁
    exact add_left_cancel (h₁.trans (he j i).symm)
  have hc (r : K) : linearLineEval a N (MvPolynomial.C r) =
      _root_.Polynomial.C (MvPolynomial.C r) := by
    simp [linearLineEval, lineEval, IsScalarTower.algebraMap_apply K B
      (_root_.Polynomial B), _root_.Polynomial.algebraMap_eq]
  have hmap (i j : Fin 3) :
      linearLineEval a N ((H * A) i j) = (T * C) i j := by
    simp only [Matrix.mul_apply, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    change linearLineEval a N (H i k) * linearLineEval a N (MvPolynomial.C (N k j)) =
      linearLineEval a N (H i k) * _root_.Polynomial.C (MvPolynomial.C (N k j))
    rw [hc]
  change (H * A).transpose = H * A
  apply Matrix.ext
  intro i j
  change (H * A) j i = (H * A) i j
  apply linearLineEval_injective_of_cube_zero a N hN
  rw [hmap, hmap]
  exact hTC j i

/-- Transverse Euler identity before any longitudinal specialization. -/
theorem sourceTransverseEuler_of_weight
    (P : StationarySource K) (n : ℕ)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight (n : ℤ)) :
    (∑ j : Fin 3, X (.inr j) * pderiv (.inr j) P) =
      (n : StationarySource K) * P := by
  classical
  have hnat : P.IsWeightedHomogeneous transverseCubicNatWeight n := by
    intro d hd
    have he : ((Finsupp.weight transverseCubicNatWeight d : ℕ) : ℤ) =
        Finsupp.weight transverseCubicWeight d := by
      simp only [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases i with
      | inl u => cases u; simp [transverseCubicNatWeight, transverseCubicWeight]
      | inr j => simp [transverseCubicNatWeight, transverseCubicWeight, nsmul_eq_mul]
    have hh := hP hd
    rw [← he] at hh
    exact_mod_cast hh
  have h := hnat.sum_weight_X_mul_pderiv
  simpa [transverseCubicNatWeight, Fintype.sum_sum_type, nsmul_eq_mul] using h

/-- Euler's identity in Hessian-vector form. Explicit entrywise
rewriting avoids reducing the matrix multiplication implementation
during definitional equality checking. -/
theorem sourceTransverseHessian_mulVec_coordinates
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1)) :
    (hessian L).submatrix Sum.inr Sum.inr *ᵥ
      (fun j : Fin 3 => X (Sum.inr j)) =
      (n : StationarySource K) • (fun i : Fin 3 => pderiv (Sum.inr i) L) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hessian_apply,
    Pi.smul_apply, smul_eq_mul]
  have hp := pderiv_isWeightedHomogeneous hL (Sum.inr i)
  have hp' : (pderiv (Sum.inr i) L).IsWeightedHomogeneous
      transverseCubicWeight (n : ℤ) := by
    simpa [transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight (K := K) (pderiv (Sum.inr i) L) n hp'
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The matrix step of the gradient ODE is independent of the
polynomial ring. Keep its elaboration over an abstract ring rather
than unfolding the concrete multivariate polynomial arithmetic. -/
private theorem sourceNilpotent_gradient_ode_algebra
    {R : Type*} [CommRing R]
    (A H : Matrix (Fin 3) (Fin 3) R)
    (G Y W D : Fin 3 → R) (t c : R)
    (hcomm : A.transpose * H = H * A)
    (hE : H *ᵥ Y = c • G)
    (hW : W = A *ᵥ Y - t • ((A ^ 2) *ᵥ Y))
    (hk : D + H *ᵥ W = 0) :
    D = -c • (A.transpose *ᵥ G - t • ((A.transpose ^ 2) *ᵥ G)) := by
  have hcomm2 : H * A ^ 2 = A.transpose ^ 2 * H := by
    calc
      _ = (H * A) * A := by rw [pow_two, Matrix.mul_assoc]
      _ = (A.transpose * H) * A := congrArg (fun M => M * A) hcomm.symm
      _ = A.transpose * (H * A) := Matrix.mul_assoc _ _ _
      _ = A.transpose * (A.transpose * H) :=
        congrArg (fun M => A.transpose * M) hcomm.symm
      _ = _ := by rw [pow_two, Matrix.mul_assoc]
  have h1 : H *ᵥ (A *ᵥ Y) = c • (A.transpose *ᵥ G) := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul]
  have h2 : H *ᵥ ((A ^ 2) *ᵥ Y) = c • (A.transpose ^ 2 *ᵥ G) := by
    rw [Matrix.mulVec_mulVec, hcomm2, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul]
  have hHW : H *ᵥ W = c • (A.transpose *ᵥ G - t • (A.transpose ^ 2 *ᵥ G)) := by
    rw [hW, Matrix.mulVec_sub, Matrix.mulVec_smul, h1, h2]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hHW] at hk
  have hh : D = -(c • (A.transpose *ᵥ G - t • (A.transpose ^ 2 *ᵥ G))) :=
    eq_neg_iff_add_eq_zero.mpr hk
  simpa only [neg_smul] using hh

/-- The transverse gradient obeys an exact first-order nilpotent
matrix evolution at fixed ORIGINAL transverse coordinates.
Here n=m-1 for a leading layer of transverse degree m. -/
theorem sourceNilpotent_transverseGradient_ode
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
    let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
    let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
    (fun i : Fin 3 => pderiv (Sum.inl ()) (G i)) =
      - (n : StationarySource K) •
        (A.transpose *ᵥ G - t • ((A.transpose ^ 2) *ᵥ G)) := by
  classical
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.map MvPolynomial.C
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
  let Y : Fin 3 → StationarySource K := fun i => X (.inr i)
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  let W : Fin 3 → StationarySource K := sourceNilpotentVelocity a N
  let D : Fin 3 → StationarySource K := fun i => pderiv (.inl ()) (G i)
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    simp only [H, Matrix.transpose_apply, Matrix.submatrix_apply, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have hcomm : A.transpose * H = H * A := by
    have h := sourceNilpotent_hessian_selfAdjoint a N hN L (fun i => hgrad (.inr i))
    change (H * A).transpose = H * A at h
    rwa [Matrix.transpose_mul, hH] at h
  have hE : H *ᵥ Y = (n : StationarySource K) • G :=
    sourceTransverseHessian_mulVec_coordinates L n hL
  have hA2 : A ^ 2 = (N ^ 2).map (MvPolynomial.C : K →+* StationarySource K) := by
    simp only [A, pow_two, Matrix.map_mul]
  have hW : W = A *ᵥ Y - t • ((A ^ 2) *ᵥ Y) := by
    rw [hA2]
    funext i
    simp only [W, sourceNilpotentVelocity, sourceLinearVector, A, t, Y,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hk : D + H *ᵥ W = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, D, G, H, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, hessian_apply]
    have hi := sourceNilpotent_gradient_kernel a N hN L hgrad (.inr i)
    rw [show (∑ j : Fin 3, pderiv (.inr j) (pderiv (.inr i) L) * W j) =
        ∑ j : Fin 3, W j * pderiv (.inr j) (pderiv (.inr i) L) by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _]
    exact hi
  exact sourceNilpotent_gradient_ode_algebra A H G Y W D t
    (n : StationarySource K) hcomm hE hW hk



/-! ## Uniform longitudinal rigidity in the pole-free branch

Use an abstract derivation on an abstract commutative ring for the
nilpotent ODE calculation. Only the final application knows that the
derivation is the longitudinal partial derivative of the source.
-/

private def nilpotentVectorDeriv {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (v : Fin 3 → R) : Fin 3 → R :=
  fun i => D (v i)

private theorem nilpotentVectorDeriv_sub {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (u v : Fin 3 → R) :
    nilpotentVectorDeriv D (u-v) =
      nilpotentVectorDeriv D u - nilpotentVectorDeriv D v := by
  funext i
  simp [nilpotentVectorDeriv, Pi.sub_apply]

private theorem nilpotentVectorDeriv_smul {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R) (r : R) (v : Fin 3 → R) :
    nilpotentVectorDeriv D (r • v) =
      D r • v + r • nilpotentVectorDeriv D v := by
  funext i
  simp only [nilpotentVectorDeriv, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Derivation.leibniz]
  ring

private theorem nilpotentVectorDeriv_mulVec {k R : Type*} [CommRing k] [CommRing R]
    [Algebra k R] (D : Derivation k R R)
    (A : Matrix (Fin 3) (Fin 3) R) (hA : ∀ i j, D (A i j) = 0)
    (v : Fin 3 → R) :
    nilpotentVectorDeriv D (A *ᵥ v) = A *ᵥ nilpotentVectorDeriv D v := by
  classical
  funext i
  simp only [nilpotentVectorDeriv, Matrix.mulVec, dotProduct, map_sum,
    Derivation.leibniz, smul_eq_mul, hA, mul_zero, add_zero]

/-- Differentiating a nilpotent ODE twice and three times. This is
independent of the number of polynomial source variables. -/
private theorem nilpotentVectorDeriv_second_third
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i j, D (A i j) = 0) (h3 : A ^ 3 = 0)
    (c t : R) (hc : D c = 0) (ht : D t = 1) (G : Fin 3 → R)
    (hode : nilpotentVectorDeriv D G =
      -c • (A *ᵥ G - t • (A ^ 2 *ᵥ G))) :
    nilpotentVectorDeriv D (nilpotentVectorDeriv D G) =
      (c * (c+1)) • (A ^ 2 *ᵥ G) ∧
    nilpotentVectorDeriv D (nilpotentVectorDeriv D (nilpotentVectorDeriv D G)) = 0 := by
  classical
  let V := A *ᵥ G
  let W := A ^ 2 *ᵥ G
  have hA2 (i j : Fin 3) : D ((A ^ 2) i j) = 0 := by
    simp only [pow_two, Matrix.mul_apply, map_sum, Derivation.leibniz,
      hA, smul_zero, add_zero, Finset.sum_const_zero]
  have hleft : A * A ^ 2 = 0 := by rw [← pow_succ', h3]
  have hright : A ^ 2 * A = 0 := by rw [← pow_succ, h3]
  have hfour : A ^ 2 * A ^ 2 = 0 := by
    calc
      _ = (A ^ 2 * A) * A := by
        calc
          A ^ 2 * A ^ 2 = A ^ 2 * (A * A) := by rw [← pow_two]
          _ = _ := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hright, zero_mul]
  have hAV : A *ᵥ V = W := by
    dsimp only [V, W]
    rw [Matrix.mulVec_mulVec, pow_two]
  have hAW : A *ᵥ W = 0 := by
    dsimp only [W]
    rw [Matrix.mulVec_mulVec, hleft, Matrix.zero_mulVec]
  have hA2V : A ^ 2 *ᵥ V = 0 := by
    dsimp only [V]
    rw [Matrix.mulVec_mulVec, hright, Matrix.zero_mulVec]
  have hA2W : A ^ 2 *ᵥ W = 0 := by
    dsimp only [W]
    rw [Matrix.mulVec_mulVec, hfour, Matrix.zero_mulVec]
  change nilpotentVectorDeriv D G = -c • (V - t • W) at hode
  have hV : nilpotentVectorDeriv D V = -c • W := by
    calc
      _ = A *ᵥ nilpotentVectorDeriv D G :=
        nilpotentVectorDeriv_mulVec D A hA G
      _ = _ := by
        rw [hode, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
          hAV, hAW, smul_zero, sub_zero]
  have hW : nilpotentVectorDeriv D W = 0 := by
    calc
      _ = A ^ 2 *ᵥ nilpotentVectorDeriv D G :=
        nilpotentVectorDeriv_mulVec D (A ^ 2) hA2 G
      _ = _ := by
        rw [hode, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
          hA2V, hA2W, smul_zero, sub_zero, smul_zero]
  have hsecond : nilpotentVectorDeriv D (nilpotentVectorDeriv D G) =
      (c * (c+1)) • W := by
    rw [hode, nilpotentVectorDeriv_smul, nilpotentVectorDeriv_sub,
      nilpotentVectorDeriv_smul, hV, hW, ht, map_neg, hc]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  refine ⟨hsecond, ?_⟩
  rw [hsecond, nilpotentVectorDeriv_smul, hW]
  have hcc : D (c * (c+1)) = 0 := by
    simp [Derivation.leibniz, hc]
  rw [hcc, zero_smul, smul_zero, add_zero]

/-- The actual transverse gradient is longitudinally quadratic, and
its second derivative is the explicit last nilpotent power. -/
theorem sourceNilpotent_transverseGradient_second_third
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.transpose.map MvPolynomial.C
    let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
    let c : StationarySource K := n
    (fun i : Fin 3 => pderiv (Sum.inl ()) (pderiv (Sum.inl ()) (G i))) =
      (c * (c+1)) • (A ^ 2 *ᵥ G) ∧
    ∀ i : Fin 3, pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) (G i))) = 0 := by
  classical
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) := N.transpose.map MvPolynomial.C
  let G : Fin 3 → StationarySource K := fun i => pderiv (.inr i) L
  let c : StationarySource K := n
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  let D : Derivation K (StationarySource K) (StationarySource K) := pderiv (.inl ())
  have hA (i j : Fin 3) : D (A i j) = 0 := by
    simp [D, A, Matrix.map_apply, pderiv_C]
  have h3N : N.transpose ^ 3 = 0 := by rw [← Matrix.transpose_pow, hN, Matrix.transpose_zero]
  have h3 : A ^ 3 = 0 := by
    have h : (N.transpose ^ 3).map (MvPolynomial.C : K →+* StationarySource K) =
        (0 : Matrix (Fin 3) (Fin 3) (StationarySource K)) := by
      rw [h3N]
      ext i j
      simp
    rw [show (3 : ℕ) = 2+1 by rfl, pow_succ, pow_two, Matrix.map_mul,
      Matrix.map_mul] at h
    rw [show (3 : ℕ) = 2+1 by rfl, pow_succ, pow_two]
    exact h
  have hc : D c = 0 := D.map_natCast n
  have ht : D t = 1 := by simp [D, t, pderiv_X]
  have hAT : (N.map (MvPolynomial.C : K →+* StationarySource K)).transpose = A := by
    ext i j
    rfl
  have hode := sourceNilpotent_transverseGradient_ode a N hN L n hL hgrad
  dsimp only at hode
  rw [hAT] at hode
  have hode' : nilpotentVectorDeriv D G = -c • (A *ᵥ G - t • (A ^ 2 *ᵥ G)) := hode
  obtain ⟨hsecond, hthird⟩ :=
    nilpotentVectorDeriv_second_third D A hA h3 c t hc ht G hode'
  refine ⟨hsecond, ?_⟩
  intro i
  exact congrFun hthird i

/-- Uniform longitudinal degree restriction on the original
transverse-homogeneous leading layer. No lower layer is changed. -/
theorem sourceNilpotent_longitudinal_third_eq_zero
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) L)) = 0 := by
  classical
  let P := pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) L))
  have h := (sourceNilpotent_transverseGradient_second_third a N hN L n hL hgrad).2
  have hz (i : Fin 3) : pderiv (.inr i) P = 0 := by
    dsimp only [P]
    simp only [HC4.Newton.pderiv_comm_backport (Sum.inr i) (Sum.inl ())]
    exact h i
  have hp := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous
      (pderiv_isWeightedHomogeneous hL (Sum.inl ())) (Sum.inl ())) (Sum.inl ())
  have hp' : P.IsWeightedHomogeneous transverseCubicWeight ((n+1 : ℕ) : ℤ) := by
    simpa [P, transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight P (n+1) hp'
  simp only [hz, mul_zero, Finset.sum_const_zero] at he
  have hn : ((n+1 : ℕ) : StationarySource K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (mul_eq_zero.mp he.symm).resolve_left hn


end
end HC4.Polynomial.RankThreeCubic
