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
  rw [_root_.Polynomial.coeff_sub, transverse_coeff_mul_two,
    ha0, ha1, zero_mul, zero_mul, zero_add, zero_add,
    transverseSchurMixed_coeff_two H hb hp hq, hdet] at h
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
    rw [sourceTransverseSchurFrame_det F m hm hbound hdet φ u v w]
    simp [_root_.Polynomial.coeff_X_pow, Ne.symm (Nat.ne_of_lt hn)]
  have h := transverseSchur_coeff_recurrence H n
  rw [hd, zero_add] at h
  exact h

end
end HC4.Polynomial.RankThreeCubic
