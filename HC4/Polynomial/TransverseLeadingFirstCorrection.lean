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
    [CharZero K] {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
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
    [CharZero K] {E : Type*} [CommRing E] [IsDomain E] [CharZero E] [Algebra K E]
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
          A ^ 2 * A ^ 2 = A ^ 2 * (A * A) :=
            congrArg (fun M => A ^ 2 * M) (pow_two A)
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
    have hA2 : A ^ 2 = (N.transpose ^ 2).map
        (MvPolynomial.C : K →+* StationarySource K) := by
      simp only [A, pow_two, Matrix.map_mul]
    calc
      A ^ 3 = A ^ 2 * A := pow_succ A 2
      _ = ((N.transpose ^ 2) * N.transpose).map
          (MvPolynomial.C : K →+* StationarySource K) := by
        rw [hA2, Matrix.map_mul]
      _ = (N.transpose ^ 3).map
          (MvPolynomial.C : K →+* StationarySource K) :=
        congrArg (fun M : Matrix (Fin 3) (Fin 3) K =>
          M.map (MvPolynomial.C : K →+* StationarySource K)) (pow_succ N.transpose 2).symm
      _ = 0 := h
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




/-! ## Exact longitudinal support, with the nilpotence-index refinement

The derivative identities become literal exponent bounds in the
original source. In the square-zero case the explicit second
gradient derivative vanishes, so the leading layer is affine in x.
-/

/-- A nonzero coefficient of positive exponent survives one derivative
at its unique shifted exponent. Work over an abstract index type so
elaboration does not unfold the concrete sum-type Finsupp operations. -/
private theorem sourceCoeff_derivative_ne_zero
    {ι : Type*} (i : ι)
    (P : MvPolynomial ι K) (d : ι →₀ ℕ)
    (hd : MvPolynomial.coeff d P ≠ 0) (hp : 0 < d i) :
    MvPolynomial.coeff (d - Finsupp.single i 1) (pderiv i P) ≠ 0 := by
  classical
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  change MvPolynomial.coeff e (pderiv i P) ≠ 0
  rw [HC4.Newton.coeff_pderiv_backport, he]
  exact mul_ne_zero hd (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (e i)))

private theorem sourceSupport_secondDerivative_bound
    {ι : Type*} (i : ι) (P : MvPolynomial ι K)
    (hP : pderiv i (pderiv i P) = 0)
    (d : ι →₀ ℕ) (hd : MvPolynomial.coeff d P ≠ 0) :
    d i ≤ 1 := by
  classical
  by_contra hn
  have hp : 0 < d i := by omega
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hc : MvPolynomial.coeff e (pderiv i P) ≠ 0 :=
    sourceCoeff_derivative_ne_zero i P d hd hp
  have hz : e i = 0 :=
    HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero i (pderiv i P) hP e hc
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have heval := congrArg (fun z : ι →₀ ℕ => z i) he
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at heval
  omega

private theorem sourceSupport_thirdDerivative_bound
    {ι : Type*} (i : ι) (P : MvPolynomial ι K)
    (hP : pderiv i (pderiv i (pderiv i P)) = 0)
    (d : ι →₀ ℕ) (hd : MvPolynomial.coeff d P ≠ 0) :
    d i ≤ 2 := by
  classical
  by_contra hn
  have hp : 0 < d i := by omega
  let e : ι →₀ ℕ := d - Finsupp.single i 1
  have hc : MvPolynomial.coeff e (pderiv i P) ≠ 0 :=
    sourceCoeff_derivative_ne_zero i P d hd hp
  have hz : e i ≤ 1 := sourceSupport_secondDerivative_bound i (pderiv i P) hP e hc
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have heval := congrArg (fun z : ι →₀ ℕ => z i) he
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at heval
  omega

/-- Two vanishing longitudinal derivatives force each surviving
monomial of the original polynomial to have longitudinal exponent ≤1. -/
theorem sourceLongitudinal_support_le_one
    (P : StationarySource K)
    (hP : pderiv (.inl ()) (pderiv (.inl ()) P) = 0)
    (d : StationaryExponent) (hd : MvPolynomial.coeff d P ≠ 0) :
    d (.inl ()) ≤ 1 :=
  sourceSupport_secondDerivative_bound (Sum.inl ()) P hP d hd

/-- Three vanishing longitudinal derivatives force each surviving
monomial of the original polynomial to have longitudinal exponent ≤2. -/
theorem sourceLongitudinal_support_le_two
    (P : StationarySource K)
    (hP : pderiv (.inl ()) (pderiv (.inl ()) (pderiv (.inl ()) P)) = 0)
    (d : StationaryExponent) (hd : MvPolynomial.coeff d P ≠ 0) :
    d (.inl ()) ≤ 2 :=
  sourceSupport_thirdDerivative_bound (Sum.inl ()) P hP d hd

/-- Square-zero linear characteristics force the original homogeneous
leading potential to be longitudinally affine. -/
theorem sourceNilpotent_longitudinal_second_eq_zero_of_square_zero
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 2 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    pderiv (.inl ()) (pderiv (.inl ()) L) = 0 := by
  classical
  have h3 : N ^ 3 = 0 := by rw [pow_succ N 2, hN, zero_mul]
  let P := pderiv (.inl ()) (pderiv (.inl ()) L)
  let A : Matrix (Fin 3) (Fin 3) (StationarySource K) :=
    N.transpose.map MvPolynomial.C
  have h2N : N.transpose ^ 2 = 0 := by
    rw [← Matrix.transpose_pow, hN, Matrix.transpose_zero]
  have h2A : A ^ 2 = 0 := by
    have h : (N.transpose ^ 2).map (MvPolynomial.C : K →+* StationarySource K) =
        (0 : Matrix (Fin 3) (Fin 3) (StationarySource K)) := by
      rw [h2N]
      ext i j
      simp
    simpa only [A, pow_two, Matrix.map_mul] using h
  have hs := (sourceNilpotent_transverseGradient_second_third a N h3 L n hL hgrad).1
  dsimp only at hs
  have hs' :
      (fun i : Fin 3 => pderiv (Sum.inl ()) (pderiv (Sum.inl ())
        (pderiv (Sum.inr i) L))) =
      ((n : StationarySource K) * ((n : StationarySource K)+1)) •
        (A ^ 2 *ᵥ (fun i : Fin 3 => pderiv (Sum.inr i) L)) := hs
  rw [h2A, Matrix.zero_mulVec, smul_zero] at hs'
  have hz (i : Fin 3) : pderiv (.inr i) P = 0 := by
    dsimp only [P]
    simp only [HC4.Newton.pderiv_comm_backport (Sum.inr i) (Sum.inl ())]
    exact congrFun hs' i
  have hp := pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous hL (Sum.inl ())) (Sum.inl ())
  have hp' : P.IsWeightedHomogeneous transverseCubicWeight ((n+1 : ℕ) : ℤ) := by
    simpa [P, transverseCubicWeight] using hp
  have he := sourceTransverseEuler_of_weight P (n+1) hp'
  simp only [hz, mul_zero, Finset.sum_const_zero] at he
  have hn : ((n+1 : ℕ) : StationarySource K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (mul_eq_zero.mp he.symm).resolve_left hn

/-- A pole-free leading layer has total degree at most m+2, or m+1
when its characteristic matrix is square-zero. These are bounds on
the LEADING layer, not on the lower layers of the original source. -/
theorem sourceNilpotent_leading_totalDegree_support_bound
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K) (n : ℕ)
    (hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 1))
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L))) :
    IsWeightLE (stationaryEdgeWeight 1 1) ((n : ℤ)+3) L ∧
      (N ^ 2 = 0 → IsWeightLE (stationaryEdgeWeight 1 1) ((n : ℤ)+2) L) := by
  have hthird := sourceNilpotent_longitudinal_third_eq_zero a N hN L n hL hgrad
  constructor
  · intro d hd
    have hc := MvPolynomial.mem_support_iff.mp hd
    have hp := sourceLongitudinal_support_le_two L hthird d hc
    have hq := hL hc
    rw [stationaryEdge_weight_eq, one_mul, one_mul, hq]
    omega
  · intro h2 d hd
    have hsecond :=
      sourceNilpotent_longitudinal_second_eq_zero_of_square_zero a N h2 L n hL hgrad
    have hc := MvPolynomial.mem_support_iff.mp hd
    have hp := sourceLongitudinal_support_le_one L hsecond d hc
    have hq := hL hc
    rw [stationaryEdge_weight_eq, one_mul, one_mul, hq]
    omega




/-! ## First LOWER layer in a pole-free chart

The first correction identity works over the polynomial coefficient
domain itself. The inverse nilpotent shear therefore reconstructs
the actual lower layer from its two time coefficients, with no
denominators and no claim of nonlinear Hessian invariance.
-/

/-- Polynomial first correction transport: the actual adjacent
source layer has only two characteristic-time coefficients. -/
theorem sourceNilpotent_firstCorrection_affine
    (F : StationarySource K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight m F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight m F)))) :
    let P := linearLineEval a N (initialForm transverseCubicWeight (m-1) F)
    P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  have hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0 := hreg
  have hV : V (.inl ()) = 1 := rfl
  have hg : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight m F)) =
      _root_.Polynomial.C (MvPolynomial.aeval z
        (pderiv i (initialForm transverseCubicWeight m F))) := hgrad
  exact sourceLeading_firstCorrection_affine_along_line F m hm hcap hdet z V hz hV hg

/-- The honest polynomial inverse characteristic coordinates, regarded
as a substitution of the reference transverse polynomial ring. -/
def sourceNilpotentInverseEval
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial (Fin 3) K →ₐ[K] StationarySource K :=
  MvPolynomial.aeval fun i =>
    X (.inr i) -
      (X (.inl ()) - MvPolynomial.C a) * sourceLinearVector N i +
      (X (.inl ()) - MvPolynomial.C a) ^ 2 * sourceLinearVector (N ^ 2) i

private theorem sourceNilpotent_time_eval
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) :
    linearLineEval a N (X (.inl ()) - MvPolynomial.C a) =
      (_root_.Polynomial.X : _root_.Polynomial (MvPolynomial (Fin 3) K)) := by
  simp [linearLineEval, lineEval]

private theorem sourceNilpotentInverseEval_X_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) (i : Fin 3) :
    linearLineEval a N (sourceNilpotentInverseEval a N (X i)) =
      _root_.Polynomial.C (X i) := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hx : linearLineEval a N (X (.inr i)) =
      _root_.Polynomial.C (X i : B) +
        _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
    simp [linearLineEval, lineEval, referenceLinearVector]
  have h2 : N * N = N ^ 2 := (pow_two N).symm
  have h3 : N ^ 2 * N = 0 := by rw [← pow_succ, hN]
  have hz : referenceLinearVector (0 : Matrix (Fin 3) (Fin 3) K) i = 0 := by
    simp [referenceLinearVector]
  have hx0 : linearLineEval a N (X (Sum.inl ())) =
      _root_.Polynomial.C (MvPolynomial.C a : B) + _root_.Polynomial.X := by
    simp [linearLineEval, lineEval]
  have hc : linearLineEval a N (MvPolynomial.C a) =
      _root_.Polynomial.C (MvPolynomial.C a : B) := by
    simp [linearLineEval, lineEval]
  simp only [sourceNilpotentInverseEval, MvPolynomial.aeval_X, map_add, map_sub,
    map_mul, map_pow, hx, hx0, hc,
    linearLineEval_sourceLinearVector, h2, h3, hz, map_zero, zero_mul, add_zero]
  ring

/-- Composing inverse coordinates with forward line evaluation
recovers the reference polynomial as a constant time polynomial. -/
theorem sourceNilpotentInverseEval_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (P : MvPolynomial (Fin 3) K) :
    linearLineEval a N (sourceNilpotentInverseEval a N P) = _root_.Polynomial.C P := by
  classical
  let B := MvPolynomial (Fin 3) K
  have hcomp : (linearLineEval a N).toRingHom.comp
      (sourceNilpotentInverseEval a N).toRingHom =
      (_root_.Polynomial.C : B →+* _root_.Polynomial B) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change linearLineEval a N (sourceNilpotentInverseEval a N (MvPolynomial.C c)) =
        _root_.Polynomial.C (MvPolynomial.C c)
      simp [sourceNilpotentInverseEval, linearLineEval, lineEval,
        IsScalarTower.algebraMap_apply K B (_root_.Polynomial B),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      exact sourceNilpotentInverseEval_X_transport a N hN i
  exact RingHom.congr_fun hcomp P

/-- Reconstruct any affine-in-time source polynomial from its first
two time coefficients using the nilpotent polynomial inverse. -/
theorem sourceNilpotent_affine_inverseFormula
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K)
    (hQ : let P := linearLineEval a N Q
      P = _root_.Polynomial.C (P.coeff 0) +
        _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X) :
    let P := linearLineEval a N Q
    Q = sourceNilpotentInverseEval a N (P.coeff 0) +
      sourceNilpotentInverseEval a N (P.coeff 1) *
        (X (.inl ()) - MvPolynomial.C a) := by
  apply linearLineEval_injective_of_cube_zero a N hN
  rw [map_add, map_mul, sourceNilpotentInverseEval_transport a N hN,
    sourceNilpotentInverseEval_transport a N hN, sourceNilpotent_time_eval]
  exact hQ

/-- Exact original-source reconstruction of the first lower grade.
This connects leading rigidity to the actual lower source support. -/
theorem sourceNilpotent_firstCorrection_inverseFormula
    (F : StationarySource K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight m F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight m F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight m F)))) :
    let Q := initialForm transverseCubicWeight (m-1) F
    let P := linearLineEval a N Q
    Q = sourceNilpotentInverseEval a N (P.coeff 0) +
      sourceNilpotentInverseEval a N (P.coeff 1) *
        (X (.inl ()) - MvPolynomial.C a) :=
  sourceNilpotent_affine_inverseFormula a N hN _ 
    (sourceNilpotent_firstCorrection_affine F m hm hcap hdet a N hreg hgrad)




/-! ## Actual second lower layer on the characteristic

The two parameters remain distinct: s is the reverse transverse Rees
parameter and t is time on the characteristic. The determinant clock
is in s, while every coefficient is a polynomial in t.
-/

private def sourceLineIndex : Fin 4 ≃ Unit ⊕ Fin 3 where
  toFun := ![Sum.inl (), Sum.inr 0, Sum.inr 1, Sum.inr 2]
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro i
    cases i with
    | inl u => cases u; rfl
    | inr j => fin_cases j <;> rfl

private def sourceLineBlockOfMatrix {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R) : GeneralFourBlock R :=
  GeneralFourBlock.ofSymmetricMatrix (M.submatrix sourceLineIndex sourceLineIndex)

private theorem sourceLineBlockOfMatrix_det {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (hsym : ∀ i j, M i j = M j i) :
    (sourceLineBlockOfMatrix M).determinantCore = M.det := by
  rw [← GeneralFourBlock.matrix_det]
  unfold sourceLineBlockOfMatrix
  rw [GeneralFourBlock.matrix_ofSymmetricMatrix]
  · exact Matrix.det_submatrix_equiv_self sourceLineIndex M
  · intro i j
    exact hsym _ _

/-- Coefficientwise projection of the actual ten entries; this is not
a ring homomorphism on the determinant. -/
def transverseBlockCoeff {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) (j : ℕ) :
    GeneralFourBlock R where
  a := H.a.coeff j
  b := H.b.coeff j
  d := H.d.coeff j
  p := H.p.coeff j
  q := H.q.coeff j
  r := H.r.coeff j
  s := H.s.coeff j
  x := H.x.coeff j
  y := H.y.coeff j
  z := H.z.coeff j

/-- A constant-in-Rees-time characteristic frame commutes with taking
individual Rees coefficients. The entries may depend on line time. -/
theorem transverseCharacteristicFrame_coeff {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) (u v w : R) (j : ℕ) :
    transverseBlockCoeff (transverseCharacteristicFrame H
      (_root_.Polynomial.C u) (_root_.Polynomial.C v) (_root_.Polynomial.C w)) j =
      transverseCharacteristicFrame (transverseBlockCoeff H j) u v w := by
  apply GeneralFourBlock.ext <;>
    simp only [transverseBlockCoeff, transverseCharacteristicFrame,
      two_mul, add_mul, pow_two, ← _root_.Polynomial.C_mul,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul]

/-- The actual unframed reverse Hessian, evaluated along an affine
characteristic. Its coefficients lie in the line-time polynomial ring. -/
def sourceLeading_lineBlock
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    GeneralFourBlock (_root_.Polynomial (_root_.Polynomial E)) :=
  sourceLineBlockOfMatrix
    ((_root_.Polynomial.mapRingHom (lineEval z V).toRingHom).mapMatrix
      (sourceLeading_reverseHessian F m))

theorem sourceLeading_lineBlock_det
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    (sourceLeading_lineBlock F m z V).determinantCore =
      _root_.Polynomial.monomial (4*m-6)
        (lineEval z V (MvPolynomial.C δ)) := by
  let φ : _root_.Polynomial (StationarySource K) →+*
      _root_.Polynomial (_root_.Polynomial E) :=
    _root_.Polynomial.mapRingHom (lineEval (K := K) z V).toRingHom
  have hsym (i j : Unit ⊕ Fin 3) :
      sourceLeading_reverseHessian F m i j =
        sourceLeading_reverseHessian F m j i := by
    apply _root_.Polynomial.ext
    intro k
    rw [sourceLeading_reverseHessian_coeff, sourceLeading_reverseHessian_coeff]
    split_ifs
    · simp only [hessian_apply, HC4.Newton.pderiv_comm_backport j i]
    · rfl
  change (sourceLineBlockOfMatrix (φ.mapMatrix
    (sourceLeading_reverseHessian F m))).determinantCore = _
  rw [sourceLineBlockOfMatrix_det, ← RingHom.map_det,
    sourceLeading_reverseHessian_constantDet F m hm hcap hdet]
  · exact _root_.Polynomial.map_monomial (lineEval (K := K) z V).toRingHom
  · intro i j
    change φ (sourceLeading_reverseHessian F m i j) =
      φ (sourceLeading_reverseHessian F m j i)
    rw [hsym]

/-- The coefficient at j is literally the evaluated Hessian of the
jth lower source layer. No new potential is introduced. -/
theorem sourceLeading_lineBlock_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) :
    transverseBlockCoeff (sourceLeading_lineBlock F m z V) j =
      sourceLineBlockOfMatrix ((lineEval z V).toRingHom.mapMatrix
        (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F))) := by
  apply GeneralFourBlock.ext <;>
    simp only [transverseBlockCoeff, sourceLeading_lineBlock, sourceLineBlockOfMatrix,
      GeneralFourBlock.ofSymmetricMatrix, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, _root_.Polynomial.coe_mapRingHom, _root_.Polynomial.coeff_map,
      sourceLeading_reverseHessian_coeff, if_pos hj]

/-- The actual reverse Hessian in the normalized characteristic frame,
constant in s but not assumed constant in t. -/
def sourceLeading_lineSchurFrame
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    GeneralFourBlock (_root_.Polynomial (_root_.Polynomial E)) :=
  transverseCharacteristicFrame (sourceLeading_lineBlock F m z V)
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 0))))
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 1))))
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 2))))

theorem sourceLeading_lineSchurFrame_det
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    (sourceLeading_lineSchurFrame F m z V).determinantCore =
      _root_.Polynomial.monomial (4*m-6) (lineEval z V (MvPolynomial.C δ)) := by
  unfold sourceLeading_lineSchurFrame
  rw [transverseCharacteristicFrame_det, sourceLeading_lineBlock_det F m hm hcap hdet]

theorem sourceLeading_lineSchurFrame_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) :
    transverseBlockCoeff (sourceLeading_lineSchurFrame F m z V) j =
      transverseCharacteristicFrame
        (sourceLineBlockOfMatrix ((lineEval z V).toRingHom.mapMatrix
          (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F))))
        (_root_.Polynomial.C (V (.inr 0)))
        (_root_.Polynomial.C (V (.inr 1)))
        (_root_.Polynomial.C (V (.inr 2))) := by
  unfold sourceLeading_lineSchurFrame
  rw [transverseCharacteristicFrame_coeff, sourceLeading_lineBlock_coeff F m j hj]

/-- Exact second constraint in the actual line-time coefficient ring.
The kernel-frame hypotheses will be extracted from gradient transport
and the regular transverse anchor, not supplied as source assumptions. -/
theorem sourceLeading_lineSchurFrame_second_constraint
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    let H := sourceLeading_lineSchurFrame F m z V
    H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 →
    H.a.coeff 2 * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := H.a.coeff 2, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock (_root_.Polynomial E)) := by
  let H := sourceLeading_lineSchurFrame F m z V
  change H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 → _
  intro hb hp hq hregular
  have hd := sourceLeading_lineSchurFrame_det F m (by omega) hcap hdet z V
  have hz (j : ℕ) (hj : j < 4*m-6) : H.determinantCore.coeff j = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff j = 0
    rw [hd, _root_.Polynomial.coeff_monomial, if_neg (Ne.symm (Nat.ne_of_lt hj))]
  obtain ⟨ha0, ha1⟩ := transverseSchur_longitudinal_zero_one
    H hb hp hq hregular (hz 0 (by omega)) (hz 1 (by omega))
  exact transverseSchur_second_constraint H ha0 ha1 hb hp hq (hz 2 (by omega))




/-! ## Differential meaning of the actual characteristic frame -/

private theorem sourceLineFrame_a_eq_sum {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (W : Unit ⊕ Fin 3 → R) (hW : W (.inl ()) = 1)
    (hsym : ∀ i j, M i j = M j i) :
    (transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      (W (.inr 0)) (W (.inr 1)) (W (.inr 2))).a =
      ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3, W i * M i j * W j := by
  classical
  have h01 := hsym (.inr 0) (.inl ())
  have h02 := hsym (.inr 1) (.inl ())
  have h03 := hsym (.inr 2) (.inl ())
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  simp [transverseCharacteristicFrame, sourceLineBlockOfMatrix,
    GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
    Fintype.sum_sum_type, Fin.sum_univ_three, hW, h01, h02, h03, h12, h13, h23]
  <;> ring

private theorem sourceLineFrame_mixed_eq_sums {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (W : Unit ⊕ Fin 3 → R) (hW : W (.inl ()) = 1)
    (hsym : ∀ i j, M i j = M j i) :
    let H := transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      (W (.inr 0)) (W (.inr 1)) (W (.inr 2))
    H.b = (∑ j, W j * M (.inr 0) j) ∧
    H.p = (∑ j, W j * M (.inr 1) j) ∧
    H.q = (∑ j, W j * M (.inr 2) j) := by
  classical
  have h01 := hsym (.inr 0) (.inl ())
  have h02 := hsym (.inr 1) (.inl ())
  have h03 := hsym (.inr 2) (.inl ())
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [transverseCharacteristicFrame, sourceLineBlockOfMatrix,
      GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, hW, h01, h02, h03, h12, h13, h23]
    <;> ring

private theorem sourceLineFrame_transverseDet_eq {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (u v w : R) (hsym : ∀ i j, M i j = M j i) :
    transverseSchurDet (transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      u v w) = (M.submatrix Sum.inr Sum.inr).det := by
  rw [Matrix.det_fin_three]
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  simp [transverseSchurDet, transverseCharacteristicFrame, sourceLineBlockOfMatrix,
    GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
    h12, h13, h23] <;> ring

private theorem transverseSchurDet_coeff_zero {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) :
    (transverseSchurDet H).coeff 0 = transverseSchurDet (transverseBlockCoeff H 0) := by
  simp only [transverseSchurDet, transverseBlockCoeff,
    _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_sub,
    _root_.Polynomial.mul_coeff_zero]

/-- The second line derivative is the actual source Hessian quadratic
form along the original affine characteristic. -/
theorem sourceLine_secondDerivative_eq_hessian
    {E : Type*} [CommRing E] [Algebra K E]
    (z V : Unit ⊕ Fin 3 → E) (Q : StationarySource K) :
    (lineEval z V Q).derivative.derivative =
      ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3,
        _root_.Polynomial.C (V i) * lineEval z V (hessian Q i j) *
          _root_.Polynomial.C (V j) := by
  classical
  rw [transverse_lineEval_derivative]
  simp only [_root_.Polynomial.derivative_sum, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_C, zero_mul, zero_add]
  simp_rw [transverse_lineEval_derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _root_.Polynomial.C (V i) *
    (_root_.Polynomial.C (V j) * lineEval z V (pderiv j (pderiv i Q))) = _
  rw [hessian_apply]
  ring

/-- At every actual layer, the longitudinal coefficient of the framed
Hessian is precisely the second derivative of that layer in time;
the mixed entries are the first time derivatives of its transverse
gradient. This does not differentiate a nonconstant frame. -/
theorem sourceLeading_lineSchurFrame_differential_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1) :
    let H := sourceLeading_lineSchurFrame F m z V
    let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
    H.a.coeff j = (lineEval z V Q).derivative.derivative ∧
    H.b.coeff j = (lineEval z V (pderiv (.inr 0) Q)).derivative ∧
    H.p.coeff j = (lineEval z V (pderiv (.inr 1) Q)).derivative ∧
    H.q.coeff j = (lineEval z V (pderiv (.inr 2) Q)).derivative := by
  classical
  let H := sourceLeading_lineSchurFrame F m z V
  let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
  let M := (lineEval z V).toRingHom.mapMatrix (hessian Q)
  let W : Unit ⊕ Fin 3 → _root_.Polynomial E :=
    fun i => _root_.Polynomial.C (V i)
  have hW : W (.inl ()) = 1 := by simp [W, hV]
  have hsym (i k : Unit ⊕ Fin 3) : M i k = M k i := by
    change lineEval z V (pderiv k (pderiv i Q)) =
      lineEval z V (pderiv i (pderiv k Q))
    rw [HC4.Newton.pderiv_comm_backport k i]
  have hfr : transverseBlockCoeff H j =
      transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
        (W (.inr 0)) (W (.inr 1)) (W (.inr 2)) :=
    sourceLeading_lineSchurFrame_coeff F m j hj z V
  have ha := sourceLineFrame_a_eq_sum M W hW hsym
  obtain ⟨hb, hp, hq⟩ := sourceLineFrame_mixed_eq_sums M W hW hsym
  change (transverseBlockCoeff H j).a = _ ∧
    (transverseBlockCoeff H j).b = _ ∧
    (transverseBlockCoeff H j).p = _ ∧
    (transverseBlockCoeff H j).q = _
  rw [hfr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha, sourceLine_secondDerivative_eq_hessian]
    rfl
  · rw [hb, transverse_lineEval_derivative]
    rfl
  · rw [hp, transverse_lineEval_derivative]
    rfl
  · rw [hq, transverse_lineEval_derivative]
    rfl

/-- The leading transverse determinant in the framed series is the
actual transverse Hessian determinant transported along the line. -/
theorem sourceLeading_lineSchurFrame_transverseDet_zero
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 =
      lineEval z V ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det := by
  classical
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let M := (lineEval z V).toRingHom.mapMatrix (hessian L)
  have hsym (i k : Unit ⊕ Fin 3) : M i k = M k i := by
    change lineEval z V (pderiv k (pderiv i L)) =
      lineEval z V (pderiv i (pderiv k L))
    rw [HC4.Newton.pderiv_comm_backport k i]
  rw [transverseSchurDet_coeff_zero,
    sourceLeading_lineSchurFrame_coeff F m 0 (Nat.zero_le m) z V]
  simp only [Nat.cast_zero, sub_zero]
  rw [sourceLineFrame_transverseDet_eq _ _ _ _ hsym]
  change ((lineEval z V).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)).det = _
  rw [← RingHom.map_det]
  rfl

/-- The leading frame conditions follow from the existing gradient
transport and regular reference anchor, at all transverse degrees. -/
theorem sourceLeading_lineSchurFrame_kernel_regular
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E)
    (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    let H := sourceLeading_lineSchurFrame F m z V
    H.b.coeff 0 = 0 ∧ H.p.coeff 0 = 0 ∧ H.q.coeff 0 = 0 ∧
      (transverseSchurDet H).coeff 0 ≠ 0 := by
  have hd := sourceLeading_lineSchurFrame_differential_coeff F m 0 (Nat.zero_le m) z V hV
  simp only [Nat.cast_zero, sub_zero] at hd
  obtain ⟨_, hb, hp, hq⟩ := hd
  rw [hgrad (.inr 0), _root_.Polynomial.derivative_C] at hb
  rw [hgrad (.inr 1), _root_.Polynomial.derivative_C] at hp
  rw [hgrad (.inr 2), _root_.Polynomial.derivative_C] at hq
  refine ⟨hb, hp, hq, ?_⟩
  rw [sourceLeading_lineSchurFrame_transverseDet_zero]
  intro h
  have hc := congrArg (fun p : _root_.Polynomial E => p.coeff 0) h
  change (lineEval z V ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
    Sum.inr Sum.inr).det).coeff 0 = (0 : _root_.Polynomial E).coeff 0 at hc
  rw [cubic_lineEval_coeff_zero, _root_.Polynomial.coeff_zero] at hc
  exact hz hc

/-- Source-honest second-order constraint, with all frame hypotheses
discharged. The left side is the second time derivative of the
actual second lower layer, not an independent unknown. -/
theorem sourceLeading_secondCorrection_lineODE
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    let H := sourceLeading_lineSchurFrame F m z V
    let Q := initialForm transverseCubicWeight ((m : ℤ)-2) F
    (lineEval z V Q).derivative.derivative * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := 0, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock (_root_.Polynomial E)) := by
  obtain ⟨hb, hp, hq, hr⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hgrad
  have h := sourceLeading_lineSchurFrame_second_constraint F m hm hcap hdet z V hb hp hq hr
  have ha := (sourceLeading_lineSchurFrame_differential_coeff F m 2 (by omega) z V hV).1
  dsimp only at h ha ⊢
  rw [ha] at h
  simpa only [transverseSchurMixed] using h




/-! ## Time degree estimates in the nilpotent chart

These bounds are on actual polynomials in characteristic time. In
particular they do not assert that a nonlinear shear preserves the
Hessian determinant of the original source.
-/

private abbrev LineTime (K : Type*) [Field K] :=
  _root_.Polynomial (MvPolynomial (Fin 3) K)

private def sourceTimeMatrix (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  (N.map MvPolynomial.C).map _root_.Polynomial.C

private theorem sourceTimeMatrix_mul
    (N M : Matrix (Fin 3) (Fin 3) K) :
    sourceTimeMatrix (N * M) = sourceTimeMatrix N * sourceTimeMatrix M := by
  simp only [sourceTimeMatrix, Matrix.map_mul]

private theorem sourceTimeMatrix_zero :
    sourceTimeMatrix (0 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  simp [sourceTimeMatrix, Matrix.map_apply]

private theorem sourceTimeMatrix_cube
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) :
    sourceTimeMatrix N ^ 3 = 0 := by
  have h : sourceTimeMatrix (N ^ 3) = 0 := by rw [hN, sourceTimeMatrix_zero]
  have he : sourceTimeMatrix (N ^ 3) = sourceTimeMatrix N ^ 3 := by
    rw [pow_succ N 2, pow_succ (sourceTimeMatrix N) 2, sourceTimeMatrix_mul,
      pow_two N, pow_two (sourceTimeMatrix N), sourceTimeMatrix_mul]
  exact he.symm.trans h

private theorem sourceTimeMatrix_square
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 2 = 0) :
    sourceTimeMatrix N ^ 2 = 0 := by
  have h : sourceTimeMatrix (N ^ 2) = 0 := by rw [hN, sourceTimeMatrix_zero]
  simpa only [pow_two, sourceTimeMatrix_mul] using h

private def sourceTimePencil (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  1 + (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N

private def sourceTimePencilInv (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  1 - (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N +
    (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2)

private theorem sourceTimePencil_right_inverse
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) :
    sourceTimePencil N * sourceTimePencilInv N = 1 := by
  let A := (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N
  have h3 : A ^ 3 = 0 := by
    dsimp only [A]
    rw [smul_pow, sourceTimeMatrix_cube N hN, smul_zero]
  have h2 : A ^ 2 =
      (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2) := by
    dsimp only [A]
    rw [smul_pow, pow_two N, sourceTimeMatrix_mul, pow_two (sourceTimeMatrix N)]
  unfold sourceTimePencil sourceTimePencilInv
  change (1 + A) * (1 - A +
    (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2)) = 1
  rw [← h2]
  calc
    _ = 1 + A ^ 3 := by
      simp only [add_mul, one_mul, mul_add, mul_sub, mul_one,
        pow_succ' A 2, pow_two A]
      abel
    _ = 1 := by rw [h3, add_zero]

/-- Transverse differentiation in the reference variables: the
actual source gradient times the affine pencil is the gradient of
the pulled-back polynomial. No gradient constancy is needed here. -/
theorem sourceLinear_referenceGradient_chain
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (Q : StationarySource K) :
    (fun i : Fin 3 => linearLineEval a N (pderiv (.inr i) Q)) ᵥ*
      sourceTimePencil N =
      fun j : Fin 3 => coeffDeriv (pderiv j) (linearLineEval a N Q) := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let v : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let w : Unit ⊕ Fin 3 → _root_.Polynomial B := fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (v i) * _root_.Polynomial.X
  have hE : linearLineEval a N = MvPolynomial.aeval w := rfl
  have hz (j k : Fin 3) : pderiv j (z (.inr k)) = if k = j then 1 else 0 := by
    by_cases h : k = j
    · subst k; simp [z]
    · simp [z, h, pderiv_X_of_ne h]
  have hv (j k : Fin 3) : pderiv j (v (.inr k)) = MvPolynomial.C (N k j) := by
    simp only [v, Sum.elim_inr, referenceLinearVector, map_sum, MvPolynomial.pderiv_C_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [pderiv_X_of_ne hi, mul_zero]
    · simp
  have hC (j : Fin 3) (b : B) :
      coeffDeriv (pderiv j : Derivation K B B) (_root_.Polynomial.C b) =
        _root_.Polynomial.C (pderiv j b) :=
    coeffDeriv_C (pderiv j : Derivation K B B) b
  have hc (j : Fin 3) : coeffDeriv (pderiv j : Derivation K B B) (w (.inl ())) = 0 := by
    simp [w, z, v]
    calc
      _ = _root_.Polynomial.C (pderiv j (MvPolynomial.C a : B)) :=
        hC j (MvPolynomial.C a)
      _ = 0 := by simp
  have ht (j k : Fin 3) :
      coeffDeriv (pderiv j : Derivation K B B) (w (.inr k)) =
        sourceTimePencil N k j := by
    change coeffDeriv (pderiv j : Derivation K B B)
      (_root_.Polynomial.C (z (.inr k)) +
      _root_.Polynomial.C (v (.inr k)) * _root_.Polynomial.X) = _
    simp only [map_add, Derivation.leibniz, smul_eq_mul, coeffDeriv_X,
      mul_zero, zero_add, sourceTimePencil, sourceTimeMatrix,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply]
    calc
      _ = _root_.Polynomial.C (pderiv j (z (.inr k))) +
          _root_.Polynomial.X * _root_.Polynomial.C (pderiv j (v (.inr k))) :=
        congrArg₂ (fun x y : _root_.Polynomial B => x + _root_.Polynomial.X * y)
          (hC j (z (.inr k))) (hC j (v (.inr k)))
      _ = _ := by
        rw [hz j k, hv j k]
        split_ifs <;> simp <;> exact mul_comm _ _
  funext j
  change (∑ i : Fin 3, linearLineEval a N (pderiv (.inr i) Q) *
    sourceTimePencil N i j) = coeffDeriv (pderiv j) (linearLineEval a N Q)
  rw [hE, derivation_aeval]
  simp only [Fintype.sum_sum_type, hc, mul_zero, Finset.sum_const_zero, zero_add, ht]

private theorem sourceTime_coeffDeriv_natDegree_le
    (D : Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K))
    (P : LineTime K) :
    (coeffDeriv D P).natDegree ≤ P.natDegree := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_coeffDeriv, _root_.Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero]

private theorem sourceTime_natDegree_sum_le
    {R I : Type*} [CommRing R] (s : Finset I) (f : I → _root_.Polynomial R)
    (d : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d) :
    (∑ i ∈ s, f i).natDegree ≤ d := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [_root_.Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact _root_.Polynomial.coeff_eq_zero_of_natDegree_lt ((h i hi).trans_lt hk)

private theorem sourceTimePencilInv_natDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (sourceTimePencilInv N i j).natDegree ≤ 2 := by
  have h1 : (1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j =
      if i = j then 1 else 0 := by rw [Matrix.one_apply]
  have hd : ((1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j).natDegree ≤ 0 := by
    rw [h1]
    split_ifs <;> simp
  have hlin : ((_root_.Polynomial.X : LineTime K) *
      sourceTimeMatrix N i j).natDegree ≤ 1 := by
    change (_root_.Polynomial.X * _root_.Polynomial.C (MvPolynomial.C (N i j))).natDegree ≤ 1
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  have hquad : (((_root_.Polynomial.X : LineTime K)^2) *
      sourceTimeMatrix (N^2) i j).natDegree ≤ 2 := by
    change (_root_.Polynomial.X ^ 2 *
      _root_.Polynomial.C (MvPolynomial.C ((N^2) i j))).natDegree ≤ 2
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  simp only [sourceTimePencilInv, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le
    ((_root_.Polynomial.natDegree_sub_le _ _).trans (max_le (hd.trans (by omega))
      (hlin.trans (by omega)))) hquad

/-- Each actual transverse partial derivative costs at most two
characteristic-time degrees, uniformly in the transverse layer.
This is the cube-zero estimate needed for the degree induction. -/
theorem sourceNilpotent_transverseGradient_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i : Fin 3) :
    (linearLineEval a N (pderiv (.inr i) Q)).natDegree ≤
      (linearLineEval a N Q).natDegree + 2 := by
  classical
  let G : Fin 3 → LineTime K := fun j => linearLineEval a N (pderiv (.inr j) Q)
  let D : Fin 3 → LineTime K := fun j => coeffDeriv (pderiv j) (linearLineEval a N Q)
  have h : G ᵥ* sourceTimePencil N = D := sourceLinear_referenceGradient_chain a N Q
  have he : G = D ᵥ* sourceTimePencilInv N := by
    calc
      G = G ᵥ* (1 : Matrix (Fin 3) (Fin 3) (LineTime K)) :=
        (Matrix.vecMul_one G).symm
      _ = G ᵥ* (sourceTimePencil N * sourceTimePencilInv N) := by
        rw [sourceTimePencil_right_inverse N hN]
      _ = (G ᵥ* sourceTimePencil N) ᵥ* sourceTimePencilInv N :=
        (Matrix.vecMul_vecMul G _ _).symm
      _ = _ := by rw [h]
  change (G i).natDegree ≤ _
  rw [he]
  change (∑ j : Fin 3, D j * sourceTimePencilInv N j i).natDegree ≤ _
  apply sourceTime_natDegree_sum_le
  intro j _
  exact _root_.Polynomial.natDegree_mul_le_of_le
    (sourceTime_coeffDeriv_natDegree_le (pderiv j) (linearLineEval a N Q))
    (sourceTimePencilInv_natDegree_le N j i)

/-- Two actual transverse derivatives cost at most four time degrees.
The estimate applies to every lower source layer. -/
theorem sourceNilpotent_transverseHessian_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i j : Fin 3) :
    (linearLineEval a N (hessian Q (.inr i) (.inr j))).natDegree ≤
      (linearLineEval a N Q).natDegree + 4 := by
  change (linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) Q))).natDegree ≤ _
  have h1 := sourceNilpotent_transverseGradient_timeDegree_le a N hN Q i
  have h2 := sourceNilpotent_transverseGradient_timeDegree_le a N hN (pderiv (.inr i) Q) j
  omega

/-- A first mixed characteristic derivative costs at most one time
degree in the cube-zero chart (including the constant case). -/
theorem sourceNilpotent_mixed_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i : Fin 3) :
    (linearLineEval a N (pderiv (.inr i) Q)).derivative.natDegree ≤
      (linearLineEval a N Q).natDegree + 1 := by
  have h1 := sourceNilpotent_transverseGradient_timeDegree_le a N hN Q i
  have h2 := _root_.Polynomial.natDegree_derivative_le
    (linearLineEval a N (pderiv (.inr i) Q))
  omega




/-! ## Leading transverse adjugate and a quantitative second correction -/

private theorem sourceTimePencil_natDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (sourceTimePencil N i j).natDegree ≤ 1 := by
  have hd : ((1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j).natDegree ≤ 0 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hlin : ((_root_.Polynomial.X : LineTime K) *
      sourceTimeMatrix N i j).natDegree ≤ 1 := by
    change (_root_.Polynomial.X * _root_.Polynomial.C (MvPolynomial.C (N i j))).natDegree ≤ 1
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  simp only [sourceTimePencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le (hd.trans (by omega)) hlin

/-- The leading transverse adjugate is affine in characteristic time,
even when the leading transverse Hessian itself is quadratic in time.
The determinant is the original nonzero reference determinant. -/
theorem sourceLinear_leadingAdjugate_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (L : StationarySource K)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let T := (linearLineEval a N).toRingHom.mapMatrix H
    let M := (referenceSlice a).toRingHom.mapMatrix H
    T.det = _root_.Polynomial.C (referenceSlice a H.det) ∧
      T.adjugate = sourceTimePencil N * M.adjugate.map _root_.Polynomial.C := by
  classical
  let B := MvPolynomial (Fin 3) K
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  let J := sourceTimePencil N
  have h : T * J = M.map _root_.Polynomial.C :=
    transverseHessian_transport_of_linear_gradient a N L hgrad
  let J0 : Matrix (Fin 3) (Fin 3) (_root_.Polynomial K) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial K) • N.map _root_.Polynomial.C
  have hJ0 : J0.det = 1 := det_linearCharacteristic_eq_one a N L hreg hgrad
  let f := _root_.Polynomial.mapRingHom (MvPolynomial.C : K →+* B)
  have hmap : f.mapMatrix J0 = J := by
    ext i j
    by_cases hij : i = j <;>
      simp [f, J0, J, sourceTimePencil, sourceTimeMatrix, hij, Matrix.smul_apply,
        smul_eq_mul, RingHom.mapMatrix_apply, _root_.Polynomial.map_add, _root_.Polynomial.map_mul]
  have hJ : J.det = 1 := by
    rw [← hmap, ← RingHom.map_det, hJ0, map_one]
  have hdet : T.det = _root_.Polynomial.C (referenceSlice a H.det) := by
    have hh := congrArg Matrix.det h
    change (T * J).det = (M.map _root_.Polynomial.C).det at hh
    rw [Matrix.det_mul, hJ, mul_one] at hh
    calc
      _ = (M.map _root_.Polynomial.C).det := hh
      _ = _ := (_root_.Polynomial.C.map_det M).symm.trans
        (congrArg _root_.Polynomial.C ((referenceSlice a).map_det H).symm)
  have hadj : (M.map _root_.Polynomial.C).adjugate = J.adjugate * T.adjugate := by
    rw [← h, Matrix.adjugate_mul_distrib]
  have hC : (M.map _root_.Polynomial.C).adjugate =
      M.adjugate.map _root_.Polynomial.C :=
    (_root_.Polynomial.C.map_adjugate M).symm
  refine ⟨hdet, ?_⟩
  calc
    T.adjugate = (J * J.adjugate) * T.adjugate := by
      rw [Matrix.mul_adjugate, hJ, one_smul, one_mul]
    _ = J * (J.adjugate * T.adjugate) := mul_assoc _ _ _
    _ = J * M.adjugate.map _root_.Polynomial.C := by rw [← hadj, hC]

theorem sourceLinear_leadingAdjugate_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (L : StationarySource K)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (i j : Fin 3) :
    (((linearLineEval a N).toRingHom.mapMatrix
      ((hessian L).submatrix Sum.inr Sum.inr)).adjugate i j).natDegree ≤ 1 := by
  classical
  rw [(sourceLinear_leadingAdjugate_transport a N L hreg hgrad).2]
  rw [Matrix.mul_apply]
  apply sourceTime_natDegree_sum_le
  intro k _
  change (sourceTimePencil N i k *
    _root_.Polynomial.C (((referenceSlice a).toRingHom.mapMatrix
      ((hessian L).submatrix Sum.inr Sum.inr)).adjugate k j)).natDegree ≤ 1
  exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans
    (sourceTimePencil_natDegree_le N i k)

/-- Express the scalar mixed Schur correction as the quadratic pairing
with the adjugate of the actual transverse matrix. -/
private theorem sourceLineFrame_mixed_adjugate {R : Type*} [CommRing R]
    (H : GeneralFourBlock R) (T : Matrix (Fin 3) (Fin 3) R)
    (hd : H.d = T 0 0) (hr : H.r = T 0 1) (hs : H.s = T 0 2)
    (hx : H.x = T 1 1) (hy : H.y = T 1 2) (hz : H.z = T 2 2)
    (hSym : ∀ i j, T i j = T j i) :
    transverseSchurMixed H =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![H.b, H.p, H.q] : Fin 3 → R) i * T.adjugate i j *
          (![H.b, H.p, H.q] : Fin 3 → R) j := by
  classical
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  rw [Matrix.adjugate_fin_three]
  simp [transverseSchurMixed, hd, hr, hs, hx, hy, hz,
    Fin.sum_univ_three, h10, h20, h21] <;> ring

private theorem sourceTime_degree_of_secondDerivative_le
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : _root_.Polynomial R) (d : ℕ)
    (h : P.derivative.derivative.natDegree ≤ d) :
    P.natDegree ≤ d + 2 := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hc : P.derivative.derivative.coeff (k-2) = 0 :=
    _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [_root_.Polynomial.coeff_derivative, _root_.Polynomial.coeff_derivative] at hc
  have he : k - 2 + 1 + 1 = k := by omega
  rw [he] at hc
  have h1 : ((k - 2 + 1 : ℕ) : R) ≠ 0 := by exact_mod_cast (by omega : k - 2 + 1 ≠ 0)
  have h2 : (k : R) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hc' : (P.coeff k * (k : R)) * ((k - 2 + 1 : ℕ) : R) = 0 := by
    have heR : ((k - 2 : ℕ) : R) + 1 + 1 = (k : R) := by
      exact_mod_cast he
    simpa only [Nat.cast_add, Nat.cast_one, heR] using hc
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right h1)).resolve_right h2

/-- Actual second lower layer degree bound, not merely a bound on
abstract Schur variables. The constant leading determinant cancels
without any localization. -/
theorem sourceNilpotent_secondCorrection_timeDegree_le_seven
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    (linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-2) F)).natDegree ≤ 7 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let Q := initialForm transverseCubicWeight ((m : ℤ)-1) F
  let P := linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-2) F)
  let H := sourceLeading_lineSchurFrame F m z V
  let T := (linearLineEval a N).toRingHom.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  have haff := sourceNilpotent_firstCorrection_affine F (m : ℤ) (by omega)
    hcap hdet a N hreg hgrad
  have hQ : (linearLineEval a N Q).natDegree ≤ 1 := by
    change (linearLineEval a N Q).natDegree ≤ 1
    have he : linearLineEval a N Q =
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 0) +
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 1) * _root_.Polynomial.X := haff
    calc
      _ = (_root_.Polynomial.C ((linearLineEval a N Q).coeff 0) +
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 1) * _root_.Polynomial.X).natDegree :=
        congrArg _root_.Polynomial.natDegree he
      _ ≤ 1 := _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
        ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hc := sourceLeading_lineSchurFrame_differential_coeff F m 1 (by omega) z V hV
  obtain ⟨_, hb, hp, hq⟩ := hc
  let W : Fin 3 → LineTime K := ![H.b.coeff 1, H.p.coeff 1, H.q.coeff 1]
  have hW (i : Fin 3) : (W i).natDegree ≤ 2 := by
    fin_cases i
    · change (H.b.coeff 1).natDegree ≤ 2
      change H.b.coeff 1 = (linearLineEval a N (pderiv (.inr 0) Q)).derivative at hb
      rw [hb]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 0).trans (by omega)
    · change (H.p.coeff 1).natDegree ≤ 2
      change H.p.coeff 1 = (linearLineEval a N (pderiv (.inr 1) Q)).derivative at hp
      rw [hp]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 1).trans (by omega)
    · change (H.q.coeff 1).natDegree ≤ 2
      change H.q.coeff 1 = (linearLineEval a N (pderiv (.inr 2) Q)).derivative at hq
      rw [hq]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 2).trans (by omega)
  have ht : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)) := fun i => hgrad (.inr i)
  have hAdj (i j : Fin 3) : (T.adjugate i j).natDegree ≤ 1 :=
    sourceLinear_leadingAdjugate_timeDegree_le a N L hreg ht i j
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, W i * T.adjugate i j * W j).natDegree ≤ 5 := by
    apply sourceTime_natDegree_sum_le
    intro i _
    apply sourceTime_natDegree_sum_le
    intro j _
    exact _root_.Polynomial.natDegree_mul_le_of_le
      (_root_.Polynomial.natDegree_mul_le_of_le (hW i) (hAdj i j)) (hW j)
  have hsym (i j : Fin 3) : T i j = T j i := by
    change linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) L)) =
      linearLineEval a N (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  let U : GeneralFourBlock (LineTime K) :=
    { a := 0, b := H.b.coeff 1, p := H.p.coeff 1, q := H.q.coeff 1,
      d := H.d.coeff 0, r := H.r.coeff 0, s := H.s.coeff 0,
      x := H.x.coeff 0, y := H.y.coeff 0, z := H.z.coeff 0 }
  have he := sourceLeading_lineSchurFrame_coeff F m 0 (Nat.zero_le m) z V
  simp only [Nat.cast_zero, sub_zero] at he
  have hu : transverseSchurMixed U = ∑ i : Fin 3, ∑ j : Fin 3,
      W i * T.adjugate i j * W j := by
    apply sourceLineFrame_mixed_adjugate U T <;> try exact hsym
    · exact congrArg GeneralFourBlock.d he
    · exact congrArg GeneralFourBlock.r he
    · exact congrArg GeneralFourBlock.s he
    · exact congrArg GeneralFourBlock.x he
    · exact congrArg GeneralFourBlock.y he
    · exact congrArg GeneralFourBlock.z he
  have hODE := sourceLeading_secondCorrection_lineODE F m hm hcap hdet z V hV hz hg
  change P.derivative.derivative * (transverseSchurDet H).coeff 0 =
    transverseSchurMixed U at hODE
  have hd : (transverseSchurDet H).coeff 0 =
      _root_.Polynomial.C (referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det) := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (linearLineEval a N).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
    exact (sourceLinear_leadingAdjugate_transport a N L hreg ht).1
  rw [hd, hu] at hODE
  have hdeg := congrArg _root_.Polynomial.natDegree hODE
  change (P.derivative.derivative * _root_.Polynomial.C
    (referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det)).natDegree = _ at hdeg
  rw [_root_.Polynomial.natDegree_mul_C hreg] at hdeg
  exact sourceTime_degree_of_secondDerivative_le P 5 (hdeg.trans_le hsum)




/-! ## Uniform cleared Schur degree induction

The degree profile distinguishes the zero Rees coefficient of the
transverse block from positive coefficients. Both mixed factors have
zero constant coefficient. These are essential, not optional, savings
in the convolution estimate.
-/

section TimeDegreeInduction

variable {R : Type*} [CommRing R]
local notation "TP" => _root_.Polynomial R
local notation "RP" => _root_.Polynomial TP

private theorem sourceTime_mul_coeff_degree_le
    (p q : RP) (n d : ℕ)
    (h : ∀ i j : ℕ, i+j=n → (p.coeff i * q.coeff j).natDegree ≤ d) :
    ((p*q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_mul]
  apply sourceTime_natDegree_sum_le
  intro ij hij
  exact h ij.1 ij.2 (Finset.mem_antidiagonal.mp hij)

private theorem sourceTime_add_coeff_degree_le
    {p q : RP} {n d : ℕ}
    (hp : (p.coeff n).natDegree ≤ d) (hq : (q.coeff n).natDegree ≤ d) :
    ((p+q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_add]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le hp hq

private theorem sourceTime_sub_coeff_degree_le
    {p q : RP} {n d : ℕ}
    (hp : (p.coeff n).natDegree ≤ d) (hq : (q.coeff n).natDegree ≤ d) :
    ((p-q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_sub]
  exact (_root_.Polynomial.natDegree_sub_le _ _).trans (max_le hp hq)

def timeTransverseProfile (k : ℕ) : ℕ :=
  if k = 0 then 2 else 9*k-4

private def timeMinorProfile (k : ℕ) : ℕ :=
  if k = 0 then 4 else 9*k-2

private def timeDetProfile (k : ℕ) : ℕ :=
  if k = 0 then 6 else 9*k

private theorem sourceTime_transverse_pair
    (p q : RP) (n k : ℕ) (hk : k < n)
    (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
    (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeTransverseProfile i) :
    ((p*q).coeff k).natDegree ≤ timeMinorProfile k := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  have hi := hp i (by omega)
  have hj := hq j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hi hj
  simp only [timeTransverseProfile, timeMinorProfile] at hdeg ⊢
  split_ifs at hdeg ⊢ <;> omega

private theorem sourceTime_transverse_triple
    (p q : RP) (n k : ℕ) (hk : k < n)
    (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
    (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeMinorProfile i) :
    ((p*q).coeff k).natDegree ≤ timeDetProfile k := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  have hi := hp i (by omega)
  have hj := hq j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hi hj
  simp only [timeTransverseProfile, timeMinorProfile, timeDetProfile] at hdeg ⊢
  split_ifs at hdeg ⊢ <;> omega

private theorem sourceTime_mixed_pair_zero
    (p q : RP) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0)
    (k : ℕ) (hk : k < 2) : (p*q).coeff k = 0 := by
  rw [_root_.Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · rw [hi, hp, zero_mul]
  · have hj : ij.2 = 0 := by omega
    rw [hj, hq, mul_zero]

private theorem sourceTime_mixed_pair
    (p q : RP) (n k : ℕ) (hk : k ≤ n)
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0)
    (hp : ∀ i < n, 0 < i → (p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (q.coeff i).natDegree ≤ 9*i-7) :
    ((p*q).coeff k).natDegree ≤ 9*k-14 := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  by_cases hi : i = 0
  · rw [hi, hp0, zero_mul, _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  by_cases hj : j = 0
  · rw [hj, hq0, mul_zero, _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le
    (hp i (by omega) (by omega)) (hq j (by omega) (by omega))
  omega

private theorem sourceTime_mixed_minor
    (p q r : RP) (n : ℕ) (hn : 2 ≤ n)
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0)
    (hp : ∀ i < n, 0 < i → (p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (q.coeff i).natDegree ≤ 9*i-7)
    (hr : ∀ i < n, (r.coeff i).natDegree ≤ timeMinorProfile i) :
    ((p*q*r).coeff n).natDegree ≤ 9*n-10 := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  by_cases hi : i < 2
  · rw [sourceTime_mixed_pair_zero p q hp0 hq0 i hi, zero_mul,
      _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  have hpq := sourceTime_mixed_pair p q n i (by omega) hp0 hq0 hp hq
  have hminor := hr j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hpq hminor
  unfold timeMinorProfile at hdeg
  split_ifs at hdeg <;> omega

/-- Pure coefficient induction step. No formal inverse and no
hypothesis on higher coefficients is used. -/
theorem transverseSchur_cleared_timeDegree_step [IsDomain R]
    (H : GeneralFourBlock RP) (n : ℕ) (hn : 2 ≤ n)
    (c : R) (hc : c ≠ 0)
    (hconstant : (transverseSchurDet H).coeff 0 = _root_.Polynomial.C c)
    (hclock : H.determinantCore.coeff n = 0)
    (ha0 : H.a.coeff 0 = 0) (ha1 : H.a.coeff 1 = 0)
    (hb0 : H.b.coeff 0 = 0) (hp0 : H.p.coeff 0 = 0) (hq0 : H.q.coeff 0 = 0)
    (ha : ∀ i < n, 2 ≤ i → (H.a.coeff i).natDegree ≤ 9*i-10)
    (hb : ∀ i < n, 0 < i → (H.b.coeff i).natDegree ≤ 9*i-7)
    (hp : ∀ i < n, 0 < i → (H.p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (H.q.coeff i).natDegree ≤ 9*i-7)
    (hd : ∀ i < n, (H.d.coeff i).natDegree ≤ timeTransverseProfile i)
    (hr : ∀ i < n, (H.r.coeff i).natDegree ≤ timeTransverseProfile i)
    (hs : ∀ i < n, (H.s.coeff i).natDegree ≤ timeTransverseProfile i)
    (hx : ∀ i < n, (H.x.coeff i).natDegree ≤ timeTransverseProfile i)
    (hy : ∀ i < n, (H.y.coeff i).natDegree ≤ timeTransverseProfile i)
    (hz : ∀ i < n, (H.z.coeff i).natDegree ≤ timeTransverseProfile i) :
    (H.a.coeff n).natDegree ≤ 9*n-10 := by
  classical
  have minor {p q r s : RP}
      (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
      (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeTransverseProfile i)
      (hr : ∀ i < n, (r.coeff i).natDegree ≤ timeTransverseProfile i)
      (hs : ∀ i < n, (s.coeff i).natDegree ≤ timeTransverseProfile i)
      (k : ℕ) (hk : k < n) :
      ((p*q-r*s).coeff k).natDegree ≤ timeMinorProfile k :=
    sourceTime_sub_coeff_degree_le
      (sourceTime_transverse_pair p q n k hk hp hq)
      (sourceTime_transverse_pair r s n k hk hr hs)
  have m1 := minor hx hz hy hy
  have m2 := minor hr hz hs hy
  have m3 := minor hr hy hs hx
  have m4 := minor hd hz hs hs
  have m5 := minor hd hy hr hs
  have m6 := minor hd hx hr hr
  have hD (k : ℕ) (hk : k < n) :
      ((transverseSchurDet H).coeff k).natDegree ≤ timeDetProfile k := by
    unfold transverseSchurDet
    exact sourceTime_add_coeff_degree_le
      (sourceTime_sub_coeff_degree_le
        (sourceTime_transverse_triple _ _ n k hk hd m1)
        (sourceTime_transverse_triple _ _ n k hk hr m2))
      (sourceTime_transverse_triple _ _ n k hk hs m3)
  have hM : ((transverseSchurMixed H).coeff n).natDegree ≤ 9*n-10 := by
    unfold transverseSchurMixed
    exact sourceTime_add_coeff_degree_le
      (sourceTime_sub_coeff_degree_le
        (sourceTime_add_coeff_degree_le
          (sourceTime_add_coeff_degree_le
            (sourceTime_sub_coeff_degree_le
              (sourceTime_mixed_minor _ _ _ n hn hb0 hb0 hb hb m1)
              (sourceTime_mixed_minor _ _ _ n hn hb0 hp0 hb hp
                (fun k hk => sourceTime_add_coeff_degree_le (m2 k hk) (m2 k hk))))
            (sourceTime_mixed_minor _ _ _ n hn hb0 hq0 hb hq
              (fun k hk => sourceTime_add_coeff_degree_le (m3 k hk) (m3 k hk))))
          (sourceTime_mixed_minor _ _ _ n hn hp0 hp0 hp hp m4))
        (sourceTime_mixed_minor _ _ _ n hn hp0 hq0 hp hq
          (fun k hk => sourceTime_add_coeff_degree_le (m5 k hk) (m5 k hk))))
      (sourceTime_mixed_minor _ _ _ n hn hq0 hq0 hq hq m6)
  have hsum : (∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
      H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2).natDegree ≤ 9*n-10 := by
    apply sourceTime_natDegree_sum_le
    intro ij hij
    have hh := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
    have hne := Finset.ne_of_mem_erase hij
    have hj : 0 < ij.2 := by
      by_contra! h
      apply hne
      exact Prod.ext (by omega) (by omega)
    by_cases hi0 : ij.1 = 0
    · rw [hi0, ha0, zero_mul, _root_.Polynomial.natDegree_zero]
      exact Nat.zero_le _
    by_cases hi1 : ij.1 = 1
    · rw [hi1, ha1, zero_mul, _root_.Polynomial.natDegree_zero]
      exact Nat.zero_le _
    have h1 := ha ij.1 (by omega) (by omega)
    have h2 := hD ij.2 (by omega)
    have hdeg := _root_.Polynomial.natDegree_mul_le_of_le h1 h2
    unfold timeDetProfile at hdeg
    split_ifs at hdeg <;> omega
  have he := transverseSchur_coeff_recurrence H n
  rw [hconstant, hclock, zero_add] at he
  have hdeg := congrArg _root_.Polynomial.natDegree he
  change (H.a.coeff n * _root_.Polynomial.C c).natDegree = _ at hdeg
  rw [_root_.Polynomial.natDegree_mul_C hc] at hdeg
  exact hdeg.trans_le ((_root_.Polynomial.natDegree_sub_le _ _).trans (max_le hM hsum))

end TimeDegreeInduction




/-- The transported leading transverse Hessian has degree at most
two, by multiplying the exact transport equation by the polynomial
inverse pencil. No division by the reference determinant is used. -/
theorem sourceNilpotent_leadingHessian_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (i j : Fin 3) :
    (linearLineEval a N (hessian L (.inr i) (.inr j))).natDegree ≤ 2 := by
  classical
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  have h : T * sourceTimePencil N = M.map _root_.Polynomial.C :=
    transverseHessian_transport_of_linear_gradient a N L hgrad
  have he : T = M.map _root_.Polynomial.C * sourceTimePencilInv N := by
    calc
      T = T * (sourceTimePencil N * sourceTimePencilInv N) := by
        rw [sourceTimePencil_right_inverse N hN, mul_one]
      _ = (T * sourceTimePencil N) * sourceTimePencilInv N := (mul_assoc _ _ _).symm
      _ = _ := by rw [h]
  change (T i j).natDegree ≤ 2
  rw [he, Matrix.mul_apply]
  apply sourceTime_natDegree_sum_le
  intro k _
  change (_root_.Polynomial.C (M i k) * sourceTimePencilInv N k j).natDegree ≤ 2
  exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
    (sourceTimePencilInv_natDegree_le N k j)

/-- All six transverse coefficients are entries of the actual evaluated
source Hessian. Package their common bound for the induction. -/
private theorem sourceLinear_frame_transverse_degree
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (d : ℕ)
    (hd : ∀ i k : Fin 3, (linearLineEval a N
      (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)
        (.inr i) (.inr k))).natDegree ≤ d) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    (H.d.coeff j).natDegree ≤ d ∧ (H.r.coeff j).natDegree ≤ d ∧
    (H.s.coeff j).natDegree ≤ d ∧ (H.x.coeff j).natDegree ≤ d ∧
    (H.y.coeff j).natDegree ≤ d ∧ (H.z.coeff j).natDegree ≤ d := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let H := sourceLeading_lineSchurFrame F m z V
  let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
  have he := sourceLeading_lineSchurFrame_coeff F m j hj z V
  have h00 : H.d.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 0)) :=
    congrArg GeneralFourBlock.d he
  have h01 : H.r.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 1)) :=
    congrArg GeneralFourBlock.r he
  have h02 : H.s.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 2)) :=
    congrArg GeneralFourBlock.s he
  have h11 : H.x.coeff j = linearLineEval a N (hessian Q (.inr 1) (.inr 1)) :=
    congrArg GeneralFourBlock.x he
  have h12 : H.y.coeff j = linearLineEval a N (hessian Q (.inr 1) (.inr 2)) :=
    congrArg GeneralFourBlock.y he
  have h22 : H.z.coeff j = linearLineEval a N (hessian Q (.inr 2) (.inr 2)) :=
    congrArg GeneralFourBlock.z he
  change (H.d.coeff j).natDegree ≤ d ∧ (H.r.coeff j).natDegree ≤ d ∧
    (H.s.coeff j).natDegree ≤ d ∧ (H.x.coeff j).natDegree ≤ d ∧
    (H.y.coeff j).natDegree ≤ d ∧ (H.z.coeff j).natDegree ≤ d
  rw [h00, h01, h02, h11, h12, h22]
  exact ⟨hd 0 0, hd 0 1, hd 0 2, hd 1 1, hd 1 2, hd 2 2⟩

/-- Uniform degree control of every positive-order actual source layer
in a regular nilpotent linear characteristic chart. The determinant
clock and leading transport are the only source hypotheses used.
The estimate is independent of the original longitudinal degree. -/
theorem sourceNilpotent_allCorrections_timeDegree_le
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (j : ℕ) (hj : j ≤ m) (hjpos : 0 < j) :
    (linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)).natDegree
      ≤ 9*j-8 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let Q := fun i : ℕ => initialForm transverseCubicWeight ((m : ℤ)-(i : ℤ)) F
  let P := fun i : ℕ => linearLineEval a N (Q i)
  let H := sourceLeading_lineSchurFrame F m z V
  let c := referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  have ht : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)) := fun i => hgrad (.inr i)
  obtain ⟨hb0, hp0, hq0, hregular⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hg
  have hclock (i : ℕ) (hi : i ≤ m) : H.determinantCore.coeff i = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff i = 0
    rw [sourceLeading_lineSchurFrame_det F m (by omega) hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ i)]
  obtain ⟨ha0, ha1⟩ := transverseSchur_longitudinal_zero_one H hb0 hp0 hq0
    hregular (hclock 0 (by omega)) (hclock 1 (by omega))
  have hconstant : (transverseSchurDet H).coeff 0 = _root_.Polynomial.C c := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (linearLineEval a N).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
    exact (sourceLinear_leadingAdjugate_transport a N L hreg ht).1
  have hdiff (i : ℕ) (hi : i ≤ m) :
      H.a.coeff i = (P i).derivative.derivative ∧
      H.b.coeff i = (linearLineEval a N (pderiv (.inr 0) (Q i))).derivative ∧
      H.p.coeff i = (linearLineEval a N (pderiv (.inr 1) (Q i))).derivative ∧
      H.q.coeff i = (linearLineEval a N (pderiv (.inr 2) (Q i))).derivative :=
    sourceLeading_lineSchurFrame_differential_coeff F m i hi z V hV
  have hbase : (P 1).natDegree ≤ 1 := by
    have he : P 1 = _root_.Polynomial.C ((P 1).coeff 0) +
        _root_.Polynomial.C ((P 1).coeff 1) * _root_.Polynomial.X :=
      sourceNilpotent_firstCorrection_affine F (m : ℤ) (by omega) hcap hdet a N hreg hgrad
    calc
      _ = (_root_.Polynomial.C ((P 1).coeff 0) +
          _root_.Polynomial.C ((P 1).coeff 1) * _root_.Polynomial.X).natDegree :=
        congrArg _root_.Polynomial.natDegree he
      _ ≤ 1 := _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
        ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hlead (i k : Fin 3) :
      (linearLineEval a N (hessian (Q 0) (.inr i) (.inr k))).natDegree ≤ 2 := by
    simpa only [Q, Nat.cast_zero, sub_zero] using
      sourceNilpotent_leadingHessian_timeDegree_le a N hN L ht i k
  have hmain (n : ℕ) : n ≤ m → 0 < n → (P n).natDegree ≤ 9*n-8 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hpos
      by_cases hone : n = 1
      · subst n
        exact hbase
      have htwo : 2 ≤ n := by omega
      have hprev (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (P i).natDegree ≤ 9*i-8 := ih i hi (by omega) hip
      have ha (i : ℕ) (hi : i < n) (hip : 2 ≤ i) :
          (H.a.coeff i).natDegree ≤ 9*i-10 := by
        rw [(hdiff i (by omega)).1]
        have h1 := _root_.Polynomial.natDegree_derivative_le (P i)
        have h2 := _root_.Polynomial.natDegree_derivative_le (P i).derivative
        have h3 := hprev i hi (by omega)
        omega
      have hmixed (i : ℕ) (hi : i < n) (hip : 0 < i) (k : Fin 3) :
          (linearLineEval a N (pderiv (.inr k) (Q i))).derivative.natDegree ≤ 9*i-7 := by
        have he := sourceNilpotent_mixed_timeDegree_le a N hN (Q i) k
        change _ ≤ (P i).natDegree + 1 at he
        have hp := hprev i hi hip
        omega
      have htrans (i : ℕ) (hi : i < n) :
          (H.d.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.r.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.s.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.x.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.y.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.z.coeff i).natDegree ≤ timeTransverseProfile i := by
        apply sourceLinear_frame_transverse_degree F m i (by omega) a N
        intro k l
        change (linearLineEval a N (hessian (Q i) (.inr k) (.inr l))).natDegree ≤ _
        by_cases hi0 : i = 0
        · subst i
          simpa only [timeTransverseProfile, if_pos rfl] using hlead k l
        · have he := sourceNilpotent_transverseHessian_timeDegree_le a N hN (Q i) k l
          change _ ≤ (P i).natDegree + 4 at he
          have hp := hprev i hi (by omega)
          simp only [timeTransverseProfile, if_neg hi0]
          omega
      have hb (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.b.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.1]
        exact hmixed i hi hip 0
      have hp (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.p.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.2.1]
        exact hmixed i hi hip 1
      have hq (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.q.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.2.2]
        exact hmixed i hi hip 2
      have hd := transverseSchur_cleared_timeDegree_step H n htwo c hreg hconstant
        (hclock n hn) ha0 ha1 hb0 hp0 hq0 ha hb hp hq
        (fun i hi => (htrans i hi).1)
        (fun i hi => (htrans i hi).2.1)
        (fun i hi => (htrans i hi).2.2.1)
        (fun i hi => (htrans i hi).2.2.2.1)
        (fun i hi => (htrans i hi).2.2.2.2.1)
        (fun i hi => (htrans i hi).2.2.2.2.2)
      rw [(hdiff n hn).1] at hd
      have hlast := sourceTime_degree_of_secondDerivative_le (P n) (9*n-10) hd
      omega
  exact hmain j hj hjpos




/-! ## Return to original coordinates -/

private theorem sourceTotalDegree_sum_le
    {σ I : Type*} (s : Finset I) (f : I → MvPolynomial σ K)
    (d : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_finset_sum s f).trans (Finset.sup_le h)

private theorem sourceTime_referenceCoeff_mul
    (P Q : LineTime K) (d e : ℕ)
    (hp : ∀ k, (P.coeff k).totalDegree ≤ d)
    (hq : ∀ k, (Q.coeff k).totalDegree ≤ e) :
    ∀ k, ((P*Q).coeff k).totalDegree ≤ d+e := by
  intro k
  rw [_root_.Polynomial.coeff_mul]
  apply sourceTotalDegree_sum_le
  intro ij _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp ij.1) (hq ij.2))

private theorem sourceTime_referenceCoeff_pow
    (P : LineTime K) (d : ℕ) (hp : ∀ k, (P.coeff k).totalDegree ≤ d)
    (n : ℕ) : ∀ k, ((P^n).coeff k).totalDegree ≤ n*d := by
  induction n with
  | zero =>
    intro k
    simp only [pow_zero, zero_mul, _root_.Polynomial.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact sourceTime_referenceCoeff_mul _ _ _ _ ih hp

private theorem sourceTime_referenceCoeff_prod
    {I : Type*} (s : Finset I) (f : I → LineTime K) (d : I → ℕ)
    (h : ∀ i ∈ s, ∀ k, ((f i).coeff k).totalDegree ≤ d i) :
    ∀ k, ((∏ i ∈ s, f i).coeff k).totalDegree ≤ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, Finset.sum_empty, _root_.Polynomial.coeff_one]
    split_ifs <;> simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact sourceTime_referenceCoeff_mul _ _ _ _
      (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem sourceLinearVector_totalDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (sourceLinearVector N i).totalDegree ≤ 1 := by
  unfold sourceLinearVector
  apply sourceTotalDegree_sum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private theorem referenceLinearVector_totalDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (referenceLinearVector N i).totalDegree ≤ 1 := by
  unfold referenceLinearVector
  apply sourceTotalDegree_sum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private def sourceTransverseNatGrade : Unit ⊕ Fin 3 → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

private theorem sourceTransverseNatGrade_sum (d : StationaryExponent) :
    ((∑ i ∈ d.support, d i * sourceTransverseNatGrade i : ℕ) : ℤ) =
      Finsupp.weight transverseCubicWeight d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl u => cases u; simp [sourceTransverseNatGrade, transverseCubicWeight]
  | inr j => simp [sourceTransverseNatGrade, transverseCubicWeight, nsmul_eq_mul]

private theorem sourceTime_referenceCoeff_X
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (i : Unit ⊕ Fin 3) (k : ℕ) :
    ((linearLineEval a N (X i)).coeff k).totalDegree ≤ sourceTransverseNatGrade i := by
  cases i with
  | inl u =>
    cases u
    have he : linearLineEval a N (X (.inl ())) =
        _root_.Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin 3) K) +
          _root_.Polynomial.X := by simp [linearLineEval, lineEval]
    rw [he, _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_X]
    split_ifs <;> simp [sourceTransverseNatGrade] <;> omega
  | inr i =>
    have he : linearLineEval a N (X (.inr i)) =
        _root_.Polynomial.C (X i : MvPolynomial (Fin 3) K) +
          _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
      simp [linearLineEval, lineEval, referenceLinearVector]
    rw [he, _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C,
      _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X]
    have h := referenceLinearVector_totalDegree_le N i
    split_ifs <;> simp_all [sourceTransverseNatGrade]

/-- The time coefficients of a transverse homogeneous source layer
have reference total degree at most the original transverse grade. -/
theorem sourceLinear_referenceCoeff_totalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (Q : StationarySource K) (r : ℕ)
    (hQ : IsWeightLE transverseCubicWeight (r : ℤ) Q) (k : ℕ) :
    ((linearLineEval a N Q).coeff k).totalDegree ≤ r := by
  classical
  calc
    _ = ((linearLineEval a N (∑ d ∈ Q.support,
      MvPolynomial.monomial d (MvPolynomial.coeff d Q))).coeff k).totalDegree :=
        congrArg (fun P => ((linearLineEval a N P).coeff k).totalDegree) (MvPolynomial.as_sum Q)
    _ ≤ r := by
      rw [map_sum, _root_.Polynomial.finset_sum_coeff]
      apply sourceTotalDegree_sum_le
      intro d hd
      have hweight := hQ hd
      have hsum := sourceTransverseNatGrade_sum d
      have hbound : (∑ i ∈ d.support, d i * sourceTransverseNatGrade i) ≤ r := by omega
      rw [MvPolynomial.monomial_eq, map_mul]
      change ((linearLineEval a N (MvPolynomial.C (MvPolynomial.coeff d Q)) *
        linearLineEval a N (∏ i ∈ d.support, X i ^ d i)).coeff k).totalDegree ≤ r
      simp only [map_prod, map_pow]
      have hc : linearLineEval a N (MvPolynomial.C (MvPolynomial.coeff d Q)) =
          _root_.Polynomial.C (MvPolynomial.C (MvPolynomial.coeff d Q)) := by
        simp [linearLineEval, lineEval]
      rw [hc, _root_.Polynomial.coeff_C_mul]
      have hp := sourceTime_referenceCoeff_prod d.support
        (fun i => linearLineEval a N (X i) ^ d i)
        (fun i => d i * sourceTransverseNatGrade i)
        (fun i _ => sourceTime_referenceCoeff_pow _ _
          (sourceTime_referenceCoeff_X a N i) (d i)) k
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact hp.trans hbound)

private theorem sourceTime_shift_totalDegree_le (a : K) :
    (X (.inl ()) - MvPolynomial.C a : StationarySource K).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg, ← map_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

private theorem sourceNilpotentInverseEval_X_degree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (sourceNilpotentInverseEval a N (X i)).totalDegree ≤ 3 := by
  rw [sourceNilpotentInverseEval, MvPolynomial.aeval_X]
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  change ((X (Sum.inr i : Unit ⊕ Fin 3) : StationarySource K) - t * sourceLinearVector N i +
    t^2 * sourceLinearVector (N^2) i).totalDegree ≤ 3
  have ht := sourceTime_shift_totalDegree_le a
  have h1 := (MvPolynomial.totalDegree_mul t (sourceLinearVector N i)).trans
    (Nat.add_le_add ht (sourceLinearVector_totalDegree_le N i))
  have h2 := (MvPolynomial.totalDegree_pow t 2).trans (Nat.mul_le_mul_left 2 ht)
  have h3 := (MvPolynomial.totalDegree_mul (t^2) (sourceLinearVector (N^2) i)).trans
    (Nat.add_le_add h2 (sourceLinearVector_totalDegree_le (N^2) i))
  have hn : (-(t * sourceLinearVector N i)).totalDegree ≤ 2 := by
    rw [← neg_one_mul]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using h1)
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) (hn.trans (by omega))))
      (h3.trans (by omega)))

/-- Inverse characteristic substitution increases reference total
degree by at most a factor of three. -/
theorem sourceNilpotentInverseEval_totalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (P : MvPolynomial (Fin 3) K) :
    (sourceNilpotentInverseEval a N P).totalDegree ≤ 3*P.totalDegree := by
  classical
  calc
    _ = (sourceNilpotentInverseEval a N (∑ d ∈ P.support,
      MvPolynomial.monomial d (MvPolynomial.coeff d P))).totalDegree :=
        congrArg (fun p => (sourceNilpotentInverseEval a N p).totalDegree) (MvPolynomial.as_sum P)
    _ ≤ _ := by
      rw [map_sum]
      apply sourceTotalDegree_sum_le
      intro d hd
      rw [MvPolynomial.monomial_eq, map_mul]
      change (sourceNilpotentInverseEval a N (MvPolynomial.C (MvPolynomial.coeff d P)) *
        sourceNilpotentInverseEval a N (∏ i ∈ d.support, X i ^ d i)).totalDegree ≤ _
      simp only [map_prod, map_pow]
      rw [show sourceNilpotentInverseEval a N (MvPolynomial.C (MvPolynomial.coeff d P)) =
        MvPolynomial.C (MvPolynomial.coeff d P) by simp [sourceNilpotentInverseEval]]
      apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C, zero_add]
      apply (MvPolynomial.totalDegree_finset_prod _ _).trans
      calc
        _ ≤ ∑ i ∈ d.support, d i * 3 := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (Nat.mul_le_mul_left _ (sourceNilpotentInverseEval_X_degree_le a N i))
        _ = 3 * d.sum (fun _ e => e) := by
          rw [Finsupp.sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree hd)

/-- Reconstruction in every time degree, not just the first correction. -/
theorem sourceNilpotent_inverseFormula
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) :
    let P := linearLineEval a N Q
    Q = ∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) *
      (X (.inl ()) - MvPolynomial.C a)^k := by
  let P := linearLineEval a N Q
  apply linearLineEval_injective_of_cube_zero a N hN
  simp only [map_sum, map_mul, map_pow, sourceNilpotentInverseEval_transport a N hN,
    sourceNilpotent_time_eval]
  exact (_root_.Polynomial.sum_C_mul_X_pow_eq P).symm

set_option maxHeartbeats 1000000 in
/-- A transverse cap and a time-degree cap in the nilpotent chart
give a bound on the ORIGINAL polynomial, with no determinant change. -/
theorem sourceNilpotent_originalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (r d : ℕ)
    (hQ : IsWeightLE transverseCubicWeight (r : ℤ) Q)
    (hP : (linearLineEval a N Q).natDegree ≤ d) :
    Q.totalDegree ≤ 3*r+d := by
  let P := linearLineEval a N Q
  have he := sourceNilpotent_inverseFormula a N hN Q
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  change Q = ∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) * t^k at he
  calc
    _ = (∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) * t^k).totalDegree :=
        congrArg MvPolynomial.totalDegree he
    _ ≤ _ := by
      apply sourceTotalDegree_sum_le
      intro k hk
      have hk' := (_root_.Polynomial.le_natDegree_of_ne_zero (_root_.Polynomial.mem_support_iff.mp hk)).trans hP
      have hc := sourceLinear_referenceCoeff_totalDegree_le a N Q r hQ k
      have h1 := (sourceNilpotentInverseEval_totalDegree_le a N (P.coeff k)).trans
        (Nat.mul_le_mul_left 3 hc)
      have h2 := (MvPolynomial.totalDegree_pow t k).trans
        (Nat.mul_le_mul_left k (sourceTime_shift_totalDegree_le a))
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add h1 (h2.trans (by simpa using hk')))




/-- A global original-coordinate total-degree bound for a regular
nilpotent linear characteristic of an actual constant-Hessian source.
No longitudinal degree bound is an input. -/
theorem sourceNilpotent_totalDegree_le
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    F.totalDegree ≤ 9*m-8 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  have hlead : (linearLineEval a N L).derivative.derivative = 0 := by
    change (lineEval z V L).derivative.derivative = 0
    rw [transverse_lineEval_derivative]
    have hg : ∀ i, lineEval z V (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L)) := hgrad
    rw [_root_.Polynomial.derivative_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [hg i]
    have he : (_root_.Polynomial.C (V i) : LineTime K) *
        _root_.Polynomial.C (referenceSlice a (pderiv i L)) =
        _root_.Polynomial.C (V i * referenceSlice a (pderiv i L)) :=
      (_root_.Polynomial.C.map_mul (V i) (referenceSlice a (pderiv i L))).symm
    calc
      _ = (_root_.Polynomial.C (V i * referenceSlice a (pderiv i L)) :
          LineTime K).derivative :=
        congrArg _root_.Polynomial.derivative he
      _ = 0 := _root_.Polynomial.derivative_C
  have hleadDegree : (linearLineEval a N L).natDegree ≤ 2 :=
    sourceTime_degree_of_secondDerivative_le _ 0 (by rw [hlead]; simp)
  have hsum := sourceLeading_reverseLayerSum_eq F m hcap
  calc
    _ = (∑ j ∈ Finset.range (m+1),
      initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F).totalDegree :=
        congrArg MvPolynomial.totalDegree hsum.symm
    _ ≤ _ := by
      apply sourceTotalDegree_sum_le
      intro j hj
      have hjm : j ≤ m := by
        have hh := Finset.mem_range.mp hj
        omega
      let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
      have hQ : IsWeightLE transverseCubicWeight ((m-j : ℕ) : ℤ) Q := by
        intro d hd
        have he := initialForm_isWeightedHomogeneous transverseCubicWeight
          ((m : ℤ)-(j : ℤ)) F (MvPolynomial.mem_support_iff.mp hd)
        rw [Nat.cast_sub hjm]
        exact he.le
      by_cases hj0 : j = 0
      · subst j
        have hh : Q = L := by simp [Q, L]
        have hP : (linearLineEval a N Q).natDegree ≤ 2 := by rw [hh]; exact hleadDegree
        have hd := sourceNilpotent_originalDegree_le a N hN Q (m-0) 2 hQ hP
        exact hd.trans (by omega)
      · have hP := sourceNilpotent_allCorrections_timeDegree_le F m hm hcap hdet
          a N hN hreg hgrad j hjm (by omega)
        have hd := sourceNilpotent_originalDegree_le a N hN Q (m-j) (9*j-8) hQ hP
        exact hd.trans (by omega)




/-! ## A collision obstruction directly on the marked gradient curve

The original Hessian determinant implies a Bezout identity for the
derivative of the actual marked-axis gradient, not just pointwise
nonvanishing over the ground field. Consequently a collision cannot
be carried by a rank-one polynomial gradient curve, even when the
longitudinal degree is large.
-/

def stationaryAxisTrace : StationarySource K →ₐ[K] _root_.Polynomial K :=
  lineEval (fun _ => 0) (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0))

theorem stationaryAxisTrace_eval (P : StationarySource K) (t : K) :
    (stationaryAxisTrace P).eval t = stationaryAxisEval t P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [stationaryAxisTrace, stationaryAxisEval, lineEval]
  | add p q hp hq =>
    simp only [map_add, _root_.Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, _root_.Polynomial.eval_mul, map_mul, hp]
    cases i with
    | inl u => cases u; simp [stationaryAxisTrace, stationaryAxisEval, lineEval]
    | inr j => simp [stationaryAxisTrace, stationaryAxisEval, lineEval]

theorem stationaryAxisTrace_derivative (P : StationarySource K) :
    (stationaryAxisTrace P).derivative = stationaryAxisTrace (pderiv (.inl ()) P) := by
  classical
  change (lineEval (fun _ => (0 : K))
    (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0)) P).derivative = _
  rw [transverse_lineEval_derivative, Fintype.sum_sum_type]
  simp [stationaryAxisTrace]

/-- The cofactor row is an explicit polynomial Bezout certificate
for the tangent vector of the actual marked gradient curve. -/
theorem stationaryAxisTrace_gradient_bezout
    (F : StationarySource K) {δ : K}
    (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
    ∑ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i =
        _root_.Polynomial.C δ := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  have hA : A.det = _root_.Polynomial.C δ := by
    change ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).det = _
    rw [← RingHom.map_det]
    change stationaryAxisTrace (hessianDeterminant F) = _
    rw [hdet]
    simp [stationaryAxisTrace, lineEval]
  change (∑ i : Unit ⊕ Fin 3,
    (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) = _
  calc
    _ = ∑ i : Unit ⊕ Fin 3, A i (.inl ()) * A.adjugate (.inl ()) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [stationaryAxisTrace_derivative]
      rfl
    _ = A.det := (Matrix.det_eq_sum_mul_adjugate_col A (.inl ())).symm
    _ = _ := hA

/-- No nonconstant polynomial can divide every component of the
marked gradient tangent. This holds without a regular transverse
anchor and without any degree cap on the source. -/
theorem stationaryAxisTrace_commonDerivativeDivisor_degree_zero
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (D : _root_.Polynomial K)
    (hD : ∀ i : Unit ⊕ Fin 3, D ∣ (stationaryAxisTrace (pderiv i F)).derivative) :
    D.natDegree = 0 := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  choose Q hQ using hD
  have h := stationaryAxisTrace_gradient_bezout F hdet
  change (∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
    A.adjugate (.inl ()) i) = _ at h
  let E := ∑ i : Unit ⊕ Fin 3, Q i * A.adjugate (.inl ()) i
  have he : D * E = _root_.Polynomial.C δ := by
    dsimp [E]
    rw [Finset.mul_sum]
    calc
      _ = ∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
          A.adjugate (.inl ()) i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hQ i, mul_assoc]
      _ = _ := h
  have hne : D * E ≠ 0 := by rw [he]; exact _root_.Polynomial.C_ne_zero.mpr hδ
  have hd : D ≠ 0 := by
    intro hz
    apply hne
    rw [hz, zero_mul]
  have he' : E ≠ 0 := by
    intro hz
    apply hne
    rw [hz, mul_zero]
  have hdegree := congrArg _root_.Polynomial.natDegree he
  rw [_root_.Polynomial.natDegree_mul' (mul_ne_zero
    (_root_.Polynomial.leadingCoeff_ne_zero.mpr hd)
    (_root_.Polynomial.leadingCoeff_ne_zero.mpr he')),
    _root_.Polynomial.natDegree_C] at hdegree
  omega

private theorem sourceTime_derivative_constant_of_equal_endpoints
    (P : _root_.Polynomial K) (c : K)
    (h : P.derivative = _root_.Polynomial.C c)
    (he : P.eval 1 = P.eval 0) : P.derivative = 0 := by
  let Q := P - _root_.Polynomial.C c * _root_.Polynomial.X
  have hQ : Q.derivative = 0 := by
    change (P - _root_.Polynomial.C c * _root_.Polynomial.X).derivative = 0
    rw [map_sub, h, _root_.Polynomial.derivative_mul,
      _root_.Polynomial.derivative_C, _root_.Polynomial.derivative_X]
    simp
  have hc := _root_.Polynomial.eq_C_of_derivative_eq_zero hQ
  have h1 := congrArg (fun q : _root_.Polynomial K => q.eval 1) hc
  have h0 := congrArg (fun q : _root_.Polynomial K => q.eval 0) hc
  change (P - _root_.Polynomial.C c * _root_.Polynomial.X).eval 1 =
    (_root_.Polynomial.C (Q.coeff 0)).eval 1 at h1
  change (P - _root_.Polynomial.C c * _root_.Polynomial.X).eval 0 =
    (_root_.Polynomial.C (Q.coeff 0)).eval 0 at h0
  simp only [_root_.Polynomial.eval_sub, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, _root_.Polynomial.eval_X, mul_one, mul_zero, sub_zero] at h1 h0
  have hz : c = 0 := by
    rw [he, h0] at h1
    linear_combination -h1
  rw [h, hz, map_zero]

/-- A marked collision cannot have its entire gradient trace in an
affine line, even if the source and the trace have arbitrary degree.
The tangent rank-one assumption is stated as an exact polynomial
identity, not a condition on only one evaluation point. -/
theorem stationaryAxisTrace_rankOne_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (D : _root_.Polynomial K) (v : Unit ⊕ Fin 3 → K)
    (hline : ∀ i, (stationaryAxisTrace (pderiv i F)).derivative =
      _root_.Polynomial.C (v i) * D) : False := by
  classical
  have hD : ∀ i : Unit ⊕ Fin 3, D ∣ (stationaryAxisTrace (pderiv i F)).derivative := by
    intro i
    refine ⟨_root_.Polynomial.C (v i), ?_⟩
    rw [hline i, mul_comm]
  have hd := stationaryAxisTrace_commonDerivativeDivisor_degree_zero F hδ hdet D hD
  have hC := _root_.Polynomial.eq_C_of_natDegree_eq_zero hd
  have hz (i : Unit ⊕ Fin 3) : (stationaryAxisTrace (pderiv i F)).derivative = 0 := by
    apply sourceTime_derivative_constant_of_equal_endpoints _ (v i * D.coeff 0)
    · calc
        _ = _root_.Polynomial.C (v i) * D := hline i
        _ = _root_.Polynomial.C (v i) * _root_.Polynomial.C (D.coeff 0) :=
          congrArg (fun p => _root_.Polynomial.C (v i) * p) hC
        _ = _ := (_root_.Polynomial.C.map_mul _ _).symm
    · rw [stationaryAxisTrace_eval, stationaryAxisTrace_eval]
      exact hcoll i
  have hb := stationaryAxisTrace_gradient_bezout F hdet
  change (∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
    ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).adjugate (.inl ()) i) = _ at hb
  simp only [hz, zero_mul, Finset.sum_const_zero] at hb
  exact hδ (_root_.Polynomial.C_eq_zero.mp hb.symm)




/-! ## Exact low-grade extraction on the marked axis

The entire marked gradient and its Hessian witness are determined
by the first three transverse grades of the ORIGINAL source.
No replacement potential is asserted to have constant determinant
away from that axis.
-/

/-- Only transverse grade zero survives the marked-axis substitution. -/
theorem stationaryAxisTrace_initialForm_zero (P : StationarySource K) :
    stationaryAxisTrace (initialForm transverseCubicWeight 0 P) =
      stationaryAxisTrace P := by
  classical
  have hz : stationaryAxisTrace (P - initialForm transverseCubicWeight 0 P) = 0 := by
    change MvPolynomial.aeval
      (fun i : Unit ⊕ Fin 3 =>
        _root_.Polynomial.C (0 : K) +
          _root_.Polynomial.C (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0) i) *
            _root_.Polynomial.X) (P - initialForm transverseCubicWeight 0 P) = 0
    apply MvPolynomial.aeval_eq_zero
    intro d hd
    have hw : Finsupp.weight transverseCubicWeight d ≠ 0 := by
      intro h
      apply hd
      simp [MvPolynomial.coeff_sub, coeff_initialForm, h]
    have he : ∃ j : Fin 3, d (.inr j) ≠ 0 := by
      by_contra! hn
      apply hw
      rw [transverseCubicWeight_eq_transverseSum]
      simp [hn]
    obtain ⟨j, hj⟩ := he
    exact ⟨.inr j, Finsupp.mem_support_iff.mpr hj, by simp⟩
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- The actual marked gradient component comes from exactly one
transverse source layer: zero for the longitudinal component and
one for each transverse component. -/
theorem stationaryAxisTrace_gradient_layer
    (F : StationarySource K) (i : Unit ⊕ Fin 3) :
    stationaryAxisTrace (pderiv i F) =
      stationaryAxisTrace (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F)) := by
  rw [pderiv_initialForm, sub_self, stationaryAxisTrace_initialForm_zero]

/-- Each entry of the actual marked Hessian comes from precisely the
source layer indexed by the sum of the two derivative weights. -/
theorem stationaryAxisTrace_hessian_layer
    (F : StationarySource K) (i j : Unit ⊕ Fin 3) :
    stationaryAxisTrace (hessian F i j) =
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j) := by
  rw [hessian_initialForm_entry,
    show transverseCubicWeight i + transverseCubicWeight j -
      transverseCubicWeight i - transverseCubicWeight j = 0 by ring,
    stationaryAxisTrace_initialForm_zero]

/-- The marked-axis Hessian determinant is an exact low-layer
certificate, independent of the remaining high source layers. -/
theorem stationaryAxisTrace_lowLayers_det
    (F : StationarySource K) {δ : K}
    (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    (Matrix.of fun i j : Unit ⊕ Fin 3 =>
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j)).det =
      _root_.Polynomial.C δ := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  have he : (Matrix.of fun i j : Unit ⊕ Fin 3 =>
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j)) = A := by
    apply Matrix.ext
    intro i j
    change stationaryAxisTrace (hessian (initialForm transverseCubicWeight
      (transverseCubicWeight i + transverseCubicWeight j) F) i j) =
        stationaryAxisTrace (hessian F i j)
    exact (stationaryAxisTrace_hessian_layer F i j).symm
  rw [he]
  change ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).det = _
  rw [← RingHom.map_det]
  change stationaryAxisTrace (hessianDeterminant F) = _
  rw [hdet]
  simp [stationaryAxisTrace, lineEval]

private theorem stationaryAxisTrace_quadratic_secant
    (P : _root_.Polynomial K) (hP : P.natDegree ≤ 2) :
    P.eval 1 - P.eval 0 = P.derivative.eval (1/2) := by
  have he : P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X +
      _root_.Polynomial.C (P.coeff 2) * _root_.Polynomial.X^2 := by
    apply _root_.Polynomial.ext
    intro n
    have hz (k : ℕ) : P.coeff (k+3) = 0 :=
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          simpa [_root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X_pow,
            Nat.succ_eq_add_one, Nat.add_assoc] using hz n
  have h1 := congrArg (fun p : _root_.Polynomial K => p.eval 1) he
  have h0 := congrArg (fun p : _root_.Polynomial K => p.eval 0) he
  have hd := congrArg (fun p : _root_.Polynomial K => p.derivative.eval (1/2)) he
  dsimp only at h1 h0 hd
  rw [h1, h0, hd]
  simp [_root_.Polynomial.derivative_add, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow] <;> ring

/-- Arbitrary total degree is allowed: a quadratic restriction of the
actual gradient to the marked axis is enough to forbid the collision. -/
theorem stationaryAxisTrace_quadraticGradient_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (hquad : ∀ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).natDegree ≤ 2) : False := by
  classical
  have hz (i : Unit ⊕ Fin 3) :
      ((stationaryAxisTrace (pderiv i F)).derivative).eval (1/2) = 0 := by
    have he := stationaryAxisTrace_quadratic_secant
      (stationaryAxisTrace (pderiv i F)) (hquad i)
    rw [stationaryAxisTrace_eval, stationaryAxisTrace_eval, hcoll i, sub_self] at he
    exact he.symm
  have hb := stationaryAxisTrace_gradient_bezout F hdet
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  change (∑ i : Unit ⊕ Fin 3,
    (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) =
      _root_.Polynomial.C δ at hb
  have he := congrArg (fun p : _root_.Polynomial K => p.eval (1/2)) hb
  change (_root_.Polynomial.evalRingHom (1/2 : K))
    (∑ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) =
    (_root_.Polynomial.evalRingHom (1/2 : K)) (_root_.Polynomial.C δ) at he
  simp only [map_sum, map_mul, _root_.Polynomial.coe_evalRingHom,
    hz, zero_mul, Finset.sum_const_zero, _root_.Polynomial.eval_C] at he
  exact hδ he.symm

/-- Any surviving marked collision forces a genuinely higher-degree
gradient trace in transverse grade zero or one of the actual source.
Higher layers cannot conceal this necessary condition. -/
theorem stationaryAxisTrace_collision_forces_lowLayer_degree
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    ∃ i : Unit ⊕ Fin 3, 3 ≤ (stationaryAxisTrace
      (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F))).natDegree := by
  by_contra! h
  apply stationaryAxisTrace_quadraticGradient_markedCollision_impossible F hδ hdet hcoll
  intro i
  rw [stationaryAxisTrace_gradient_layer]
  have hi := h i
  omega




/-! ## Mixed-gap propagation to the actual terminal layers

A sufficiently late mixed correction forces every pre-gap
longitudinal correction to vanish, using the exact determinant
clock. The gap condition is explicit; it is not yet extracted
from the leading characteristic classification.
-/

section MixedGap

variable {R : Type*} [CommRing R] [IsDomain R]
local notation "RP" => _root_.Polynomial R

private theorem transverse_gap_mul
    (p q : RP) (a b n : ℕ) (hn : n < a+b)
    (hp : ∀ i < a, p.coeff i = 0)
    (hq : ∀ i < b, q.coeff i = 0) :
    (p*q).coeff n = 0 := by
  rw [_root_.Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < a
  · rw [hp _ hi, zero_mul]
  · rw [hq _ (by omega), mul_zero]

private theorem transverse_gap_triple
    (p q r : RP) (k n : ℕ) (hn : n < 2*k)
    (hp : ∀ i < k, p.coeff i = 0)
    (hq : ∀ i < k, q.coeff i = 0) :
    (p*q*r).coeff n = 0 := by
  apply transverse_gap_mul (p*q) r (2*k) 0 n (by omega)
  · intro i hi
    exact transverse_gap_mul p q k k i (by omega) hp hq
  · intro i hi
    omega

/-- A mixed gap of length k implies a gap of length 2*k in the
quadratic adjugate pairing. -/
theorem transverseSchurMixed_coeff_zero_of_gap
    (H : GeneralFourBlock RP) (k n : ℕ) (hn : n < 2*k)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0) :
    (transverseSchurMixed H).coeff n = 0 := by
  simp only [transverseSchurMixed, _root_.Polynomial.coeff_add,
    _root_.Polynomial.coeff_sub,
    transverse_gap_triple _ _ _ k n hn hb hb,
    transverse_gap_triple _ _ _ k n hn hb hp,
    transverse_gap_triple _ _ _ k n hn hb hq,
    transverse_gap_triple _ _ _ k n hn hp hp,
    transverse_gap_triple _ _ _ k n hn hp hq,
    transverse_gap_triple _ _ _ k n hn hq hq, sub_self, add_zero]

/-- The determinant and mixed gaps propagate through the cleared
Schur recurrence, with no inverse or division of coefficients. -/
theorem transverseSchur_longitudinal_zero_of_mixedGap
    (H : GeneralFourBlock RP) (k clock : ℕ)
    (hreg : (transverseSchurDet H).coeff 0 ≠ 0)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0)
    (hdet : ∀ i < clock, H.determinantCore.coeff i = 0) :
    ∀ n < 2*k, n < clock → H.a.coeff n = 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hc
    have he := transverseSchur_coeff_recurrence H n
    have hsum : (∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
        H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2) = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      have hh := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
      have hne := Finset.ne_of_mem_erase hij
      have hi : ij.1 < n := by
        by_contra! h
        apply hne
        exact Prod.ext (by omega) (by omega)
      rw [ih ij.1 hi (by omega) (by omega), zero_mul]
    rw [hdet n hc, transverseSchurMixed_coeff_zero_of_gap H k n hn hb hp hq,
      hsum, zero_add, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hreg

end MixedGap

/-- In a genuine source characteristic chart, a mixed gap forces
actual source layers to be affine in characteristic time all the
way up to the smaller of twice the gap and the determinant clock. -/
theorem sourceLeading_correction_secondDerivative_zero_of_mixedGap
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (hgap : j < 2*k) (hclock : j < 4*m-6) :
    (lineEval z V (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)).derivative.derivative = 0 := by
  let H := sourceLeading_lineSchurFrame F m z V
  have hd (i : ℕ) (hi : i < 4*m-6) : H.determinantCore.coeff i = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff i = 0
    rw [sourceLeading_lineSchurFrame_det F m hm hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ i)]
  have ha := transverseSchur_longitudinal_zero_of_mixedGap H k (4*m-6)
    hreg hb hp hq hd j hgap hclock
  rw [(sourceLeading_lineSchurFrame_differential_coeff F m j hj z V hV).1] at ha
  exact ha

/-- A mixed gap reaching beyond the bottom two source layers makes
both of them affine in the same actual characteristic chart. -/
theorem sourceLeading_bottomLayers_secondDerivative_zero_of_mixedGap
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (hgap : m < 2*k) :
    (lineEval z V (initialForm transverseCubicWeight 0 F)).derivative.derivative = 0 ∧
      (lineEval z V (initialForm transverseCubicWeight 1 F)).derivative.derivative = 0 := by
  have h0 := sourceLeading_correction_secondDerivative_zero_of_mixedGap
    F m k m (by omega) (by omega) hcap hdet z V hV hreg hb hp hq hgap (by omega)
  have h1 := sourceLeading_correction_secondDerivative_zero_of_mixedGap
    F m k (m-1) (by omega) (by omega) hcap hdet z V hV hreg hb hp hq (by omega) (by omega)
  constructor
  · simpa only [sub_self] using h0
  · have he : (m : ℤ) - ((m-1 : ℕ) : ℤ) = 1 := by omega
    rwa [he] at h1




/-! ## Close the late-mixed-gap branch on the actual marked axis -/

private def sourceAxisTimeEval (u : K) : LineTime K →+* K :=
  _root_.Polynomial.eval₂RingHom (MvPolynomial.eval (fun _ : Fin 3 => 0)) u

private theorem sourceAxisTimeEval_C (u : K) (b : MvPolynomial (Fin 3) K) :
    sourceAxisTimeEval u (_root_.Polynomial.C b) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) b := by
  simp [sourceAxisTimeEval]

private theorem sourceAxisTimeEval_X (u : K) :
    sourceAxisTimeEval u (_root_.Polynomial.X : LineTime K) = u := by
  simp [sourceAxisTimeEval]

private theorem sourceReferenceLinearVector_eval_zero
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    MvPolynomial.eval (fun _ : Fin 3 => 0) (referenceLinearVector N i) = 0 := by
  simp [referenceLinearVector]

/-- The linear characteristic chart restricts on the marked axis
to the honest translation x = a+u. -/
private theorem sourceAxisTimeEval_linearLineEval
    (a u : K) (N : Matrix (Fin 3) (Fin 3) K) (P : StationarySource K) :
    sourceAxisTimeEval u (linearLineEval a N P) = stationaryAxisEval (a+u) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : linearLineEval a N (MvPolynomial.C c) =
        _root_.Polynomial.C (MvPolynomial.C c) := by simp [linearLineEval, lineEval]
    rw [h, sourceAxisTimeEval_C]
    simp [stationaryAxisEval]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | inl v =>
      cases v
      have h : linearLineEval a N (X (.inl ())) =
          _root_.Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin 3) K) +
            _root_.Polynomial.X := by simp [linearLineEval, lineEval]
      rw [h, map_add, sourceAxisTimeEval_C, sourceAxisTimeEval_X]
      simp [stationaryAxisEval]
    | inr i =>
      have h : linearLineEval a N (X (.inr i)) =
          _root_.Polynomial.C (X i : MvPolynomial (Fin 3) K) +
            _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
        simp [linearLineEval, lineEval, referenceLinearVector]
      rw [h, map_add, map_mul, sourceAxisTimeEval_C, sourceAxisTimeEval_C,
        sourceAxisTimeEval_X, sourceReferenceLinearVector_eval_zero]
      simp [stationaryAxisEval]

private theorem sourceAxisTimeEval_linearLineEval_derivative
    (a u : K) (N : Matrix (Fin 3) (Fin 3) K) (P : StationarySource K) :
    sourceAxisTimeEval u (linearLineEval a N P).derivative =
      stationaryAxisEval (a+u) (pderiv (.inl ()) P) := by
  classical
  let z : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
    Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
    Sum.elim (fun _ => 1) (referenceLinearVector N)
  change sourceAxisTimeEval u (lineEval z V P).derivative = _
  rw [transverse_lineEval_derivative, map_sum, Fintype.sum_sum_type]
  have he (i : Unit ⊕ Fin 3) : sourceAxisTimeEval u
      (_root_.Polynomial.C (V i) * lineEval z V (pderiv i P)) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (V i) *
        stationaryAxisEval (a+u) (pderiv i P) := by
    rw [map_mul, sourceAxisTimeEval_C]
    exact congrArg (fun c => MvPolynomial.eval (fun _ : Fin 3 => 0) (V i) * c)
      (sourceAxisTimeEval_linearLineEval a u N (pderiv i P))
  simp only [he, V, Sum.elim_inl, Sum.elim_inr, map_one, one_mul,
    sourceReferenceLinearVector_eval_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp

private theorem sourceTime_degree_le_one_of_second_zero
    (P : LineTime K) (hP : P.derivative.derivative = 0) : P.natDegree ≤ 1 := by
  have hd := _root_.Polynomial.eq_C_of_derivative_eq_zero hP
  let c := P.derivative.coeff 0
  have hzero : (P - _root_.Polynomial.C c * _root_.Polynomial.X).derivative = 0 := by
    rw [map_sub, _root_.Polynomial.derivative_C_mul_X, hd]
    exact sub_self _
  have he := _root_.Polynomial.eq_C_of_derivative_eq_zero hzero
  have hp : P = _root_.Polynomial.C ((P - _root_.Polynomial.C c *
      _root_.Polynomial.X).coeff 0) + _root_.Polynomial.C c * _root_.Polynomial.X := by
    calc
      P = (P - _root_.Polynomial.C c * _root_.Polynomial.X) +
          _root_.Polynomial.C c * _root_.Polynomial.X := by ring
      _ = _ := congrArg (fun q : LineTime K => q + _root_.Polynomial.C c *
        _root_.Polynomial.X) he
  rw [hp]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
    ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))

private theorem sourceAxisTimeEval_affine_formula
    (P : LineTime K) (hP : P.natDegree ≤ 1) (u : K) :
    sourceAxisTimeEval u P =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 0) +
        MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 1) * u := by
  have he : P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X := by
    apply _root_.Polynomial.ext
    intro n
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        have hz : P.coeff (n+2) = 0 :=
          _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simpa [_root_.Polynomial.coeff_C_mul_X, Nat.succ_eq_add_one,
          Nat.add_assoc] using hz
  calc
    _ = sourceAxisTimeEval u (_root_.Polynomial.C (P.coeff 0) +
        _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X) :=
      congrArg (sourceAxisTimeEval u) he
    _ = _ := by rw [map_add, map_mul, sourceAxisTimeEval_C,
      sourceAxisTimeEval_C, sourceAxisTimeEval_X]

private theorem sourceAxisTimeEval_affine_eq_of_endpoints
    (P Q : LineTime K) (hp : P.natDegree ≤ 1) (hq : Q.natDegree ≤ 1)
    (a : K)
    (h0 : sourceAxisTimeEval (-a) P = sourceAxisTimeEval (-a) Q)
    (h1 : sourceAxisTimeEval (1-a) P = sourceAxisTimeEval (1-a) Q) (u : K) :
    sourceAxisTimeEval u P = sourceAxisTimeEval u Q := by
  rw [sourceAxisTimeEval_affine_formula P hp, sourceAxisTimeEval_affine_formula Q hq] at h0 h1 ⊢
  have hs : MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 1) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (Q.coeff 1) := by
    linear_combination h1 - h0
  rw [hs] at h0 ⊢
  have hc : MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 0) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (Q.coeff 0) := by
    linear_combination h0
  rw [hc]

private theorem stationaryAxisEval_gradient_layer
    (F : StationarySource K) (i : Unit ⊕ Fin 3) (t : K) :
    stationaryAxisEval t (pderiv i F) =
      stationaryAxisEval t (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F)) := by
  have h := congrArg (fun p : _root_.Polynomial K => p.eval t)
    (stationaryAxisTrace_gradient_layer F i)
  simpa only [stationaryAxisTrace_eval] using h

/-- Affineness of both bottom source layers in a nilpotent
characteristic chart excludes an actual marked gradient collision.
The affine pencil is used on the original gradient, not on a
replacement Hessian determinant. -/
theorem sourceNilpotent_affineBottomLayers_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (h0 : (linearLineEval a N (initialForm transverseCubicWeight 0 F)).derivative.derivative = 0)
    (h1 : (linearLineEval a N (initialForm transverseCubicWeight 1 F)).derivative.derivative = 0) :
    False := by
  classical
  let Q0 := initialForm transverseCubicWeight 0 F
  let Q1 := initialForm transverseCubicWeight 1 F
  let P0 := linearLineEval a N Q0
  let P1 := linearLineEval a N Q1
  let G (u : K) (i : Fin 3) := stationaryAxisEval (a+u) (pderiv (.inr i) Q1)
  let c := G (-a)
  let J (u : K) := (sourceTimePencil N).map (sourceAxisTimeEval u)
  let D (j : Fin 3) := coeffDeriv (pderiv j) P1
  let R (j : Fin 3) := ∑ i : Fin 3,
    _root_.Polynomial.C (MvPolynomial.C (c i)) * sourceTimePencil N i j
  have hdegD (j : Fin 3) : (D j).natDegree ≤ 1 :=
    (sourceTime_coeffDeriv_natDegree_le (pderiv j) P1).trans
      (sourceTime_degree_le_one_of_second_zero P1 h1)
  have hdegR (j : Fin 3) : (R j).natDegree ≤ 1 := by
    apply sourceTime_natDegree_sum_le
    intro i _
    exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
      (sourceTimePencil_natDegree_le N i j)
  have hchain (u : K) : G u ᵥ* J u = fun j => sourceAxisTimeEval u (D j) := by
    funext j
    have h := congrArg (fun v : Fin 3 → LineTime K => sourceAxisTimeEval u (v j))
      (sourceLinear_referenceGradient_chain a N Q1)
    change sourceAxisTimeEval u (∑ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) Q1) * sourceTimePencil N i j) =
        sourceAxisTimeEval u (D j) at h
    rw [map_sum] at h
    simp only [map_mul, sourceAxisTimeEval_linearLineEval] at h
    exact h
  have hconst (u : K) : c ᵥ* J u = fun j => sourceAxisTimeEval u (R j) := by
    funext j
    change (∑ i : Fin 3, c i * sourceAxisTimeEval u (sourceTimePencil N i j)) =
      sourceAxisTimeEval u (∑ i : Fin 3,
        _root_.Polynomial.C (MvPolynomial.C (c i)) * sourceTimePencil N i j)
    rw [map_sum]
    simp only [map_mul, sourceAxisTimeEval_C, MvPolynomial.eval_C]
  have hG1 : G (1-a) = c := by
    funext i
    change stationaryAxisEval (a+(1-a)) (pderiv (.inr i) Q1) =
      stationaryAxisEval (a+(-a)) (pderiv (.inr i) Q1)
    rw [show a+(1-a) = 1 by ring, add_neg_cancel]
    have hl (t : K) : stationaryAxisEval t (pderiv (.inr i) F) =
        stationaryAxisEval t (pderiv (.inr i) Q1) :=
      stationaryAxisEval_gradient_layer F (.inr i) t
    rw [← hl 1, ← hl 0]
    exact hcoll (.inr i)
  have hendpoint (u : K) (hu : G u = c) (j : Fin 3) :
      sourceAxisTimeEval u (D j) = sourceAxisTimeEval u (R j) := by
    calc
      _ = (G u ᵥ* J u) j := (congrFun (hchain u) j).symm
      _ = (c ᵥ* J u) j := by rw [hu]
      _ = _ := congrFun (hconst u) j
  have hG (u : K) : G u = c := by
    have he : G u ᵥ* J u = c ᵥ* J u := by
      rw [hchain u, hconst u]
      funext j
      exact sourceAxisTimeEval_affine_eq_of_endpoints (D j) (R j)
        (hdegD j) (hdegR j) a (hendpoint (-a) rfl j)
        (hendpoint (1-a) hG1 j) u
    let S := (sourceTimePencilInv N).map (sourceAxisTimeEval u)
    have hinv : J u * S = 1 := by
      change (sourceTimePencil N).map (sourceAxisTimeEval u) *
        (sourceTimePencilInv N).map (sourceAxisTimeEval u) = _
      rw [← Matrix.map_mul, sourceTimePencil_right_inverse N hN]
      apply Matrix.ext
      intro i j
      simp [Matrix.map_apply, Matrix.one_apply]
    calc
      G u = G u ᵥ* (1 : Matrix (Fin 3) (Fin 3) K) := (Matrix.vecMul_one _).symm
      _ = G u ᵥ* (J u * S) := by rw [hinv]
      _ = (G u ᵥ* J u) ᵥ* S := (Matrix.vecMul_vecMul _ _ _).symm
      _ = (c ᵥ* J u) ᵥ* S := by rw [he]
      _ = c := by rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hlong (u : K) : stationaryAxisEval (a+u) (pderiv (.inl ()) Q0) =
      stationaryAxisEval (a+(-a)) (pderiv (.inl ()) Q0) := by
    rw [← sourceAxisTimeEval_linearLineEval_derivative,
      ← sourceAxisTimeEval_linearLineEval_derivative]
    have hc := _root_.Polynomial.eq_C_of_derivative_eq_zero h0
    rw [hc, sourceAxisTimeEval_C, sourceAxisTimeEval_C]
  have hall (i : Unit ⊕ Fin 3) (t : K) :
      stationaryAxisEval t (pderiv i F) = stationaryAxisEval 0 (pderiv i F) := by
    rw [stationaryAxisEval_gradient_layer F i t, stationaryAxisEval_gradient_layer F i 0]
    cases i with
    | inl v =>
      cases v
      have h := hlong (t-a)
      rw [show a+(t-a) = t by ring, add_neg_cancel] at h
      exact h
    | inr i =>
      have h := congrFun (hG (t-a)) i
      change stationaryAxisEval (a+(t-a)) (pderiv (.inr i) Q1) =
        stationaryAxisEval (a+(-a)) (pderiv (.inr i) Q1) at h
      rw [show a+(t-a) = t by ring, add_neg_cancel] at h
      exact h
  apply stationaryAxisTrace_rankOne_markedCollision_impossible F hδ hdet hcoll
    0 (fun _ => 0)
  intro i
  have he : stationaryAxisTrace (pderiv i F) =
      _root_.Polynomial.C (stationaryAxisEval 0 (pderiv i F)) := by
    apply _root_.Polynomial.funext
    intro t
    rw [stationaryAxisTrace_eval, _root_.Polynomial.eval_C]
    exact hall i t
  rw [he, _root_.Polynomial.derivative_C, mul_zero]

/-- The mixed block of a surviving regular nilpotent-linear marked
collision must have a nonzero correction by reverse order floor(m/2).
The order-zero block is excluded by the actual leading transport. -/
theorem sourceNilpotent_markedCollision_forces_earlyMixed
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    ∃ j : ℕ, 0 < j ∧ 2*j ≤ m ∧
      (H.b.coeff j ≠ 0 ∨ H.p.coeff j ≠ 0 ∨ H.q.coeff j ≠ 0) := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let H := sourceLeading_lineSchurFrame F m z V
  let L := initialForm transverseCubicWeight (m : ℤ) F
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  obtain ⟨hb0, hp0, hq0, hr⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hg
  change ∃ j : ℕ, 0 < j ∧ 2*j ≤ m ∧
    (H.b.coeff j ≠ 0 ∨ H.p.coeff j ≠ 0 ∨ H.q.coeff j ≠ 0)
  by_contra hn
  let k := m/2+1
  have hgap : m < 2*k := by dsimp [k]; omega
  have hzero (j : ℕ) (hj : j < k) :
      H.b.coeff j = 0 ∧ H.p.coeff j = 0 ∧ H.q.coeff j = 0 := by
    by_cases hj0 : j = 0
    · subst j
      exact ⟨hb0, hp0, hq0⟩
    · have hjm : 2*j ≤ m := by dsimp [k] at hj; omega
      have hjpos : 0 < j := by omega
      refine ⟨?_, ?_, ?_⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inl h⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inr (Or.inl h)⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inr (Or.inr h)⟩
  obtain ⟨h0, h1⟩ := sourceLeading_bottomLayers_secondDerivative_zero_of_mixedGap
    F m k hm hcap hdet z V hV hr (fun j hj => (hzero j hj).1)
    (fun j hj => (hzero j hj).2.1) (fun j hj => (hzero j hj).2.2) hgap
  exact sourceNilpotent_affineBottomLayers_markedCollision_impossible
    F hδ hdet a N hN hcoll h0 h1


end
end HC4.Polynomial.RankThreeCubic
