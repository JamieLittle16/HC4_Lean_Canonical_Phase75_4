import HC4.Polynomial.RankThreeCubicFibrePencils
import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Algebra.MvPolynomial.Funext
import HC4.MongeAmpere.SchurReduction
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Straight characteristics of the singular full Hessian

We extend polynomial partial derivations to a localization using dual
numbers. The characteristic identity is proved in an ordinary polynomial
ring using a coefficient recurrence, so no formal exponential is needed.
-/

namespace HC4.Polynomial.RankThreeCubic

noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
open nonZeroDivisors

section LocalizedDerivation

variable {K B F : Type*} [CommRing K] [CommRing B] [CommRing F]
  [Algebra K B] [Algebra B F]

private def polynomialDualJet (d : Derivation K B B) : B →+* DualNumber F where
  toFun x := (algebraMap B F x, algebraMap B F (d x))
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]

variable (M : Submonoid B) [IsLocalization M F]

private def localizationDualJet (d : Derivation K B B) : F →+* DualNumber F :=
  IsLocalization.lift (M := M) (g := polynomialDualJet (F := F) d) fun b => by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    exact IsLocalization.map_units F b

private theorem localizationDualJet_algebraMap (d : Derivation K B B) (x : B) :
    localizationDualJet (F := F) M d (algebraMap B F x) = polynomialDualJet d x :=
  IsLocalization.lift_eq _ x

private theorem localizationDualJet_fst (d : Derivation K B B) (x : F) :
    (localizationDualJet M d x).fst = x := by
  have h : ((TrivSqZeroExt.fstHom F F F).toRingHom).comp (localizationDualJet M d) =
      RingHom.id F := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro y
    change (localizationDualJet M d (algebraMap B F y)).fst = algebraMap B F y
    rw [localizationDualJet_algebraMap]
    rfl
  exact RingHom.congr_fun h x

variable [Algebra K F] [IsScalarTower K B F]

/-- Extend a derivation to a localization by taking the second component
of its unique lift to dual numbers. -/
def localizationDerivation (d : Derivation K B B) : Derivation K F F where
  toFun x := (localizationDualJet M d x).snd
  map_add' x y := by simp
  map_smul' k x := by
    have h : localizationDualJet M d (algebraMap K F k) =
        (algebraMap K F k, 0) := by
      rw [IsScalarTower.algebraMap_apply K B F, localizationDualJet_algebraMap]
      simp [polynomialDualJet, Derivation.map_algebraMap]
    simp [Algebra.smul_def, h]
  map_one_eq_zero' := by simp
  leibniz' x y := by
    simp [smul_eq_mul, localizationDualJet_fst, mul_comm]

@[simp]
theorem localizationDerivation_algebraMap (d : Derivation K B B) (x : B) :
    localizationDerivation (F := F) M d (algebraMap B F x) = algebraMap B F (d x) := by
  change (localizationDualJet M d (algebraMap B F x)).snd = _
  rw [localizationDualJet_algebraMap]
  rfl

end LocalizedDerivation

section StraightLine

variable {K F ι : Type*} [CommRing K] [CommRing F] [Algebra K F]

def coeffDeriv (D : Derivation K F F) :
    Derivation K (_root_.Polynomial F) (_root_.Polynomial F) :=
  (_root_.PolynomialModule.equivPolynomialSelf.toLinearMap.compDer D.mapCoeffs)

@[simp]
theorem coeff_coeffDeriv (D : Derivation K F F) (p : _root_.Polynomial F)
    (n : ℕ) : (coeffDeriv D p).coeff n = D (p.coeff n) := rfl

/-- Polynomial substitution along an affine line over the coefficient
field. The indeterminate is the characteristic time. -/
def lineEval (z V : ι → F) : MvPolynomial ι K →ₐ[K] _root_.Polynomial F :=
  MvPolynomial.aeval fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (V i) * _root_.Polynomial.X

/-- If the velocity is constant under the directional derivation, a
polynomial killed by that derivation is constant along the line. -/
theorem lineEval_eq_C_of_derivation_eq_zero [IsDomain F] [CharZero F]
    (D : Derivation K F F) (z V : ι → F)
    (hz : ∀ i, D (z i) = V i) (hV : ∀ i, D (V i) = 0)
    (p : MvPolynomial ι K) (hp : D (MvPolynomial.aeval z p) = 0) :
    lineEval z V p = _root_.Polynomial.C (MvPolynomial.aeval z p) := by
  classical
  let E := lineEval (K := K) z V
  have heq : (E p).derivative = coeffDeriv D (E p) := by
    clear hp
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show E (MvPolynomial.C a) = _root_.Polynomial.C (algebraMap K F a) by
        simp [E, lineEval, IsScalarTower.algebraMap_apply K F (_root_.Polynomial F),
          _root_.Polynomial.algebraMap_eq]]
      ext n
      simp [coeff_coeffDeriv, _root_.Polynomial.coeff_C, apply_ite D, Derivation.map_algebraMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      have hX : E (MvPolynomial.X i) =
          _root_.Polynomial.C (z i) + _root_.Polynomial.C (V i) * _root_.Polynomial.X := by
        simp [E, lineEval]
      have hDX : (E (MvPolynomial.X i)).derivative = coeffDeriv D (E (MvPolynomial.X i)) := by
        rw [hX]
        ext n
        simp only [map_add, _root_.Polynomial.derivative_C, _root_.Polynomial.derivative_mul,
          _root_.Polynomial.derivative_X, zero_mul, mul_one, zero_add, add_zero, coeff_coeffDeriv,
          _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul_X, _root_.Polynomial.coeff_C,
          apply_ite D, map_add, map_zero, hz, hV, ite_self, add_zero]
      simp only [map_mul, _root_.Polynomial.derivative_mul, Derivation.leibniz, smul_eq_mul, hp, hDX]
      ring
  have evEq : (_root_.Polynomial.constantCoeff.comp E.toRingHom) =
      (MvPolynomial.aeval z : MvPolynomial ι K →ₐ[K] F).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, lineEval, IsScalarTower.algebraMap_apply K F (_root_.Polynomial F),
        _root_.Polynomial.algebraMap_eq]
    · intro i
      simp [E, lineEval]
  have h0 : (E p).coeff 0 = MvPolynomial.aeval z p := RingHom.congr_fun evEq p
  have hzero (n : ℕ) : (E p).coeff (n + 1) = 0 := by
    induction n with
    | zero =>
      have h := congrArg (fun f : _root_.Polynomial F => f.coeff 0) heq
      simpa [_root_.Polynomial.coeff_derivative, h0, hp] using h
    | succ n ih =>
      have h := congrArg (fun f : _root_.Polynomial F => f.coeff (n + 1)) heq
      simp only [_root_.Polynomial.coeff_derivative, coeff_coeffDeriv, ih, map_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast Nat.succ_ne_zero (n + 1))
  have hC : E p = _root_.Polynomial.C ((E p).coeff 0) := by
    ext (_ | n)
    · simp
    · simpa using hzero n
  rw [h0] at hC
  exact hC

end StraightLine

section BlockKernel

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

/-- A singular bordered matrix with invertible transverse block has a
kernel vector normalised to one in the longitudinal coordinate. -/
theorem exists_normalizedKernel
    (H : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A)
    (hH : H.det = 0)
    (hM : IsUnit (H.submatrix Sum.inr Sum.inr).det) :
    ∃ V : Unit ⊕ ι → A, V (.inl ()) = 1 ∧ H *ᵥ V = 0 := by
  classical
  let a := H.submatrix Sum.inl Sum.inl
  let b := H.submatrix Sum.inl Sum.inr
  let c := H.submatrix Sum.inr Sum.inl
  let M := H.submatrix Sum.inr Sum.inr
  letI : Invertible M := (Matrix.isUnit_iff_isUnit_det M |>.mpr hM).invertible
  have hb : Matrix.fromBlocks a b c M = H := by
    ext i j
    cases i <;> cases j <;> rfl
  have hschur : a - b * ⅟ M * c = 0 := by
    have h := HC4.MongeAmpere.det_fromBlocks_schur₂₂ a b c M
    rw [hb, hH, HC4.MongeAmpere.schur₂₂] at h
    have hd : (a - b * ⅟ M * c).det = 0 :=
      hM.mul_right_inj.mp (by change M.det * _ = M.det * 0; rw [mul_zero, ← h])
    ext i j
    cases i
    cases j
    simpa [Matrix.det_unique] using hd
  let e : Unit → A := fun _ => 1
  let V : Unit ⊕ ι → A := Sum.elim e (-((⅟ M * c) *ᵥ e))
  refine ⟨V, rfl, ?_⟩
  rw [← hb, Matrix.fromBlocks_mulVec]
  have htop : a *ᵥ e + b *ᵥ (-((⅟ M * c) *ᵥ e)) = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← sub_eq_add_neg,
      ← Matrix.sub_mulVec, ← Matrix.mul_assoc, hschur, Matrix.zero_mulVec]
  have hbottom : c *ᵥ e + M *ᵥ (-((⅟ M * c) *ᵥ e)) = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul,
      add_neg_cancel]
  change Sum.elim (a *ᵥ e + b *ᵥ (-((⅟ M * c) *ᵥ e)))
    (c *ᵥ e + M *ᵥ (-((⅟ M * c) *ᵥ e))) = 0
  rw [htop, hbottom]
  funext i
  cases i <;> rfl

/-- A kernel vector with zero longitudinal component must vanish when
the transverse block is invertible. -/
theorem eq_zero_of_transverseKernel
    (H : Matrix (Unit ⊕ ι) (Unit ⊕ ι) A)
    (hM : IsUnit (H.submatrix Sum.inr Sum.inr).det)
    (W : Unit ⊕ ι → A) (hW : W (.inl ()) = 0) (hker : H *ᵥ W = 0) :
    W = 0 := by
  classical
  let M := H.submatrix Sum.inr Sum.inr
  letI : Invertible M := (Matrix.isUnit_iff_isUnit_det M |>.mpr hM).invertible
  have htrans : M *ᵥ (W ∘ Sum.inr) = 0 := by
    funext i
    have h := congrFun hker (.inr i)
    simpa [M, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hW] using h
  have hz : W ∘ Sum.inr = 0 := by
    have h := congrArg (fun z => ⅟ M *ᵥ z) htrans
    simpa [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec] using h
  funext i
  cases i with
  | inl j => cases j; exact hW
  | inr j => exact congrFun hz j

end BlockKernel

section Source

variable {K ι S : Type*} [Field K] [Fintype ι] [DecidableEq ι]
  [CommRing S] [IsDomain S] [CharZero S] [Algebra K S]
  [Algebra (MvPolynomial (Unit ⊕ ι) K) S]
  [IsScalarTower K (MvPolynomial (Unit ⊕ ι) K) S]

/-- The actual polynomial gradient is invariant along the affine line
in the normalised Hessian-kernel direction. The theorem works in any
localization in which the transverse Hessian determinant is a unit. -/
theorem exists_lineEval_gradient_eq
    (N : Submonoid (MvPolynomial (Unit ⊕ ι) K)) [IsLocalization N S]
    (L : MvPolynomial (Unit ⊕ ι) K)
    (hL : (HC4.Polynomial.hessian L).det = 0)
    (htrans : IsUnit (algebraMap (MvPolynomial (Unit ⊕ ι) K) S
      ((HC4.Polynomial.hessian L).submatrix Sum.inr Sum.inr).det)) :
    ∃ V : Unit ⊕ ι → S, V (.inl ()) = 1 ∧
      ∀ i, lineEval (fun j => algebraMap (MvPolynomial (Unit ⊕ ι) K) S (X j)) V
        (pderiv i L) = _root_.Polynomial.C
          (algebraMap (MvPolynomial (Unit ⊕ ι) K) S (pderiv i L)) := by
  classical
  let g := algebraMap (MvPolynomial (Unit ⊕ ι) K) S
  let z : Unit ⊕ ι → S := fun i => g (X i)
  let H := (HC4.Polynomial.hessian L).map g
  let d : Unit ⊕ ι → Derivation K S S := fun i => localizationDerivation N (pderiv i)
  have hd (i) (p : MvPolynomial (Unit ⊕ ι) K) : d i (g p) = g (pderiv i p) :=
    localizationDerivation_algebraMap N _ _
  have hHd : H.det = 0 := by simpa [H, RingHom.map_det] using congrArg g hL
  have hM : IsUnit (H.submatrix Sum.inr Sum.inr).det := by
    have he : H.submatrix Sum.inr Sum.inr =
        ((HC4.Polynomial.hessian L).submatrix Sum.inr Sum.inr).map g := rfl
    rw [he]
    change IsUnit (g.mapMatrix _).det
    rw [← RingHom.map_det]
    exact htrans
  obtain ⟨V, hV0, hker⟩ := exists_normalizedKernel H hHd hM
  have hker' (i) : ∑ j, H i j * V j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hker i
  have hs (i j) : H i j = H j i := by
    change g (pderiv j (pderiv i L)) = g (pderiv i (pderiv j L))
    rw [HC4.Newton.pderiv_comm_backport]
  have ht (i j k) : d k (H i j) = d i (H k j) := by
    change d k (g (pderiv j (pderiv i L))) = d i (g (pderiv j (pderiv k L)))
    rw [hd, hd, HC4.Newton.pderiv_comm_backport k j, HC4.Newton.pderiv_comm_backport i j,
      HC4.Newton.pderiv_comm_backport k i]
  let D : Derivation K S S := ∑ i, V i • d i
  have hD (x : S) : D x = ∑ i, V i * d i x := by
    change Derivation.coeFnAddMonoidHom D x = _
    simp only [D, map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply, smul_eq_mul]
  have hacc : H *ᵥ (fun i => D (V i)) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, hD, Pi.zero_apply]
    exact hessianKernel_acceleration d H V hs ht hker' i
  have hD0 (i) : D (V i) = 0 := by
    have h := eq_zero_of_transverseKernel H hM (fun j => D (V j))
      (by simp [hV0]) hacc
    exact congrFun h i
  have hz (i) : D (z i) = V i := by
    simp only [z, hD, hd, pderiv_X]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hg (p : MvPolynomial (Unit ⊕ ι) K) : MvPolynomial.aeval z p = g p := by
    let f := IsScalarTower.toAlgHom K (MvPolynomial (Unit ⊕ ι) K) S
    have he : MvPolynomial.aeval z = f := by ext i; simp [z, f, g]
    exact AlgHom.congr_fun he p
  refine ⟨V, hV0, fun i => ?_⟩
  have hp : D (MvPolynomial.aeval z (pderiv i L)) = 0 := by
    rw [hg, hD]
    simp_rw [hd, mul_comm (V _)]
    exact hker' i
  simpa only [hg] using lineEval_eq_C_of_derivation_eq_zero D z V hz hD0 (pderiv i L) hp

end Source

section Anchored

variable {K ι F : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
  [Field F] [Algebra K F]

/-- Anchor the characteristic at any evaluation where the transverse
determinant is nonzero. In particular the evaluation may send the
longitudinal variable to zero and the transverse variables to
indeterminates in their fraction field. -/
theorem exists_anchored_lineEval_gradient_eq
    (L : MvPolynomial (Unit ⊕ ι) K)
    (hL : (HC4.Polynomial.hessian L).det = 0)
    (P : Unit ⊕ ι → F)
    (hP : MvPolynomial.aeval P
      ((HC4.Polynomial.hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    ∃ V : Unit ⊕ ι → F, V (.inl ()) = 1 ∧
      ∀ i, lineEval P V (pderiv i L) = _root_.Polynomial.C (MvPolynomial.aeval P (pderiv i L)) := by
  classical
  let B := MvPolynomial (Unit ⊕ ι) K
  let Δ := ((HC4.Polynomial.hessian L).submatrix Sum.inr Sum.inr).det
  let S := Localization.Away Δ
  have hΔ : Δ ≠ 0 := by
    intro he
    apply hP
    change MvPolynomial.aeval P Δ = 0
    rw [he, map_zero]
  have hpow := powers_le_nonZeroDivisors_of_noZeroDivisors hΔ
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hpow
  letI : CharZero S := charZero_of_injective_algebraMap
    (IsLocalization.injective S hpow)
  obtain ⟨U, hU, hline⟩ := exists_lineEval_gradient_eq (S := S) (Submonoid.powers Δ) L hL
    (IsLocalization.Away.algebraMap_isUnit Δ)
  let φ : S →+* F := IsLocalization.Away.lift Δ (g := (MvPolynomial.aeval P).toRingHom)
    (isUnit_iff_ne_zero.mpr hP)
  have hφ (p : B) : φ (algebraMap B S p) = MvPolynomial.aeval P p :=
    IsLocalization.Away.lift_eq Δ _ p
  let g := algebraMap B S
  let z : Unit ⊕ ι → S := fun i => g (X i)
  let V : Unit ⊕ ι → F := φ ∘ U
  have hmap : (_root_.Polynomial.mapRingHom φ).comp (lineEval z U).toRingHom =
      (lineEval (K := K) P V).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change _root_.Polynomial.mapRingHom φ
        ((lineEval (K := K) z U) (MvPolynomial.C a)) =
          (lineEval (K := K) P V) (MvPolynomial.C a)
      have ha : φ (algebraMap K S a) = algebraMap K F a := by
        rw [IsScalarTower.algebraMap_apply K B S]
        simpa [B] using hφ (algebraMap K B a)
      simp [lineEval, IsScalarTower.algebraMap_apply K S (_root_.Polynomial S),
        IsScalarTower.algebraMap_apply K F (_root_.Polynomial F),
        _root_.Polynomial.algebraMap_eq, ha]
    · intro i
      change _root_.Polynomial.mapRingHom φ ((lineEval (K := K) z U) (X i)) =
        (lineEval (K := K) P V) (X i)
      simp [lineEval, z, V, g, hφ]
  refine ⟨V, by simp [V, hU], fun i => ?_⟩
  have h := congrArg (_root_.Polynomial.mapRingHom φ) (hline i)
  rw [show _root_.Polynomial.mapRingHom φ (lineEval z U (pderiv i L)) =
    lineEval P V (pderiv i L) from RingHom.congr_fun hmap (pderiv i L)] at h
  change lineEval P V (pderiv i L) =
    _root_.Polynomial.map φ (_root_.Polynomial.C (algebraMap B S (pderiv i L))) at h
  rw [_root_.Polynomial.map_C, hφ] at h
  exact h

end Anchored

section TransverseCubic

variable {K : Type*} [Field K]

/-- The longitudinal variable has weight zero and the three transverse
variables have weight one. -/
def transverseCubicWeight : Unit ⊕ Fin 3 → ℤ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- The actual cubic grade of a cap-three constant determinant source
has singular full Hessian, obtained from weight six. -/
theorem transverseCubic_hessian_det_eq_zero
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    (hessian (initialForm transverseCubicWeight 3 F)).det = 0 := by
  have he := initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    transverseCubicWeight 3 F hcap
  have hw : (Fintype.card (Unit ⊕ Fin 3) : ℤ) * 3 -
      2 * ∑ i, transverseCubicWeight i = 6 := by decide
  rw [hw, hdet, initialForm_eq_zero_of_isWeightedHomogeneous
    (MvPolynomial.isWeightedHomogeneous_C transverseCubicWeight δ) 6 (by norm_num)] at he
  exact he.symm

/-- A point with longitudinal coordinate in the ground field and
transverse coordinates the three indeterminates. -/
def transverseGenericPoint (a : K) :
    Unit ⊕ Fin 3 → FractionRing (MvPolynomial (Fin 3) K) :=
  Sum.elim (fun _ => algebraMap K _ a) (fun j => algebraMap (MvPolynomial (Fin 3) K) _ (X j))

/-- A nonzero polynomial admits a longitudinal ground-field
specialization that is still nonzero at the generic transverse point. -/
theorem exists_regular_transverseGenericPoint [Infinite K]
    {p : MvPolynomial (Unit ⊕ Fin 3) K} (hp : p ≠ 0) :
    ∃ a : K, MvPolynomial.aeval (transverseGenericPoint a) p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro v
  let B := MvPolynomial (Fin 3) K
  let f := IsScalarTower.toAlgHom K B (FractionRing B)
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C (v (.inl ()))) X
  have hz (i) : f (z i) = transverseGenericPoint (v (.inl ())) i := by
    cases i with
    | inl j => exact f.commutes (v (.inl ()))
    | inr j => rfl
  have hz' : MvPolynomial.aeval z p = 0 := by
    apply IsFractionRing.injective B (FractionRing B)
    change f (MvPolynomial.aeval z p) = f 0
    rw [MvPolynomial.comp_aeval_apply, map_zero]
    simpa only [hz] using h (v (.inl ()))
  let e : B →ₐ[K] K := MvPolynomial.aeval (fun i : Fin 3 => v (.inr i))
  have he := congrArg e hz'
  rw [MvPolynomial.comp_aeval_apply, map_zero] at he
  have hv : (fun i => e (z i)) = v := by
    funext i
    cases i with
    | inl i =>
      cases i
      exact e.commutes (v (.inl ()))
    | inr i =>
      exact MvPolynomial.aeval_X (f := fun j : Fin 3 => v (.inr j)) i
  rw [hv] at he
  rw [map_zero]
  simpa [MvPolynomial.coe_aeval_eq_eval] using he

/-- The straight characteristic identity (1) on the actual cubic
grade, at a longitudinal origin where the transverse block is
generically invertible. -/
theorem exists_transverseCubic_characteristic_at [CharZero K]
    (a : K) (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ V : Unit ⊕ Fin 3 → FractionRing (MvPolynomial (Fin 3) K), V (.inl ()) = 1 ∧
      ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
        _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)) :=
  exists_anchored_lineEval_gradient_eq _ (transverseCubic_hessian_det_eq_zero F hcap hdet)
    (transverseGenericPoint a) htrans

/-- A source with full transverse rank on its cubic grade admits the
straight characteristic at a suitable longitudinal basepoint. -/
theorem exists_transverseCubic_characteristic [CharZero K]
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FractionRing (MvPolynomial (Fin 3) K)), V (.inl ()) = 1 ∧
      ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
        _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)) := by
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  exact ⟨a, exists_transverseCubic_characteristic_at a F hcap hdet ha⟩

end TransverseCubic

end
end HC4.Polynomial.RankThreeCubic
