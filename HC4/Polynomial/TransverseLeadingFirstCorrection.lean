import HC4.Polynomial.TransverseLeadingFixedPower
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import HC4.Polynomial.RankThreeCubicPoleJacobiBridge
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.ParameterGapSecondJet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import Mathlib.Tactic
import HC4.Polynomial.TransverseLeadingSchurFoundation
import HC4.Polynomial.TransverseLeadingStationary
import HC4.Polynomial.TransverseLeadingNilpotent
import HC4.Polynomial.TransverseLeadingCorrectionDegree
import HC4.Polynomial.TransverseLeadingMarkedCollision

/-!
# Transverse mixed-pole and directional rigidity endpoints

Imports the leading Schur, stationary, nilpotent, correction-degree and
marked-collision modules. Retains prime-factor cancellation, mixed-pole
assembly and the active directional rigidity frontier.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton HC4.Valuation
open scoped BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [CharZero K]

open MvPolynomial

private abbrev StationarySource (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

private abbrev StationaryExponent := (Unit ⊕ Fin 3) →₀ ℕ

private abbrev LineTime (K : Type*) [Field K] :=
  _root_.Polynomial (MvPolynomial (Fin 3) K)

/-! ## Prime-factor cancellation for the actual mixed row

The square of each Cramer numerator is zero on a prime determinant
component on which the mixed quadratic pairing vanishes. This works
even if every cofactor vanishes there; no principal pivot is required.
-/

/-- Over a singular symmetric ternary matrix, the Cramer numerator
square equals the corresponding diagonal cofactor times the
quadratic pairing. This identity needs no domain or rank assumption. -/
theorem singular_symmetric_adjugate_mulVec_square
    {R : Type*} [CommRing R]
    (T : Matrix (Fin 3) (Fin 3) R)
    (hsym : T.IsSymm) (hdet : T.det = 0)
    (b : Fin 3 → R) (i : Fin 3) :
    ((T.adjugate *ᵥ b) i)^2 =
      T.adjugate i i *
        (∑ j : Fin 3, ∑ l : Fin 3, b j * T.adjugate j l * b l) := by
  classical
  let A := T.adjugate
  have ha : A.IsSymm := by
    change T.adjugate.transpose = T.adjugate
    rw [Matrix.adjugate_transpose, hsym]
  have hc (j l : Fin 3) : A i i * A j l = A j i * A i l :=
    adjugate_rankOne_cross_products T hdet i j l
  change ((A *ᵥ b) i)^2 = _
  calc
    _ = ∑ j : Fin 3, ∑ l : Fin 3, (A i j * b j) * (A i l * b l) := by
      simp only [Matrix.mulVec, dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ l : Fin 3, A i i * (b j * A j l * b l) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [show A i j = A j i from ha.apply j i]
      rw [show (A j i * b j) * (A i l * b l) =
        b j * (A j i * A i l) * b l by ring, ← hc j l]
      ring
    _ = _ := by simp only [A, Finset.mul_sum]

/-- Divisibility modulo a possibly nonreduced principal ideal. The
full power of the determinant is retained in the squared Cramer
numerator, not merely the radical of the determinant. -/
theorem dvd_adjugate_mulVec_square_of_dvd_mixed_pairing
    {R : Type*} [CommRing R]
    (T : Matrix (Fin 3) (Fin 3) R) (hsym : T.IsSymm)
    (b : Fin 3 → R) (d : R)
    (hdet : d ∣ T.det)
    (hpair : d ∣ ∑ j : Fin 3, ∑ l : Fin 3,
      b j * T.adjugate j l * b l) :
    ∀ i : Fin 3, d ∣ ((T.adjugate *ᵥ b) i)^2 := by
  classical
  let I : Ideal R := Ideal.span {d}
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  let M := T.map q
  let v : Fin 3 → R ⧸ I := fun j => q (b j)
  have hz (x : R) (hx : d ∣ x) : q x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)
  have hM : M.det = 0 := by
    change (q.mapMatrix T).det = 0
    rw [← RingHom.map_det]
    exact hz _ hdet
  have hS : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change q (T j i) = q (T i j)
    exact congrArg q (hsym.apply i j)
  have hAdj : M.adjugate = T.adjugate.map q := (q.map_adjugate T).symm
  have hP : (∑ j : Fin 3, ∑ l : Fin 3, v j * M.adjugate j l * v l) = 0 := by
    rw [hAdj]
    have h := hz _ hpair
    simpa only [map_sum, map_mul, Matrix.map_apply, v] using h
  intro i
  have he := singular_symmetric_adjugate_mulVec_square M hS hM v i
  rw [hP, mul_zero] at he
  have hv : (M.adjugate *ᵥ v) i = q ((T.adjugate *ᵥ b) i) := by
    rw [hAdj]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, v, map_sum, map_mul]
  rw [hv, ← map_pow] at he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

/-- Every prime divisor of both the transverse determinant and the
mixed quadratic pairing divides each Cramer numerator. In particular
a simple determinant factor cannot be a denominator of the mixed
Schur solution. The argument is valid for repeated factors as well,
but cancels only one copy without further information. -/
theorem prime_dvd_adjugate_mulVec_of_dvd_mixed_pairing
    {R : Type*} [CommRing R]
    (T : Matrix (Fin 3) (Fin 3) R) (hsym : T.IsSymm)
    (b : Fin 3 → R) (p : R) (hp : Prime p)
    (hdet : p ∣ T.det)
    (hpair : p ∣ ∑ j : Fin 3, ∑ l : Fin 3,
      b j * T.adjugate j l * b l) :
    ∀ i : Fin 3, p ∣ (T.adjugate *ᵥ b) i := by
  intro i
  exact hp.dvd_of_dvd_pow (n := 2)
    (dvd_adjugate_mulVec_square_of_dvd_mixed_pairing T hsym b p hdet hpair i)

/-- Extract an odd prime-power bound on a square. This is the
valuation inequality 2 v_p(s) >= 2*n+1, proved by cancellation
without choosing a factorization or a valuation normalization. -/
theorem prime_pow_succ_dvd_of_odd_pow_dvd_square
    {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (hp : Prime p) (n : ℕ) (s : R)
    (h : p^(2*n+1) ∣ s^2) :
    p^(n+1) ∣ s := by
  induction n generalizing s with
  | zero =>
    have hd : p ∣ s^2 := by simpa using h
    simpa using hp.dvd_of_dvd_pow (n := 2) hd
  | succ n ih =>
    have hd : p ∣ s^2 := dvd_trans
      (by simpa only [pow_one] using
        (pow_dvd_pow p (by omega : 1 ≤ 2*(n+1)+1))) h
    obtain ⟨r, hr⟩ := hp.dvd_of_dvd_pow (n := 2) hd
    obtain ⟨c, hc⟩ := h
    have he : p^2 * r^2 = p^2 * (p^(2*n+1)*c) := by
      calc
        _ = s^2 := by rw [hr]; ring
        _ = p^(2*(n+1)+1)*c := hc
        _ = _ := by
          rw [show 2*(n+1)+1 = 2+(2*n+1) by omega, pow_add]
          ring
    have hr2 : p^(2*n+1) ∣ r^2 :=
      ⟨c, mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero) he⟩
    obtain ⟨q, hq⟩ := ih r hr2
    refine ⟨q, ?_⟩
    rw [hr, hq, pow_succ']
    ring

/-- Apply full-power squared numerator divisibility to the actual first mixed-gap endpoint
in the regular source characteristic chart. The vector is the
three entries of the genuine Schur mixed row, not an auxiliary
choice of Cramer numerator. -/
theorem sourceLeading_mixedGap_dvd_Cramer_square
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 2 ≤ m)
    (hk : 2*k ≤ m) (hc : 2*k < 4*m-6)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (p : _root_.Polynomial E)
    (hpdet : p ∣ (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0) :
    let H := sourceLeading_lineSchurFrame F m z V
    let T := (lineEval z V).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix Sum.inr Sum.inr)
    let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff k, H.p.coeff k, H.q.coeff k]
    ∀ i : Fin 3, p ∣ ((T.adjugate *ᵥ b) i)^2 := by
  classical
  let H := sourceLeading_lineSchurFrame F m z V
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let T := (lineEval z V).toRingHom.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)
  let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff k, H.p.coeff k, H.q.coeff k]
  let U : GeneralFourBlock (_root_.Polynomial E) :=
    { a := 0, b := H.b.coeff k, p := H.p.coeff k, q := H.q.coeff k,
      d := H.d.coeff 0, r := H.r.coeff 0, s := H.s.coeff 0,
      x := H.x.coeff 0, y := H.y.coeff 0, z := H.z.coeff 0 }
  have hsym (i j : Fin 3) : T i j = T j i := by
    change lineEval z V (pderiv (.inr j) (pderiv (.inr i) L)) =
      lineEval z V (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have hs : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hsym j i
  have he := sourceLeading_lineSchurFrame_coeff F m 0 (Nat.zero_le m) z V
  simp only [Nat.cast_zero, sub_zero] at he
  have hu : transverseSchurMixed U =
      ∑ i : Fin 3, ∑ j : Fin 3, b i * T.adjugate i j * b j := by
    apply sourceLineFrame_mixed_adjugate U T <;> try exact hsym
    · exact congrArg GeneralFourBlock.d he
    · exact congrArg GeneralFourBlock.r he
    · exact congrArg GeneralFourBlock.s he
    · exact congrArg GeneralFourBlock.x he
    · exact congrArg GeneralFourBlock.y he
    · exact congrArg GeneralFourBlock.z he
  have hT : (transverseSchurDet H).coeff 0 = T.det := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (lineEval z V).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
  have hP : p ∣ transverseSchurMixed U := by
    have hODE := sourceLeading_mixedGap_endpoint_lineODE
      F m k hm hk hc hcap hdet z V hV hreg hb hp hq
    change (lineEval z V (initialForm transverseCubicWeight ((m : ℤ)-((2*k : ℕ) : ℤ)) F)).derivative.derivative *
      (transverseSchurDet H).coeff 0 = transverseSchurMixed U at hODE
    rw [← hODE]
    exact dvd_mul_of_dvd_right hpdet _
  change ∀ i : Fin 3, p ∣ ((T.adjugate *ᵥ b) i)^2
  apply dvd_adjugate_mulVec_square_of_dvd_mixed_pairing T hs b p
  · rw [← hT]
    exact hpdet
  · rw [← hu]
    exact hP


/-- Apply prime cancellation to the actual first mixed-gap endpoint
in the regular source characteristic chart. The vector is the
three entries of the genuine Schur mixed row, not an auxiliary
choice of Cramer numerator. -/
theorem sourceLeading_mixedGap_prime_dvd_Cramer
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 2 ≤ m)
    (hk : 2*k ≤ m) (hc : 2*k < 4*m-6)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (p : _root_.Polynomial E) (hprime : Prime p)
    (hpdet : p ∣ (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0) :
    let H := sourceLeading_lineSchurFrame F m z V
    let T := (lineEval z V).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix Sum.inr Sum.inr)
    let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff k, H.p.coeff k, H.q.coeff k]
    ∀ i : Fin 3, p ∣ (T.adjugate *ᵥ b) i := by
  dsimp only
  intro i
  exact hprime.dvd_of_dvd_pow (n := 2)
    (sourceLeading_mixedGap_dvd_Cramer_square F m k hm hk hc hcap hdet
      z V hV hreg hb hp hq p hpdet i)

/-- A determinant factor of multiplicity at least 2*n+1 cancels
at least n+1 copies in every actual first mixed Cramer numerator.
In the cubic triple-factor branch this leaves at most a simple pole. -/
theorem sourceLeading_mixedGap_prime_pow_dvd_Cramer
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 2 ≤ m)
    (hk : 2*k ≤ m) (hc : 2*k < 4*m-6)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (p : _root_.Polynomial E) (hprime : Prime p) (n : ℕ)
    (hpdet : p^(2*n+1) ∣ (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0) :
    let H := sourceLeading_lineSchurFrame F m z V
    let T := (lineEval z V).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix Sum.inr Sum.inr)
    let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff k, H.p.coeff k, H.q.coeff k]
    ∀ i : Fin 3, p^(n+1) ∣ (T.adjugate *ᵥ b) i := by
  dsimp only
  intro i
  exact prime_pow_succ_dvd_of_odd_pow_dvd_square p hprime n _
    (sourceLeading_mixedGap_dvd_Cramer_square F m k hm hk hc hcap hdet
      z V hV hreg hb hp hq (p^(2*n+1)) hpdet i)




/-! ## Next-order obstruction for a cleared simple mixed pole

A constant-in-Rees-time scaled solution v of C₀ v = p B₁
allows a denominator-free shear of the first frame column.
Its mixed entries vanish through order one, forcing its
longitudinal entry to vanish through order three. The third
coefficient tests the first transverse repair against v.
-/

section ClearedMixedPole

variable {R : Type*} [CommRing R] [IsDomain R]
local notation "RP" => _root_.Polynomial R
local notation "PC" => _root_.Polynomial.C
local notation "PX" => _root_.Polynomial.X

/-- Cleared congruence with first column (p,-s*u,-s*v,-s*w).
Its determinant scales by p²; no invertibility is assumed. -/
private def mixedPoleClearedFrame (H : GeneralFourBlock RP) (p u v w : R) :
    GeneralFourBlock RP where
  a := PC (p*p) * H.a -
    PX * (PC (2*p) * (PC u * H.b + PC v * H.p + PC w * H.q)) +
    PX * (PX * (PC (u*u) * H.d + PC (v*v) * H.x + PC (w*w) * H.z +
      PC (2*u*v) * H.r + PC (2*u*w) * H.s + PC (2*v*w) * H.y))
  b := PC p * H.b - PX * (PC u * H.d + PC v * H.r + PC w * H.s)
  p := PC p * H.p - PX * (PC u * H.r + PC v * H.x + PC w * H.y)
  q := PC p * H.q - PX * (PC u * H.s + PC v * H.y + PC w * H.z)
  d := H.d
  r := H.r
  s := H.s
  x := H.x
  y := H.y
  z := H.z

private theorem mixedPoleClearedFrame_det (H : GeneralFourBlock RP) (p u v w : R) :
    (mixedPoleClearedFrame H p u v w).determinantCore =
      PC (p*p) * H.determinantCore := by
  unfold mixedPoleClearedFrame GeneralFourBlock.determinantCore
  simp only [map_mul, map_ofNat]
  ring

/-- The next Schur coefficient forces a cleared simple-pole residue
to be isotropic against the actual first transverse repair modulo
its denominator. This uses order three, not just the order-two
quadratic-pairing constraint. -/
theorem transverseSchur_clearedMixedPole_repair_dvd
    (H : GeneralFourBlock RP) (p u v w : R)
    (hreg : (transverseSchurDet H).coeff 0 ≠ 0)
    (hb : H.b.coeff 0 = 0) (hp : H.p.coeff 0 = 0) (hq : H.q.coeff 0 = 0)
    (hu : u*H.d.coeff 0 + v*H.r.coeff 0 + w*H.s.coeff 0 = p*H.b.coeff 1)
    (hv : u*H.r.coeff 0 + v*H.x.coeff 0 + w*H.y.coeff 0 = p*H.p.coeff 1)
    (hw : u*H.s.coeff 0 + v*H.y.coeff 0 + w*H.z.coeff 0 = p*H.q.coeff 1)
    (hdet : ∀ j < 4, H.determinantCore.coeff j = 0) :
    p ∣ u*u*H.d.coeff 1 + v*v*H.x.coeff 1 + w*w*H.z.coeff 1 +
      2*u*v*H.r.coeff 1 + 2*u*w*H.s.coeff 1 + 2*v*w*H.y.coeff 1 := by
  let J := mixedPoleClearedFrame H p u v w
  have hJdet (j : ℕ) (hj : j < 4) : J.determinantCore.coeff j = 0 := by
    change (mixedPoleClearedFrame H p u v w).determinantCore.coeff j = 0
    rw [mixedPoleClearedFrame_det, _root_.Polynomial.coeff_C_mul, hdet j hj, mul_zero]
  have hJreg : (transverseSchurDet J).coeff 0 ≠ 0 := hreg
  have hb0 : J.b.coeff 0 = 0 := by
    simp [J, mixedPoleClearedFrame, _root_.Polynomial.coeff_sub,
      _root_.Polynomial.coeff_C_mul, hb]
  have hp0 : J.p.coeff 0 = 0 := by
    simp [J, mixedPoleClearedFrame, _root_.Polynomial.coeff_sub,
      _root_.Polynomial.coeff_C_mul, hp]
  have hq0 : J.q.coeff 0 = 0 := by
    simp [J, mixedPoleClearedFrame, _root_.Polynomial.coeff_sub,
      _root_.Polynomial.coeff_C_mul, hq]
  have hb1 : J.b.coeff 1 = 0 := by
    change (PC p * H.b - PX * (PC u * H.d + PC v * H.r + PC w * H.s)).coeff (0+1) = 0
    simp only [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul]
    exact sub_eq_zero.mpr hu.symm
  have hp1 : J.p.coeff 1 = 0 := by
    change (PC p * H.p - PX * (PC u * H.r + PC v * H.x + PC w * H.y)).coeff (0+1) = 0
    simp only [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul]
    exact sub_eq_zero.mpr hv.symm
  have hq1 : J.q.coeff 1 = 0 := by
    change (PC p * H.q - PX * (PC u * H.s + PC v * H.y + PC w * H.z)).coeff (0+1) = 0
    simp only [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul]
    exact sub_eq_zero.mpr hw.symm
  have hbg (j : ℕ) (hj : j < 2) : J.b.coeff j = 0 := by
    interval_cases j <;> assumption
  have hpg (j : ℕ) (hj : j < 2) : J.p.coeff j = 0 := by
    interval_cases j <;> assumption
  have hqg (j : ℕ) (hj : j < 2) : J.q.coeff j = 0 := by
    interval_cases j <;> assumption
  have ha3 := transverseSchur_longitudinal_zero_of_mixedGap J 2 4
    hJreg hbg hpg hqg hJdet 3 (by decide) (by decide)
  change (PC (p*p) * H.a -
    PX * (PC (2*p) * (PC u * H.b + PC v * H.p + PC w * H.q)) +
    PX * (PX * (PC (u*u) * H.d + PC (v*v) * H.x + PC (w*w) * H.z +
      PC (2*u*v) * H.r + PC (2*u*w) * H.s + PC (2*v*w) * H.y))).coeff ((1+1)+1) = 0 at ha3
  simp only [_root_.Polynomial.coeff_add, _root_.Polynomial.coeff_sub,
    _root_.Polynomial.coeff_X_mul, _root_.Polynomial.coeff_C_mul] at ha3
  refine ⟨2*(u*H.b.coeff 2 + v*H.p.coeff 2 + w*H.q.coeff 2) -
    p*H.a.coeff 3, ?_⟩
  linear_combination ha3

end ClearedMixedPole

/-- The third-order repair constraint on the actual reverse-Rees
source frame, with the determinant clock and regular leading
kernel discharged from source hypotheses. -/
theorem sourceLeading_clearedMixedPole_repair_dvd
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
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (p u v w : _root_.Polynomial E) :
    let H := sourceLeading_lineSchurFrame F m z V
    (u*H.d.coeff 0 + v*H.r.coeff 0 + w*H.s.coeff 0 = p*H.b.coeff 1) →
    (u*H.r.coeff 0 + v*H.x.coeff 0 + w*H.y.coeff 0 = p*H.p.coeff 1) →
    (u*H.s.coeff 0 + v*H.y.coeff 0 + w*H.z.coeff 0 = p*H.q.coeff 1) →
    p ∣ u*u*H.d.coeff 1 + v*v*H.x.coeff 1 + w*w*H.z.coeff 1 +
      2*u*v*H.r.coeff 1 + 2*u*w*H.s.coeff 1 + 2*v*w*H.y.coeff 1 := by
  dsimp only
  intro hu hv hw
  let H := sourceLeading_lineSchurFrame F m z V
  obtain ⟨hb, hp, hq, hr⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hgrad
  have hd (j : ℕ) (hj : j < 4) : H.determinantCore.coeff j = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff j = 0
    rw [sourceLeading_lineSchurFrame_det F m (by omega) hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ j)]
  exact transverseSchur_clearedMixedPole_repair_dvd H p u v w hr hb hp hq hu hv hw hd




/-! ## Cubic clock excludes a surviving transverse kernel

At a determinant component where the leading transverse block has
rank two, a fixed kernel direction cannot survive the whole transverse
pencil. The mixed row has Rees degree at most two, whereas the full
determinant has exact order six.
-/

section CubicCommonKernel

variable {R : Type*} [CommRing R] [IsDomain R]
local notation "RP" => _root_.Polynomial R

/-- The Schur determinant clock cannot be six if the transverse
pencil has a common kernel direction and a leading principal
cofactor survives. No condition on the longitudinal entry is needed. -/
theorem cubicClock_commonKernel_impossible
    (T : Matrix (Fin 3) (Fin 3) RP) (hsym : T.IsSymm)
    (b : Fin 3 → RP) (a : RP) (d : Fin 3 → R) (k : Fin 3)
    (hk : d k ≠ 0)
    (hker : T *ᵥ (fun i => _root_.Polynomial.C (d i)) = 0)
    (hkk : (T.adjugate k k).coeff 0 ≠ 0)
    (hb : ∀ i, (b i).natDegree ≤ 2)
    (δ : R) (hδ : δ ≠ 0)
    (hclock : a*T.det -
      (∑ i : Fin 3, ∑ j : Fin 3, b i*T.adjugate i j*b j) =
      _root_.Polynomial.monomial 6 δ) : False := by
  classical
  let D : Fin 3 → RP := fun i => _root_.Polynomial.C (d i)
  let A := T.adjugate
  let V : RP := ∑ i : Fin 3, D i * b i
  have hDk : D k ≠ 0 := _root_.Polynomial.C_ne_zero.mpr hk
  have hD : D ≠ 0 := by
    intro h
    exact hDk (by simpa only [Pi.zero_apply] using congrFun h k)
  have hdet : T.det = 0 := by
    by_contra ht
    exact hD (Matrix.eq_zero_of_mulVec_eq_zero ht hker)
  have hAk : A k k ≠ 0 := by
    intro h
    apply hkk
    change (A k k).coeff 0 = 0
    rw [h, _root_.Polynomial.coeff_zero]
  have hAs : A.IsSymm := by
    change T.adjugate.transpose = T.adjugate
    rw [Matrix.adjugate_transpose, hsym]
  have hcol (j : Fin 3) : T *ᵥ (fun i => A i j) = 0 := by
    funext i
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) RP => M i j)
      (Matrix.mul_adjugate T)
    simpa [A, Matrix.mulVec, dotProduct, Matrix.mul_apply, hdet] using he
  have hprop (i j : Fin 3) : D k * A i j = D i * A k j := by
    let Z : Fin 3 → RP := D k • (fun l => A l j) - A k j • D
    have hz : T *ᵥ Z = 0 := by
      change T *ᵥ (D k • (fun l => A l j) - A k j • D) = 0
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hcol j,
        show T *ᵥ D = 0 from hker]
      simp
    have hzk : Z k = 0 := by
      change D k * A k j - A k j * D k = 0
      ring
    have hzero := principalCofactor_kernel_zero_of_coordinate_zero T k hAk Z hz hzk
    have he := congrFun hzero i
    change D k * A i j - A k j * D i = 0 at he
    calc
      D k * A i j = A k j * D i := sub_eq_zero.mp he
      _ = _ := mul_comm _ _
  have hcross (i j : Fin 3) : (D k)^2 * A i j = A k k * D i * D j := by
    calc
      _ = D k * (D k * A i j) := by ring
      _ = D i * (D k * A k j) := by rw [hprop i j]; ring
      _ = D i * (D k * A j k) := by rw [show A k j = A j k from hAs.apply j k]
      _ = _ := by rw [hprop j k]; ring
  have hpair : (D k)^2 * (∑ i : Fin 3, ∑ j : Fin 3, b i*A i j*b j) =
      A k k * (V*V) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, (D k)^2 * (b i*A i j*b j) := by
        simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, A k k * ((D i*b i)*(D j*b j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show (D k)^2 * (b i*A i j*b j) =
          b i*((D k)^2*A i j)*b j by ring, hcross i j]
        ring
      _ = _ := by
        simp only [V, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
  have he : -(A k k * (V*V)) =
      (D k)^2 * _root_.Polynomial.monomial 6 δ := by
    have hh := congrArg (fun P : RP => (D k)^2 * P) hclock
    change (D k)^2 * (a*T.det - (∑ i : Fin 3, ∑ j : Fin 3, b i*A i j*b j)) = _ at hh
    rw [hdet, mul_zero, zero_sub, mul_neg, hpair] at hh
    exact hh
  have hm : (_root_.Polynomial.monomial 6 δ : RP) ≠ 0 := by
    intro h
    have hh := congrArg (fun P : RP => P.coeff 6) h
    exact hδ (by simpa using hh)
  have hV : V ≠ 0 := by
    intro h
    rw [h, mul_zero, mul_zero, neg_zero] at he
    exact (mul_ne_zero (pow_ne_zero _ hDk) hm) he.symm
  have hdeg : V.natDegree ≤ 2 := by
    apply sourceTime_natDegree_sum_le
    intro i _
    change (_root_.Polynomial.C (d i) * b i).natDegree ≤ 2
    exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans (hb i)
  have htA : (A k k).natTrailingDegree = 0 :=
    _root_.Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hkk
  have htD : ((D k)^2).natTrailingDegree = 0 := by
    change ((_root_.Polynomial.C (d k) : RP)^2).natTrailingDegree = 0
    rw [← map_pow, _root_.Polynomial.natTrailingDegree_C]
  have ht := congrArg _root_.Polynomial.natTrailingDegree he
  rw [_root_.Polynomial.natTrailingDegree_neg,
    _root_.Polynomial.natTrailingDegree_mul hAk (mul_ne_zero hV hV),
    _root_.Polynomial.natTrailingDegree_mul hV hV, htA,
    _root_.Polynomial.natTrailingDegree_mul (pow_ne_zero _ hDk) hm,
    htD, _root_.Polynomial.natTrailingDegree_monomial hδ] at ht
  have hbound := (_root_.Polynomial.natTrailingDegree_le_natDegree V).trans hdeg
  omega

end CubicCommonKernel

private theorem source_negative_transverse_initialForm_zero
    (F : StationarySource K) (m : ℤ) (hm : m < 0) :
    initialForm transverseCubicWeight m F = 0 := by
  ext d
  have hw : 0 ≤ Finsupp.weight transverseCubicWeight d := by
    rw [← sourceTransverseNatGrade_sum]
    positivity
  rw [coeff_initialForm, if_neg (by omega), MvPolynomial.coeff_zero]

/-- The mixed block of a cubic reverse Hessian has Rees degree at
most two. The nominal order-three layer has no transverse derivative. -/
theorem sourceCubic_reverseHessian_mixed_degree_le_two
    {R : Type*} [CommRing R]
    (F : StationarySource K) (q : StationarySource K →+* R)
    (i : Fin 3) :
    ((_root_.Polynomial.mapRingHom q)
      (sourceLeading_reverseHessian F 3 (.inl ()) (.inr i))).natDegree ≤ 2 := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [_root_.Polynomial.coe_mapRingHom, _root_.Polynomial.coeff_map,
    sourceLeading_reverseHessian_coeff]
  by_cases h : n ≤ 3
  · have he : n = 3 := by omega
    subst n
    rw [if_pos (by decide : 3 ≤ 3), hessian_initialForm_entry]
    have hw : ((3 : ℕ) : ℤ) - ((3 : ℕ) : ℤ) - transverseCubicWeight (.inl ()) -
        transverseCubicWeight (.inr i) = -1 := by
      simp [transverseCubicWeight]
    rw [hw, source_negative_transverse_initialForm_zero _ _ (by decide), map_zero]
  · rw [if_neg h, map_zero]

/-- Source-honest contradiction for a common transverse kernel at a
rank-two leading determinant component. The map may be evaluation
or passage to a residue domain; it must preserve the nonzero Hessian
constant. The hypothesis is on the actual transverse reverse pencil. -/
theorem sourceCubic_commonTransverseKernel_impossible
    {R : Type*} [CommRing R] [IsDomain R]
    (F : StationarySource K) (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (q : StationarySource K →+* R) (hδ : q (MvPolynomial.C δ) ≠ 0)
    (d : Fin 3 → R) (k : Fin 3) (hk : d k ≠ 0)
    (hker : let M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) (_root_.Polynomial R) :=
        (_root_.Polynomial.mapRingHom q).mapMatrix (sourceLeading_reverseHessian F 3);
      (M.submatrix (Sum.inr : Fin 3 → Unit ⊕ Fin 3) Sum.inr) *ᵥ
        (fun i => _root_.Polynomial.C (d i)) = 0)
    (hkk : let M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) (_root_.Polynomial R) :=
        (_root_.Polynomial.mapRingHom q).mapMatrix (sourceLeading_reverseHessian F 3);
      ((M.submatrix (Sum.inr : Fin 3 → Unit ⊕ Fin 3) Sum.inr).adjugate k k).coeff 0 ≠ 0) :
    False := by
  classical
  let M := (_root_.Polynomial.mapRingHom q).mapMatrix (sourceLeading_reverseHessian F 3)
  let T := M.submatrix Sum.inr Sum.inr
  let H := sourceLineBlockOfMatrix M
  let b : Fin 3 → _root_.Polynomial R := ![H.b,H.p,H.q]
  have hsym (i j : Unit ⊕ Fin 3) : M i j = M j i := by
    change _root_.Polynomial.map q (sourceLeading_reverseHessian F 3 i j) =
      _root_.Polynomial.map q (sourceLeading_reverseHessian F 3 j i)
    congr 1
    apply _root_.Polynomial.ext
    intro n
    rw [sourceLeading_reverseHessian_coeff, sourceLeading_reverseHessian_coeff]
    split_ifs
    · simp only [hessian_apply, HC4.Newton.pderiv_comm_backport j i]
    · rfl
  have hTs : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hsym (.inr j) (.inr i)
  have hTdet : transverseSchurDet H = T.det := by
    rw [Matrix.det_fin_three]
    have h12 := hsym (.inr 1) (.inr 0)
    have h13 := hsym (.inr 2) (.inr 0)
    have h23 := hsym (.inr 2) (.inr 1)
    simp [H, T, transverseSchurDet, sourceLineBlockOfMatrix,
      GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
      h12, h13, h23] <;> ring
  have hmix : transverseSchurMixed H = ∑ i : Fin 3, ∑ j : Fin 3,
      b i * T.adjugate i j * b j := by
    apply sourceLineFrame_mixed_adjugate H T <;> try rfl
    intro i j
    exact hsym (.inr i) (.inr j)
  have hb (i : Fin 3) : (b i).natDegree ≤ 2 := by
    fin_cases i
    · exact sourceCubic_reverseHessian_mixed_degree_le_two F q 0
    · exact sourceCubic_reverseHessian_mixed_degree_le_two F q 1
    · exact sourceCubic_reverseHessian_mixed_degree_le_two F q 2
  have hclock : H.determinantCore = _root_.Polynomial.monomial 6 (q (MvPolynomial.C δ)) := by
    rw [show H.determinantCore = M.det from sourceLineBlockOfMatrix_det M hsym]
    change ((_root_.Polynomial.mapRingHom q).mapMatrix
      (sourceLeading_reverseHessian F 3)).det = _
    rw [← RingHom.map_det, sourceLeading_reverseHessian_constantDet F 3 (by decide) hcap hdet]
    exact _root_.Polynomial.map_monomial q
  rw [transverseSchur_det_identity, hTdet, hmix] at hclock
  exact cubicClock_commonKernel_impossible T hTs b H.a d k hk hker hkk hb
    (q (MvPolynomial.C δ)) hδ hclock




/-! ## Assemble the actual simple mixed pole

The preceding squared-numerator bounds are sufficient to construct a
single cleared mixed solution in either cubic multiplicity pattern.
There is no choice of a rational solution independent of the source.
-/

section MixedPoleAssembly

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If the cubic determinant divides a numerator square, a double
linear factor and a distinct prime, or an exact triple prime factor,
leave at most one copy of the repeated prime in the denominator. -/
theorem cubicDet_complement_dvd_of_dvd_square
    (D p : R) (hp : Prime p)
    (hfactor : (∃ r : R, Prime r ∧ ¬ r ∣ p ∧ D = p^2*r) ∨
      (∃ c : R, IsUnit c ∧ D = p^3*c)) :
    ∃ e : R, D = p*e ∧ ∀ s : R, D ∣ s^2 → e ∣ s := by
  rcases hfactor with ⟨r, hr, hdistinct, hD⟩ | ⟨c, hc, hD⟩
  · refine ⟨p*r, ?_, ?_⟩
    · rw [hD]
      ring
    · intro s hs
      have hpD : p ∣ D := ⟨p*r, by rw [hD]; ring⟩
      have hrD : r ∣ D := ⟨p^2, by rw [hD]; ring⟩
      obtain ⟨u, hu⟩ := hp.dvd_of_dvd_pow (n := 2) (dvd_trans hpD hs)
      have hrs := hr.dvd_of_dvd_pow (n := 2) (dvd_trans hrD hs)
      rw [hu] at hrs
      obtain ⟨v, hv⟩ := (hr.dvd_mul.mp hrs).resolve_left hdistinct
      exact ⟨v, by rw [hu, hv]; ring⟩
  · refine ⟨p^2*c, ?_, ?_⟩
    · rw [hD]
      ring
    · intro s hs
      have hpD : p^3 ∣ D := ⟨c,hD⟩
      have hs2 : p^2 ∣ s :=
        prime_pow_succ_dvd_of_odd_pow_dvd_square p hp 1 s (dvd_trans hpD hs)
      obtain ⟨u, hu⟩ := hs2
      obtain ⟨a, ha⟩ := hc
      refine ⟨(↑a⁻¹ : R)*u, ?_⟩
      rw [hu, ← ha]
      calc
        p^2*u = p^2*(1:R)*u := by ring
        _ = p^2*((a:R)*(↑a⁻¹:R))*u := by simp
        _ = _ := by ring

/-- A cancelled Cramer numerator constructs an honest cleared
solution. The complementary factor is cancelled in the original
matrix equation, not in a selected component. -/
theorem exists_cleared_mixed_solution_of_cancelled_Cramer
    (T : Matrix (Fin 3) (Fin 3) R) (b : Fin 3 → R)
    (p e : R) (hdet : T.det = p*e) (hreg : T.det ≠ 0)
    (hdiv : ∀ i : Fin 3, e ∣ (T.adjugate *ᵥ b) i) :
    ∃ v : Fin 3 → R, T *ᵥ v = p • b := by
  classical
  choose v hv using hdiv
  have he : e ≠ 0 := by
    intro hz
    exact hreg (by rw [hdet,hz,mul_zero])
  have hv' : T.adjugate *ᵥ b = e • v := funext hv
  have h := calc
    T *ᵥ (e • v) = T *ᵥ (T.adjugate *ᵥ b) := by rw [← hv']
    _ = T.det • b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = (p*e) • b := by rw [hdet]
  refine ⟨v, ?_⟩
  funext i
  rw [Matrix.mulVec_smul] at h
  have hi := congrFun h i
  change e * (T *ᵥ v) i = (p*e)*b i at hi
  change (T *ᵥ v) i = p*b i
  apply mul_left_cancel₀ he
  calc
    e * (T *ᵥ v) i = (p*e)*b i := hi
    _ = _ := by ring

end MixedPoleAssembly

/-- Both cubic multiplicity patterns give a single cleared mixed
solution on the actual characteristic line, and its numerator
obeys the actual third-order transverse repair constraint.

Primality and the exact determinant factorization refer to the
line-time coefficient ring. No claim of a genuine pole is needed:
if the resulting numerator is divisible by p, the mixed solution
is polynomial instead. -/
theorem sourceCubic_exists_cleared_simpleMixedPole
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight 3 F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight 3 F))))
    (p : _root_.Polynomial E) (hp : Prime p)
    (hfactor : let D := (transverseSchurDet (sourceLeading_lineSchurFrame F 3 z V)).coeff 0;
      (∃ r : _root_.Polynomial E, Prime r ∧ ¬ r ∣ p ∧ D = p^2*r) ∨
      (∃ c : _root_.Polynomial E, IsUnit c ∧ D = p^3*c)) :
    let H := sourceLeading_lineSchurFrame F 3 z V
    let T := (lineEval z V).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr)
    let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1]
    (∃ w : Fin 3 → _root_.Polynomial E, T *ᵥ w = b) ∨
    (∃ v : Fin 3 → _root_.Polynomial E, T *ᵥ v = p • b ∧
      (∃ i : Fin 3, ¬ p ∣ v i) ∧
      p ∣ v 0*v 0*H.d.coeff 1 + v 1*v 1*H.x.coeff 1 + v 2*v 2*H.z.coeff 1 +
        2*v 0*v 1*H.r.coeff 1 + 2*v 0*v 2*H.s.coeff 1 + 2*v 1*v 2*H.y.coeff 1) := by
  classical
  let H := sourceLeading_lineSchurFrame F 3 z V
  let L := initialForm transverseCubicWeight 3 F
  let T := (lineEval z V).toRingHom.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)
  let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1]
  let D := (transverseSchurDet H).coeff 0
  obtain ⟨hb0,hp0,hq0,hreg⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F 3 z V hV hz hgrad
  have hbg (i : ℕ) (hi : i < 1) : H.b.coeff i = 0 := by
    have he : i = 0 := by omega
    subst i
    exact hb0
  have hpg (i : ℕ) (hi : i < 1) : H.p.coeff i = 0 := by
    have he : i = 0 := by omega
    subst i
    exact hp0
  have hqg (i : ℕ) (hi : i < 1) : H.q.coeff i = 0 := by
    have he : i = 0 := by omega
    subst i
    exact hq0
  have hD : D = T.det := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F 3 z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (lineEval z V).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
  obtain ⟨e,he,hcancel⟩ := cubicDet_complement_dvd_of_dvd_square D p hp hfactor
  have hdiv (i : Fin 3) : e ∣ (T.adjugate *ᵥ b) i :=
    hcancel _ (sourceLeading_mixedGap_dvd_Cramer_square F 3 1 (by decide)
      (by decide) (by decide) hcap hdet z V hV hreg hbg hpg hqg D dvd_rfl i)
  obtain ⟨v,hv⟩ := exists_cleared_mixed_solution_of_cancelled_Cramer T b p e
    (hD.symm.trans he) (by rw [← hD]; exact hreg) hdiv
  change (∃ w : Fin 3 → _root_.Polynomial E, T *ᵥ w = b) ∨ _
  by_cases hall : ∀ i : Fin 3, p ∣ v i
  · choose w hw using hall
    have heq : v = p • w := funext hw
    rw [heq, Matrix.mulVec_smul] at hv
    refine Or.inl ⟨w, ?_⟩
    funext i
    have hi := congrFun hv i
    exact mul_left_cancel₀ hp.ne_zero hi
  · have hres : ∃ i : Fin 3, ¬ p ∣ v i := by
      push_neg at hall
      exact hall
    have hcoeff := sourceLeading_lineSchurFrame_coeff F 3 0 (by decide) z V
    simp only [Nat.cast_zero, sub_zero] at hcoeff
    have hd : H.d.coeff 0 = T 0 0 := congrArg GeneralFourBlock.d hcoeff
    have hr : H.r.coeff 0 = T 0 1 := congrArg GeneralFourBlock.r hcoeff
    have hs : H.s.coeff 0 = T 0 2 := congrArg GeneralFourBlock.s hcoeff
    have hx : H.x.coeff 0 = T 1 1 := congrArg GeneralFourBlock.x hcoeff
    have hy : H.y.coeff 0 = T 1 2 := congrArg GeneralFourBlock.y hcoeff
    have hzz : H.z.coeff 0 = T 2 2 := congrArg GeneralFourBlock.z hcoeff
    have hsym (i j : Fin 3) : T i j = T j i := by
      change lineEval z V (pderiv (.inr j) (pderiv (.inr i) L)) =
        lineEval z V (pderiv (.inr i) (pderiv (.inr j) L))
      rw [HC4.Newton.pderiv_comm_backport]
    have hu : v 0*H.d.coeff 0 + v 1*H.r.coeff 0 + v 2*H.s.coeff 0 =
        p*H.b.coeff 1 := by
      have hh := congrFun hv (0 : Fin 3)
      change (∑ j : Fin 3, T 0 j*v j) = p*H.b.coeff 1 at hh
      rw [Fin.sum_univ_three] at hh
      rw [hd,hr,hs]
      linear_combination hh
    have hv1 : v 0*H.r.coeff 0 + v 1*H.x.coeff 0 + v 2*H.y.coeff 0 =
        p*H.p.coeff 1 := by
      have hh := congrFun hv (1 : Fin 3)
      change (∑ j : Fin 3, T 1 j*v j) = p*H.p.coeff 1 at hh
      rw [Fin.sum_univ_three, hsym 1 0] at hh
      rw [hr,hx,hy]
      linear_combination hh
    have hw1 : v 0*H.s.coeff 0 + v 1*H.y.coeff 0 + v 2*H.z.coeff 0 =
        p*H.q.coeff 1 := by
      have hh := congrFun hv (2 : Fin 3)
      change (∑ j : Fin 3, T 2 j*v j) = p*H.q.coeff 1 at hh
      rw [Fin.sum_univ_three, hsym 2 0, hsym 2 1] at hh
      rw [hs,hy,hzz]
      linear_combination hh
    exact Or.inr ⟨v,hv,hres,sourceLeading_clearedMixedPole_repair_dvd
      F 3 (by decide) hcap hdet z V hV hz hgrad p (v 0) (v 1) (v 2) hu hv1 hw1⟩




/-! ## A rank-two mixed residue fixes the quadratic directional jet

On the repeated component the known directional-power witness is a
fixed kernel vector. A genuine cleared mixed residue is proportional
to this same vector. Thus third-order isotropy constrains the fixed
direction, rather than a varying rational numerator. The mixed
directional pairing is also divisible by the same prime.
-/

section FixedMixedResidue

variable {R : Type*} [CommRing R] [IsDomain R]

theorem fixedMixedResidue_directional_divisibility
    (T C : Matrix (Fin 3) (Fin 3) R) (hTs : T.IsSymm)
    (b d l v : Fin 3 → R) (p : R) (hp : Prime p) (k : Fin 3)
    (hcof : ¬ p ∣ T.adjugate k k) (hdk : IsUnit (d k))
    (hd : T *ᵥ d = p • l)
    (hv : T *ᵥ v = p • b)
    (horth : ∑ i : Fin 3, l i*d i = 0)
    (hres : ∃ i : Fin 3, ¬ p ∣ v i)
    (hpair : p ∣ ∑ i : Fin 3, ∑ j : Fin 3, v i*C i j*v j) :
    (p ∣ ∑ i : Fin 3, ∑ j : Fin 3, d i*C i j*d j) ∧
      (p ∣ ∑ i : Fin 3, d i*b i) := by
  classical
  let I : Ideal R := Ideal.span {p}
  letI : I.IsPrime := by
    constructor
    · intro htop
      have hm : (1 : R) ∈ I := by rw [htop]; trivial
      exact hp.not_dvd_one (Ideal.mem_span_singleton.mp hm)
    · intro x y hxy
      rcases hp.dvd_mul.mp (Ideal.mem_span_singleton.mp hxy) with hx | hy
      · exact Or.inl (Ideal.mem_span_singleton.mpr hx)
      · exact Or.inr (Ideal.mem_span_singleton.mpr hy)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  let A := T.map q
  let D : Fin 3 → R ⧸ I := fun i => q (d i)
  let V : Fin 3 → R ⧸ I := fun i => q (v i)
  have hqp : q p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)
  have hqzero (x : R) : q x = 0 ↔ p ∣ x :=
    ⟨fun h => Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h),
      fun h => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)⟩
  have hmap (w : Fin 3 → R) (i : Fin 3) :
      (A *ᵥ (fun j => q (w j))) i = q ((T *ᵥ w) i) := by
    simp only [A, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hD : A *ᵥ D = 0 := by
    funext i
    change (A *ᵥ (fun j => q (d j))) i = 0
    rw [hmap, hd]
    change q (p*l i) = 0
    rw [map_mul, hqp, zero_mul]
  have hV : A *ᵥ V = 0 := by
    funext i
    change (A *ᵥ (fun j => q (v j))) i = 0
    rw [hmap, hv]
    change q (p*b i) = 0
    rw [map_mul, hqp, zero_mul]
  have hA : A.adjugate k k ≠ 0 := by
    intro h
    have he : A.adjugate = T.adjugate.map q := (q.map_adjugate T).symm
    rw [he] at h
    exact hcof ((hqzero _).mp h)
  have hunit : IsUnit (D k) := hdk.map q
  obtain ⟨c,hc⟩ := principalCofactor_kernelLine_of_unitCoordinate
    A D k hA hD hunit V hV
  have hc0 : c ≠ 0 := by
    intro h
    obtain ⟨i,hi⟩ := hres
    apply hi
    apply (hqzero _).mp
    change V i = 0
    rw [hc i,h,zero_mul]
  have hQ : (∑ i : Fin 3, ∑ j : Fin 3, V i*q (C i j)*V j) = 0 := by
    have h := (hqzero _).mpr hpair
    simpa only [map_sum, map_mul, V] using h
  have hQd : c*c*(∑ i : Fin 3, ∑ j : Fin 3, D i*q (C i j)*D j) = 0 := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, c*c*(D i*q (C i j)*D j) := by
        simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, V i*q (C i j)*V j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hc i,hc j]
        ring
      _ = 0 := hQ
  have hdiag : p ∣ ∑ i : Fin 3, ∑ j : Fin 3, d i*C i j*d j := by
    apply (hqzero _).mp
    simp only [map_sum,map_mul]
    exact (mul_eq_zero.mp hQd).resolve_left (mul_ne_zero hc0 hc0)
  have hdot : ∑ i : Fin 3, d i*b i = ∑ i : Fin 3, l i*v i := by
    apply mul_left_cancel₀ hp.ne_zero
    calc
      _ = ∑ i : Fin 3, d i*(T *ᵥ v) i := by
        rw [hv,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change p*(d i*b i) = d i*(p*b i)
        ring
      _ = ∑ i : Fin 3, ∑ j : Fin 3, d i*(T i j*v j) := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
      _ = ∑ j : Fin 3, ∑ i : Fin 3, T j i*d i*v j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [show T i j = T j i from hTs.apply j i]
        ring
      _ = ∑ j : Fin 3, (T *ᵥ d) j*v j := by
        simp only [Matrix.mulVec,dotProduct,Finset.sum_mul]
      _ = _ := by
        rw [hd,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        change (p*l j)*v j = p*(l j*v j)
        ring
  refine ⟨hdiag,?_⟩
  rw [hdot]
  apply (hqzero _).mp
  simp only [map_sum,map_mul]
  calc
    (∑ i : Fin 3, q (l i)*q (v i)) =
        ∑ i : Fin 3, c*(q (l i)*D i) := by
      apply Finset.sum_congr rfl
      intro i _
      change q (l i)*V i = _
      rw [hc i]
      ring
    _ = c*(∑ i : Fin 3, q (l i)*D i) := by rw [Finset.mul_sum]
    _ = 0 := by
      have hh := congrArg q horth
      simp only [map_sum,map_mul,map_zero] at hh
      rw [show (∑ i : Fin 3, q (l i)*D i) = 0 from hh,mul_zero]

end FixedMixedResidue

/-- In the actual cubic source, the residue constraint on the
quadratic repair is the divisibility of the fixed directional
second derivative. The mixed directional constraint is on the
same actual first mixed row. The leading fixed direction and
surviving cofactor are explicit inputs. -/
theorem sourceCubic_fixedMixedResidue_directional_divisibility
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight 3 F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight 3 F))))
    (p : _root_.Polynomial E) (hp : Prime p)
    (d l v : Fin 3 → _root_.Polynomial E) (k : Fin 3)
    (hdk : IsUnit (d k))
    (horth : ∑ i : Fin 3, l i*d i = 0)
    (hres : ∃ i : Fin 3, ¬ p ∣ v i)
    (hfixed : let T : Matrix (Fin 3) (Fin 3) (_root_.Polynomial E) :=
        (lineEval z V).toRingHom.mapMatrix ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr);
      T *ᵥ d = p • l ∧ ¬ p ∣ T.adjugate k k)
    (hmixed : let H := sourceLeading_lineSchurFrame F 3 z V;
      let T : Matrix (Fin 3) (Fin 3) (_root_.Polynomial E) :=
        (lineEval z V).toRingHom.mapMatrix ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr);
      T *ᵥ v = p • (![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1] : Fin 3 → _root_.Polynomial E)) :
    let H := sourceLeading_lineSchurFrame F 3 z V
    let C := (lineEval z V).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight 2 F)).submatrix Sum.inr Sum.inr)
    (p ∣ ∑ i : Fin 3, ∑ j : Fin 3, d i*C i j*d j) ∧
      (p ∣ ∑ i : Fin 3, d i*(![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1] :
        Fin 3 → _root_.Polynomial E) i) := by
  classical
  let H := sourceLeading_lineSchurFrame F 3 z V
  let T := (lineEval z V).toRingHom.mapMatrix
    ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr)
  let C := (lineEval z V).toRingHom.mapMatrix
    ((hessian (initialForm transverseCubicWeight 2 F)).submatrix Sum.inr Sum.inr)
  let b : Fin 3 → _root_.Polynomial E := ![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1]
  have hsym (i j : Fin 3) : T i j = T j i := by
    change lineEval z V (pderiv (.inr j) (pderiv (.inr i)
      (initialForm transverseCubicWeight 3 F))) =
      lineEval z V (pderiv (.inr i) (pderiv (.inr j)
        (initialForm transverseCubicWeight 3 F)))
    rw [HC4.Newton.pderiv_comm_backport]
  have hTs : T.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hsym j i
  have hCs (i j : Fin 3) : C i j = C j i := by
    change lineEval z V (pderiv (.inr j) (pderiv (.inr i)
      (initialForm transverseCubicWeight 2 F))) =
      lineEval z V (pderiv (.inr i) (pderiv (.inr j)
        (initialForm transverseCubicWeight 2 F)))
    rw [HC4.Newton.pderiv_comm_backport]
  have he0 := sourceLeading_lineSchurFrame_coeff F 3 0 (by decide) z V
  simp only [Nat.cast_zero, sub_zero] at he0
  have hd0 : H.d.coeff 0 = T 0 0 := congrArg GeneralFourBlock.d he0
  have hr0 : H.r.coeff 0 = T 0 1 := congrArg GeneralFourBlock.r he0
  have hs0 : H.s.coeff 0 = T 0 2 := congrArg GeneralFourBlock.s he0
  have hx0 : H.x.coeff 0 = T 1 1 := congrArg GeneralFourBlock.x he0
  have hy0 : H.y.coeff 0 = T 1 2 := congrArg GeneralFourBlock.y he0
  have hz0 : H.z.coeff 0 = T 2 2 := congrArg GeneralFourBlock.z he0
  have hu : v 0*H.d.coeff 0 + v 1*H.r.coeff 0 + v 2*H.s.coeff 0 =
      p*H.b.coeff 1 := by
    have hh := congrFun hmixed (0 : Fin 3)
    change (∑ j : Fin 3, T 0 j*v j) = p*H.b.coeff 1 at hh
    rw [Fin.sum_univ_three] at hh
    rw [hd0,hr0,hs0]
    linear_combination hh
  have hv1 : v 0*H.r.coeff 0 + v 1*H.x.coeff 0 + v 2*H.y.coeff 0 =
      p*H.p.coeff 1 := by
    have hh := congrFun hmixed (1 : Fin 3)
    change (∑ j : Fin 3, T 1 j*v j) = p*H.p.coeff 1 at hh
    rw [Fin.sum_univ_three, hsym 1 0] at hh
    rw [hr0,hx0,hy0]
    linear_combination hh
  have hw1 : v 0*H.s.coeff 0 + v 1*H.y.coeff 0 + v 2*H.z.coeff 0 =
      p*H.q.coeff 1 := by
    have hh := congrFun hmixed (2 : Fin 3)
    change (∑ j : Fin 3, T 2 j*v j) = p*H.q.coeff 1 at hh
    rw [Fin.sum_univ_three, hsym 2 0, hsym 2 1] at hh
    rw [hs0,hy0,hz0]
    linear_combination hh
  have he1 := sourceLeading_lineSchurFrame_coeff F 3 1 (by decide) z V
  have hgrade : ((3 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = 2 := by decide
  rw [hgrade] at he1
  have hd1 : H.d.coeff 1 = C 0 0 := congrArg GeneralFourBlock.d he1
  have hr1 : H.r.coeff 1 = C 0 1 := congrArg GeneralFourBlock.r he1
  have hs1 : H.s.coeff 1 = C 0 2 := congrArg GeneralFourBlock.s he1
  have hx1 : H.x.coeff 1 = C 1 1 := congrArg GeneralFourBlock.x he1
  have hy1 : H.y.coeff 1 = C 1 2 := congrArg GeneralFourBlock.y he1
  have hz1 : H.z.coeff 1 = C 2 2 := congrArg GeneralFourBlock.z he1
  have hpair := sourceLeading_clearedMixedPole_repair_dvd F 3 (by decide)
    hcap hdet z V hV hz hgrad p (v 0) (v 1) (v 2) hu hv1 hw1
  have hpair' : p ∣ ∑ i : Fin 3, ∑ j : Fin 3, v i*C i j*v j := by
    have hh : (∑ i : Fin 3, ∑ j : Fin 3, v i*C i j*v j) =
        v 0*v 0*H.d.coeff 1 + v 1*v 1*H.x.coeff 1 + v 2*v 2*H.z.coeff 1 +
          2*v 0*v 1*H.r.coeff 1 + 2*v 0*v 2*H.s.coeff 1 + 2*v 1*v 2*H.y.coeff 1 := by
      simp only [Fin.sum_univ_three,hCs 1 0,hCs 2 0,hCs 2 1,
        ← hd1,← hr1,← hs1,← hx1,← hy1,← hz1]
      ring
    rw [hh]
    exact hpair
  exact fixedMixedResidue_directional_divisibility T C hTs b d l v p hp k
    hfixed.2 hdk hfixed.1 hmixed horth hres hpair'




/-! ## Global directional linearity from the actual mixed residue -/

/-- A line-time polynomial whose coefficients have transverse degree
zero cannot have a homogeneous positive transverse factor unless it
vanishes. Evaluating each coefficient at the transverse origin avoids
any normalization of multivariate factorization. -/
private theorem sourceTime_eq_zero_of_constant_referenceCoeff_dvd
    (P : LineTime K) (p : MvPolynomial (Fin 3) K)
    (hp : MvPolynomial.eval (fun _ : Fin 3 => (0 : K)) p = 0)
    (hP : ∀ n, (P.coeff n).totalDegree = 0)
    (hdiv : _root_.Polynomial.C p ∣ P) : P = 0 := by
  obtain ⟨Q,hQ⟩ := hdiv
  apply _root_.Polynomial.ext
  intro n
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (hP n)
  have he : MvPolynomial.eval (fun _ : Fin 3 => (0 : K)) (P.coeff n) = 0 := by
    rw [hQ, _root_.Polynomial.coeff_C_mul, map_mul, hp, zero_mul]
  have hn : (P.coeff n).coeff 0 = 0 := by
    rw [hc, MvPolynomial.eval_C] at he
    exact he
  rw [hc,hn,map_zero,_root_.Polynomial.coeff_zero]

/-- The actual second derivative in a fixed transverse direction,
written as a cleared Hessian contraction. -/
def sourceFixedDirectionalSquare (d : Fin 3 → K) (F : StationarySource K) :
    StationarySource K :=
  ∑ i : Fin 3, ∑ j : Fin 3, MvPolynomial.C (d i) *
    hessian F (.inr i) (.inr j) * MvPolynomial.C (d j)

theorem sourceFixedDirectionalSquare_eq_second_derivative
    (d : Fin 3 → K) (F : StationarySource K) :
    sourceFixedDirectionalSquare d F =
      ∑ j : Fin 3, MvPolynomial.C (d j) *
        pderiv (.inr j) (∑ i : Fin 3, MvPolynomial.C (d i) * pderiv (.inr i) F) := by
  classical
  unfold sourceFixedDirectionalSquare
  simp only [map_sum,pderiv_C_mul,Finset.mul_sum,hessian_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sourceFixedDirectionalSquare_add (d : Fin 3 → K)
    (F G : StationarySource K) :
    sourceFixedDirectionalSquare d (F+G) =
      sourceFixedDirectionalSquare d F + sourceFixedDirectionalSquare d G := by
  simp only [sourceFixedDirectionalSquare,hessian_apply,map_add,mul_add,add_mul,
    Finset.sum_add_distrib]

private theorem sourceFixedDirectionalSquare_lineEval
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (d : Fin 3 → K)
    (F : StationarySource K) :
    let D : Fin 3 → LineTime K := fun i => _root_.Polynomial.C (MvPolynomial.C (d i))
    let T := (linearLineEval a N).toRingHom.mapMatrix
      ((hessian F).submatrix Sum.inr Sum.inr)
    linearLineEval a N (sourceFixedDirectionalSquare d F) =
      ∑ i : Fin 3, ∑ j : Fin 3, D i*T i j*D j := by
  classical
  simp only [sourceFixedDirectionalSquare,map_sum,map_mul]
  have hC (i : Fin 3) : linearLineEval a N (MvPolynomial.C (d i)) =
      _root_.Polynomial.C (MvPolynomial.C (d i)) := by
    simp [linearLineEval,lineEval]
  simp only [hC, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rfl

private theorem sourceCubic_quadratic_directional_referenceDegree_zero
    (F : StationarySource K) (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (d : Fin 3 → K) (n : ℕ) :
    ((linearLineEval a N (sourceFixedDirectionalSquare d
      (initialForm transverseCubicWeight 2 F))).coeff n).totalDegree = 0 := by
  classical
  rw [sourceFixedDirectionalSquare_lineEval]
  simp only [_root_.Polynomial.finset_sum_coeff]
  apply Nat.eq_zero_of_le_zero
  apply sourceTotalDegree_sum_le
  intro i _
  apply sourceTotalDegree_sum_le
  intro j _
  simp only [_root_.Polynomial.coeff_C_mul,_root_.Polynomial.coeff_mul_C]
  have h : ((linearLineEval a N
      (hessian (initialForm transverseCubicWeight 2 F) (.inr i) (.inr j))).coeff n).totalDegree ≤ 0 := by
    apply sourceLinear_referenceCoeff_totalDegree_le a N _ 0
    rw [hessian_initialForm_entry]
    have hw : (2 : ℤ) - transverseCubicWeight (.inr i) -
        transverseCubicWeight (.inr j) = 0 := by simp [transverseCubicWeight]
    rw [hw]
    intro e he
    have hn := MvPolynomial.mem_support_iff.mp he
    rw [coeff_initialForm] at hn
    split_ifs at hn with hh
    · rw [hh]
      exact le_rfl
    · exact (hn rfl).elim
  have h' : ((((linearLineEval a N).toRingHom.mapMatrix
      ((hessian (initialForm transverseCubicWeight 2 F)).submatrix
        Sum.inr Sum.inr)) i j).coeff n).totalDegree ≤ 0 := h
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by rw [MvPolynomial.totalDegree_C,add_zero]
        exact (MvPolynomial.totalDegree_mul _ _).trans
          (by rw [MvPolynomial.totalDegree_C,zero_add]; exact h'))

/-- The quadratic residue divisibility forces the entire actual
quadratic directional jet to vanish, not only its restriction to
the pole. The nilpotent chart is used solely by its proved
injectivity, with no nonlinear Hessian change. -/
theorem sourceCubic_quadratic_directional_eq_zero_of_dvd
    (F : StationarySource K) (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (hN : N^3 = 0) (d : Fin 3 → K) (p : MvPolynomial (Fin 3) K)
    (hp : MvPolynomial.eval (fun _ : Fin 3 => (0 : K)) p = 0)
    (hdiv : _root_.Polynomial.C p ∣ linearLineEval a N
      (sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 2 F))) :
    sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 2 F) = 0 := by
  apply linearLineEval_injective_of_cube_zero a N hN
  rw [map_zero]
  exact sourceTime_eq_zero_of_constant_referenceCoeff_dvd _ p hp
    (sourceCubic_quadratic_directional_referenceDegree_zero F a N d) hdiv

private theorem sourceFixedDirectionalSquare_lowLayer_zero
    (F : StationarySource K) (d : Fin 3 → K) (m : ℤ) (hm : m < 2) :
    sourceFixedDirectionalSquare d (initialForm transverseCubicWeight m F) = 0 := by
  have hz (i j : Fin 3) :
      hessian (initialForm transverseCubicWeight m F) (.inr i) (.inr j) = 0 := by
    rw [hessian_initialForm_entry]
    apply source_negative_transverse_initialForm_zero
    change m - 1 - 1 < 0
    omega
  simp only [sourceFixedDirectionalSquare,hz,mul_zero,zero_mul,Finset.sum_const_zero]

/-- If the leading directional square vanishes and the actual
quadratic directional square is divisible in the characteristic
chart by a factor vanishing on the transverse origin, the ORIGINAL
cubic source is affine in that fixed transverse direction. -/
theorem sourceCubic_global_directionalSquare_eq_zero
    (F : StationarySource K) (hcap : IsWeightLE transverseCubicWeight 3 F)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N^3 = 0)
    (d : Fin 3 → K) (p : MvPolynomial (Fin 3) K)
    (hp : MvPolynomial.eval (fun _ : Fin 3 => (0 : K)) p = 0)
    (h3 : sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 3 F) = 0)
    (hdiv : _root_.Polynomial.C p ∣ linearLineEval a N
      (sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 2 F))) :
    sourceFixedDirectionalSquare d F = 0 := by
  have h2 := sourceCubic_quadratic_directional_eq_zero_of_dvd F a N hN d p hp hdiv
  have h1 := sourceFixedDirectionalSquare_lowLayer_zero F d 1 (by decide)
  have h0 := sourceFixedDirectionalSquare_lowLayer_zero F d 0 (by decide)
  have he := sourceLeading_reverseLayerSum_eq F 3 hcap
  have he' : initialForm transverseCubicWeight 3 F +
      initialForm transverseCubicWeight 2 F +
      initialForm transverseCubicWeight 1 F +
      initialForm transverseCubicWeight 0 F = F := by
    simpa [Finset.sum_range_succ] using he
  calc
    sourceFixedDirectionalSquare d F = sourceFixedDirectionalSquare d
      (initialForm transverseCubicWeight 3 F + initialForm transverseCubicWeight 2 F +
        initialForm transverseCubicWeight 1 F + initialForm transverseCubicWeight 0 F) :=
      congrArg (sourceFixedDirectionalSquare d) he'.symm
    _ = 0 := by rw [sourceFixedDirectionalSquare_add,sourceFixedDirectionalSquare_add,
        sourceFixedDirectionalSquare_add,h3,h2,h1,h0]; simp

/-- A source-honest lift of the rank-two genuine mixed residue
to global directional linearity. The fixed leading equation and
surviving principal cofactor are still explicit: this theorem
does not assert that every cubic residue has rank two. -/
theorem sourceCubic_fixedMixedResidue_global_directionalSquare_eq_zero
    (F : StationarySource K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N^3 = 0)
    (hz : referenceSlice a
      ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, linearLineEval a N (pderiv i (initialForm transverseCubicWeight 3 F)) =
      _root_.Polynomial.C
        (referenceSlice a (pderiv i (initialForm transverseCubicWeight 3 F))))
    (p : MvPolynomial (Fin 3) K)
    (hp : Prime (_root_.Polynomial.C p : LineTime K))
    (hp0 : MvPolynomial.eval (fun _ : Fin 3 => (0 : K)) p = 0)
    (d : Fin 3 → K) (l v : Fin 3 → LineTime K) (k : Fin 3)
    (hdk : d k ≠ 0)
    (horth : ∑ i : Fin 3, l i * _root_.Polynomial.C (MvPolynomial.C (d i)) = 0)
    (hres : ∃ i : Fin 3, ¬ _root_.Polynomial.C p ∣ v i)
    (hfixed : let T : Matrix (Fin 3) (Fin 3) (LineTime K) :=
        (linearLineEval a N).toRingHom.mapMatrix ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr);
      T *ᵥ (fun i => _root_.Polynomial.C (MvPolynomial.C (d i))) = _root_.Polynomial.C p • l ∧
        ¬ _root_.Polynomial.C p ∣ T.adjugate k k)
    (hmixed : let z : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
        Sum.elim (fun _ => MvPolynomial.C a) X;
      let V : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
        Sum.elim (fun _ => 1) (referenceLinearVector N);
      let H := sourceLeading_lineSchurFrame F 3 z V;
      let T : Matrix (Fin 3) (Fin 3) (LineTime K) :=
        (linearLineEval a N).toRingHom.mapMatrix ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr);
      T *ᵥ v = _root_.Polynomial.C p •
        (![H.b.coeff 1,H.p.coeff 1,H.q.coeff 1] : Fin 3 → LineTime K)) :
    sourceFixedDirectionalSquare d F = 0 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let D : Fin 3 → LineTime K := fun i => _root_.Polynomial.C (MvPolynomial.C (d i))
  let T := (linearLineEval a N).toRingHom.mapMatrix
    ((hessian (initialForm transverseCubicWeight 3 F)).submatrix Sum.inr Sum.inr)
  have hu : IsUnit (d k) := isUnit_iff_ne_zero.mpr hdk
  have hu' : IsUnit (MvPolynomial.C (d k) : B) := hu.map MvPolynomial.C
  have hunit : IsUnit (D k) := hu'.map _root_.Polynomial.C
  have hpair := sourceCubic_fixedMixedResidue_directional_divisibility
    F hcap hdet z V (by rfl) hz hgrad (_root_.Polynomial.C p) hp
    D l v k hunit horth hres hfixed hmixed
  have h2 : _root_.Polynomial.C p ∣ linearLineEval a N
      (sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 2 F)) := by
    rw [sourceFixedDirectionalSquare_lineEval]
    exact hpair.1
  have h3 : sourceFixedDirectionalSquare d (initialForm transverseCubicWeight 3 F) = 0 := by
    apply linearLineEval_injective_of_cube_zero a N hN
    rw [map_zero,sourceFixedDirectionalSquare_lineEval]
    change (∑ i : Fin 3, ∑ j : Fin 3, D i*T i j*D j) = 0
    calc
      _ = ∑ i : Fin 3, D i*(T *ᵥ D) i := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _root_.Polynomial.C p * (∑ i : Fin 3, l i*D i) := by
        rw [show T *ᵥ D = _root_.Polynomial.C p • l from hfixed.1,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change D i*(_root_.Polynomial.C p*l i) = _
        ring
      _ = 0 := by rw [show (∑ i : Fin 3, l i*D i) = 0 from horth,mul_zero]
  exact sourceCubic_global_directionalSquare_eq_zero F hcap a N hN d p hp0 h3 h2


end
end HC4.Polynomial.RankThreeCubic
