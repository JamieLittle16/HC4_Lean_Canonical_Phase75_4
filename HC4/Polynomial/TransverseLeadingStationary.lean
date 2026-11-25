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

/-!
# Stationary transverse characteristics and marked collision rigidity

Actual source regular-anchor rigidity, supporting-edge exclusion and the
stationary cubic marked-collision endpoint. No change of coordinates is made.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton HC4.Valuation
open scoped BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [CharZero K]

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

end
end HC4.Polynomial.RankThreeCubic
