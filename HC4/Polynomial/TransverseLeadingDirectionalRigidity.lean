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
import HC4.Polynomial.TransverseLeadingMixedPole

/-!
# Transverse fixed-direction residue and global directional rigidity

Consumes the actual mixed-pole residue and fixed leading directional power.
Derives divisibility of the directional quadratic jet and a global vanishing
second directional derivative under the explicit source hypotheses.
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
