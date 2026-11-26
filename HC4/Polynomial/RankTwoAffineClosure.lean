import HC4.Polynomial.RankTwoMinorTransport

/-!
# Affine-coordinate rank-two closure

Expose a pure highest-degree power of the affine coefficient F
without changing the affine coordinate direction. Flat-level
rigidity then makes the first derivatives of F proportional.
A second column shear kills one mixed entry while retaining the
nonzero pivot. The actual three-minor identity forces the second
diagonal entry to vanish. Pull this plane back to the original
leading polynomial and use the verified global obstruction.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

/-- A pure-power chart for a nonconstant polynomial independent
of coordinate k can be chosen to fix the k-th column. -/
theorem rankTwo_exists_purePower_chart_fixed
    (F : S K) (k : Fin 4) (hF : pderiv k F = 0)
    (hD : 0 < F.totalDegree) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (p : Fin 4),
      M.det = 1 ∧ p ≠ k ∧
      (∀ i, M i k = (1 : Matrix (Fin 4) (Fin 4) K) i k) ∧
      coeff (Finsupp.single p F.totalDegree) (weightedLinearSubstitution M F) ≠ 0 := by
  classical
  let D := F.totalDegree
  let G := homogeneousComponent D F
  have hG : G.IsHomogeneous D := homogeneousComponent_isHomogeneous _ _
  have hG0 : G ≠ 0 := rankOne_top_ne_zero F hD
  have hex : ∃ d : Fin 4 → K, MvPolynomial.eval d G ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hG0 (hG.eq_zero_of_forall_eval_eq_zero hn)
  obtain ⟨d,hd⟩ := hex
  have haxis : coeff (Finsupp.single k D) G = 0 := by
    change coeff _ (homogeneousComponent D F) = 0
    rw [coeff_homogeneousComponent, Finsupp.degree_single, if_pos rfl]
    by_contra hn
    have hz := exponent_eq_zero_of_pderiv_eq_zero k F hF _ hn
    simp only [Finsupp.single_eq_same] at hz
    omega
  have hpivot : ∃ p : Fin 4, p ≠ k ∧ d p ≠ 0 := by
    by_contra hn
    push_neg at hn
    have he : d = Pi.single k (d k) := by
      funext i
      by_cases hi : i = k
      · subst i; simp
      · rw [Pi.single_eq_of_ne hi]
        exact hn i hi
    apply hd
    rw [he]
    exact rankOne_homogeneous_axis_zero G D hG k (d k) haxis
  obtain ⟨p,hpk,hp⟩ := hpivot
  let M := extremalKernelShear d p
  let Q := weightedLinearSubstitution M F
  let J := homogeneousComponent D Q
  have hJ : J.IsHomogeneous D := homogeneousComponent_isHomogeneous _ _
  have hJG : J = weightedLinearSubstitution M G := by
    change homogeneousComponent D (weightedLinearSubstitution M F) =
      weightedLinearSubstitution M (homogeneousComponent D F)
    rw [← rankOne_ordinaryInitial_eq_component (weightedLinearSubstitution M F) D,
      ← rankOne_ordinaryInitial_eq_component F D]
    exact weightedLinearSubstitution_initialForm _ M (by simp) _ _
  have hMd : M *ᵥ (Pi.single p (d p) : Fin 4 → K) = d := by
    funext i
    change (∑ j : Fin 4, M i j * (Pi.single p (d p) : Fin 4 → K) j) = d i
    rw [Finset.sum_eq_single p]
    · rw [Pi.single_eq_same]
      change extremalKernelShear d p i p * d p = d i
      rw [extremalKernelShear_column d p hp i, div_mul_cancel₀ _ hp]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · simp
  refine ⟨M,p,extremalKernelShear_det d p,hpk,?_,?_⟩
  · intro i
    exact extremalKernelShear_other_column d p i k (Ne.symm hpk)
  · intro hc
    have hcJ : coeff (Finsupp.single p D) J = 0 := by
      change coeff _ (homogeneousComponent D Q) = 0
      rw [coeff_homogeneousComponent, Finsupp.degree_single, if_pos rfl]
      exact hc
    have he := rankOne_homogeneous_axis_zero J D hJ p (d p) hcJ
    rw [hJG, weightedLinearSubstitution_eval, hMd] at he
    exact hd he

/-- A fixed column transports that partial derivative unchanged
except for substitution in the underlying polynomial. -/
theorem rankTwo_partial_fixedColumn
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K) (k : Fin 4)
    (hM : ∀ i, M i k = (1 : Matrix (Fin 4) (Fin 4) K) i k) :
    pderiv k (weightedLinearSubstitution M L) =
      weightedLinearSubstitution M (pderiv k L) := by
  classical
  rw [weightedLinearSubstitution_partial, Finset.sum_eq_single k]
  · rw [hM k, Matrix.one_apply_eq, map_one, mul_one]
  · intro i _ hi
    rw [hM i]
    simp [hi]
  · simp

private theorem rankTwo_partial_degree_le (F : S K) (D : ℕ)
    (hD : 0 < D) (hdeg : F.totalDegree ≤ D) (i : Fin 4) :
    (pderiv i F).totalDegree ≤ D-1 := by
  have hcap : IsWeightLE (fun _ : Fin 4 => (1 : ℤ)) (D : ℤ) F := by
    intro u hu
    rw [weight_allOnes_eq_degree]
    exact_mod_cast (MvPolynomial.le_totalDegree hu).trans hdeg
  have hh := hcap.pderiv i
  change (pderiv i F).support.sup (fun u => u.sum fun _ e => e) ≤ _
  apply Finset.sup_le
  intro u hu
  have he := hh hu
  change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) u ≤ (D : ℤ) - 1 at he
  rw [weight_allOnes_eq_degree] at he
  omega

/-- Produce constant ratios of the affine coefficient in a
determinant-one chart preserving the original affine direction. -/
theorem rankTwo_affine_exists_constantRatio_chart
    (L : S K) (k : Fin 4) (hkk : hessian L k k = 0)
    (hL : AllThreeMinorsZero (hessian L))
    (hD : 0 < (pderiv k L).totalDegree) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (p : Fin 4),
      M.det = 1 ∧ p ≠ k ∧
      let Q := weightedLinearSubstitution M L
      hessian Q k k = 0 ∧ hessian Q k p ≠ 0 ∧
      (∀ i, ∃ c : K, hessian Q k i = MvPolynomial.C c * hessian Q k p) := by
  classical
  let F := pderiv k L
  obtain ⟨M,p,hM,hpk,hfix,hpure⟩ :=
    rankTwo_exists_purePower_chart_fixed F k hkk hD
  let Q := weightedLinearSubstitution M L
  let G := weightedLinearSubstitution M F
  have hG : pderiv k Q = G := rankTwo_partial_fixedColumn L M k hfix
  have hkkQ : hessian Q k k = 0 := by
    change pderiv k (pderiv k Q) = 0
    rw [hG]
    change pderiv k (weightedLinearSubstitution M F) = 0
    rw [rankTwo_partial_fixedColumn F M k hfix, show pderiv k F = 0 from hkk, map_zero]
  let n := F.totalDegree-1
  have hDF : 0 < F.totalDegree := hD
  have hn : n+1 = F.totalDegree :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hDF)
  have hA : coeff (Finsupp.single p n) (pderiv p G) ≠ 0 := by
    rw [coeff_pderiv_backport, ← Finsupp.single_add]
    apply mul_ne_zero
    · rw [hn]
      exact hpure
    · have hh : (((n+1 : ℕ) : K)) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
      simpa [Finsupp.single_apply] using hh
  have hA0 : pderiv p G ≠ 0 := by
    intro hz
    exact hA (by rw [hz,coeff_zero])
  have hdeg (i : Fin 4) : (pderiv i G).totalDegree ≤ n :=
    rankTwo_partial_degree_le G F.totalDegree hD (weightedLinearSubstitution_totalDegree_le M F) i
  have hflat := rankTwo_affine_gradient_flatLevel_in_chart L M k hL hkkQ
  refine ⟨M,p,hM,hpk,hkkQ,?_,?_⟩
  · change pderiv p (pderiv k Q) ≠ 0
    rw [hG]
    exact hA0
  · intro i
    have hc := hflat p i
    change (pderiv p (pderiv k Q))^2 * hessian (pderiv k Q) i i -
      2 * pderiv p (pderiv k Q) * pderiv i (pderiv k Q) * hessian (pderiv k Q) p i +
      (pderiv i (pderiv k Q))^2 * hessian (pderiv k Q) p p = 0 at hc
    rw [hG] at hc
    obtain ⟨c,hc'⟩ := flatLevel_gradient_ratio_constant_of_purePivot G p i n hA
      (hdeg p) (hdeg i) hc
    refine ⟨c,?_⟩
    change pderiv i (pderiv k Q) = MvPolynomial.C c * pderiv p (pderiv k Q)
    rw [hG]
    exact hc'

/-- Eliminate one mixed entry using a constant column shear.
The remaining principal minor forces the corresponding diagonal
entry to vanish, giving an actual zero principal plane. -/
theorem rankTwo_affine_constantRatio_zeroPlane
    (Q : S K) (k p : Fin 4) (hpk : p ≠ k)
    (hkk : hessian Q k k = 0) (hkp : hessian Q k p ≠ 0)
    (hQ : AllThreeMinorsZero (hessian Q))
    (hr : ∀ i, ∃ c : K, hessian Q k i = MvPolynomial.C c * hessian Q k p) :
    ∃ (N : Matrix (Fin 4) (Fin 4) K) (l : Fin 4),
      N.det = 1 ∧ k ≠ l ∧
      let R := weightedLinearSubstitution N Q
      hessian R k k = 0 ∧ hessian R l l = 0 ∧ hessian R k l = 0 := by
  classical
  have hex : ∃ l : Fin 4, l ≠ k ∧ l ≠ p := by
    fin_cases k <;> fin_cases p <;> decide
  obtain ⟨l,hlk,hlp⟩ := hex
  obtain ⟨c,hc⟩ := hr l
  let e : Fin 4 → K := Pi.single l 1 - Pi.single p c
  have hel : e l = 1 := by simp [e,hlp]
  let N := extremalKernelShear e l
  have hN (i : Fin 4) : N i l = e i := by
    change extremalKernelShear e l i l = e i
    rw [extremalKernelShear_column e l (by rw [hel]; exact one_ne_zero), hel, div_one]
  have hNk (i : Fin 4) : N i k = (1 : Matrix (Fin 4) (Fin 4) K) i k :=
    extremalKernelShear_other_column e l i k (Ne.symm hlk)
  have hNp (i : Fin 4) : N i p = (1 : Matrix (Fin 4) (Fin 4) K) i p :=
    extremalKernelShear_other_column e l i p (Ne.symm hlp)
  let R := weightedLinearSubstitution N Q
  have hF : pderiv k R = weightedLinearSubstitution N (pderiv k Q) :=
    rankTwo_partial_fixedColumn Q N k hNk
  have hkkR : hessian R k k = 0 := by
    change pderiv k (pderiv k R) = 0
    rw [hF, rankTwo_partial_fixedColumn _ N k hNk, show pderiv k (pderiv k Q) = 0 from hkk, map_zero]
  have hkpR : hessian R k p ≠ 0 := by
    change pderiv p (pderiv k R) ≠ 0
    rw [hF,rankTwo_partial_fixedColumn _ N p hNp]
    intro hz
    apply hkp
    exact rankOne_substitution_injective N (extremalKernelShear_det e l)
      (hz.trans (map_zero (weightedLinearSubstitution N)).symm)
  have hklR : hessian R k l = 0 := by
    change pderiv l (pderiv k R) = 0
    rw [hF,weightedLinearSubstitution_partial]
    simp only [hN]
    have hsum : (∑ i : Fin 4, weightedLinearSubstitution N (pderiv i (pderiv k Q)) *
        MvPolynomial.C (e i)) =
        weightedLinearSubstitution N (hessian Q k l) -
          weightedLinearSubstitution N (hessian Q k p) * MvPolynomial.C c := by
      simp only [e,Pi.sub_apply,map_sub,mul_sub,Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp [hessian_apply]
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · simp
      · rw [Finset.sum_eq_single p]
        · simp [hessian_apply]
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · simp
    have hC : weightedLinearSubstitution N (MvPolynomial.C c) = MvPolynomial.C c :=
      (weightedLinearSubstitution N).commutes c
    rw [hsum,hc,map_mul,hC,mul_comm (MvPolynomial.C c),sub_self]
  have hminor := rankTwo_allThreeMinorsZero_substitution Q N hQ
  have hcurv := rankTwo_affine_principalMinor_curvature R k p l hkkR
    (hminor (![k,p,l] : Fin 3 → Fin 4) (![k,p,l] : Fin 3 → Fin 4))
  change (hessian R k p)^2 * hessian R l l -
    2 * hessian R k p * hessian R k l * hessian R p l +
    (hessian R k l)^2 * hessian R p p = 0 at hcurv
  rw [hklR] at hcurv
  simp only [mul_zero, zero_mul, sub_zero, zero_pow (by decide : (2:ℕ) ≠ 0),add_zero] at hcurv
  have hllR : hessian R l l = 0 :=
    (mul_eq_zero.mp hcurv).resolve_left (pow_ne_zero _ hkpR)
  exact ⟨N,l,extremalKernelShear_det e l,Ne.symm hlk,hkkR,hllR,hklR⟩

/-- Bilinearity on the span of two constant vectors. -/
theorem extremalHessianPair_span_pair_zero
    (L : S K) (u v : Fin 4 → K)
    (huu : extremalHessianPair L u u = 0)
    (huv : extremalHessianPair L u v = 0)
    (hvu : extremalHessianPair L v u = 0)
    (hvv : extremalHessianPair L v v = 0) :
    ∀ d ∈ Submodule.span K ({u,v} : Set (Fin 4 → K)),
      ∀ e ∈ Submodule.span K ({u,v} : Set (Fin 4 → K)),
        extremalHessianPair L d e = 0 := by
  classical
  intro d hd e he
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hd
  obtain ⟨c,f,rfl⟩ := Submodule.mem_span_pair.mp he
  have h :
      extremalHessianPair L (a • u + b • v) (c • u + f • v) =
        MvPolynomial.C a * extremalHessianPair L u u * MvPolynomial.C c +
        MvPolynomial.C a * extremalHessianPair L u v * MvPolynomial.C f +
        MvPolynomial.C b * extremalHessianPair L v u * MvPolynomial.C c +
        MvPolynomial.C b * extremalHessianPair L v v * MvPolynomial.C f := by
    unfold extremalHessianPair
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,
      Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h,huu,huv,hvu,hvv]
  simp

/-- An arbitrary determinant-one chart exhibiting a zero
principal plane is forbidden, even when it changes weights. -/
theorem globalWeightOptimum_no_zero_plane_arbitraryChart
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : M.det = 1)
    (k l : Fin 4) (hkl : k ≠ l)
    (hzero : let Q := weightedLinearSubstitution M (initialForm w m P)
      hessian Q k k = 0 ∧ hessian Q l l = 0 ∧ hessian Q k l = 0) : False := by
  classical
  let L := initialForm w m P
  let Q := weightedLinearSubstitution M L
  let u : Fin 4 → K := fun i => M i k
  let v : Fin 4 → K := fun i => M i l
  let V := Submodule.span K ({u,v} : Set (Fin 4 → K))
  have hzero' : hessian Q k k = 0 ∧ hessian Q l l = 0 ∧ hessian Q k l = 0 := hzero
  have hf := rankOne_substitution_injective M hM
  have hpair (i j : Fin 4) (hz : hessian Q i j = 0) :
      extremalHessianPair L (fun a => M a i) (fun a => M a j) = 0 := by
    apply hf
    rw [← extremalHessianPair_chart_entry, map_zero]
    exact hz
  have huu : extremalHessianPair L u u = 0 := hpair k k hzero'.1
  have hvv : extremalHessianPair L v v = 0 := hpair l l hzero'.2.1
  have huv : extremalHessianPair L u v = 0 := hpair k l hzero'.2.2
  have hvu : extremalHessianPair L v u = 0 := hpair l k
    ((show hessian Q l k = hessian Q k l from pderiv_comm_backport k l Q).trans hzero'.2.2)
  have hi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hM]; exact isUnit_one))
  have hu : M *ᵥ (Pi.single k (1:K) : Fin 4 → K) = u := Matrix.mulVec_single_one M k
  have hv : M *ᵥ (Pi.single l (1:K) : Fin 4 → K) = v := Matrix.mulVec_single_one M l
  have hu0 : u ≠ 0 := by
    intro hz
    have he : (Pi.single k (1:K) : Fin 4 → K) = 0 := hi (by rw [hu,hz,Matrix.mulVec_zero])
    have hh := congrFun he k
    simpa using hh
  have hvspan (a : K) : v ≠ a • u := by
    intro hz
    have he : (Pi.single l (1:K) : Fin 4 → K) = a • (Pi.single k (1:K) : Fin 4 → K) := by
      apply hi
      rw [Matrix.mulVec_smul,hu,hv]
      exact hz
    have hh := congrFun he l
    simp [Ne.symm hkl] at hh
  exact globalWeightOptimum_no_constant_isotropicPlane P w m hw hm hcap hclock hopt V u v
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)) hu0 hvspan
    (extremalHessianPair_span_pair_zero L u v huu huv hvu hvv)

/-- Full closure of the affine-coordinate rank-at-most-two branch
of the actual positive-clock globally optimal source. -/
theorem globalWeightOptimum_rankTwo_no_affineCoordinate
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1)
    (hL : AllThreeMinorsZero (hessian (initialForm w m P))) (k : Fin 4) :
    hessian (initialForm w m P) k k ≠ 0 := by
  classical
  intro hkk
  let L := initialForm w m P
  have hD : 0 < (pderiv k L).totalDegree := by
    by_contra hn
    have hz : (pderiv k L).totalDegree = 0 := by omega
    exact globalWeightOptimum_no_constant_partial P w m hw hm hcap hclock hopt hdet k _
      (totalDegree_eq_zero_iff_eq_C.mp hz)
  obtain ⟨M,p,hM,hpk,hkkQ,hkpQ,hr⟩ :=
    rankTwo_affine_exists_constantRatio_chart L k hkk hL hD
  let Q := weightedLinearSubstitution M L
  obtain ⟨N,l,hN,hkl,hzero⟩ :=
    rankTwo_affine_constantRatio_zeroPlane Q k p hpk hkkQ hkpQ
      (rankTwo_allThreeMinorsZero_substitution L M hL) hr
  apply globalWeightOptimum_no_zero_plane_arbitraryChart P w m hw hm hcap hclock hopt
    (M*N) (by rw [Matrix.det_mul,hM,hN,mul_one]) k l hkl
  dsimp only at hzero ⊢
  rw [← weightedLinearSubstitution_comp]
  exact hzero

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_affine_exists_constantRatio_chart
#print axioms HC4.Polynomial.rankTwo_affine_constantRatio_zeroPlane
#print axioms HC4.Polynomial.globalWeightOptimum_rankTwo_no_affineCoordinate
