import HC4.Polynomial.RankOneHessianRatioRigidity
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Unconditional rank-one Hessian closure

Choose a nonzero evaluation of the highest ordinary homogeneous
component of the potential. A determinant-one column shear makes
this evaluation a pure power in one variable. Twice differentiating
produces the pure highest-degree Hessian pivot required by the
ratio rigidity theorem.

The auxiliary chart is not required to preserve the original
weights: its nonzero constant Hessian kernel is pulled back before
applying global extremal exclusion.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

private theorem rankOne_allOnes_cap (L : S K) :
    IsWeightLE (fun _ : Fin 4 => (1 : ℤ)) (L.totalDegree : ℤ) L := by
  intro u hu
  rw [weight_allOnes_eq_degree]
  exact_mod_cast MvPolynomial.le_totalDegree hu

private theorem rankOne_ordinaryInitial_eq_component (L : S K) (n : ℕ) :
    initialForm (fun _ : Fin 4 => (1 : ℤ)) (n : ℤ) L =
      MvPolynomial.homogeneousComponent n L := by
  ext u
  rw [coeff_initialForm, coeff_homogeneousComponent, weight_allOnes_eq_degree]
  change (if ((u.degree : ℕ) : ℤ) = (n : ℤ) then coeff u L else 0) =
      (if u.degree = n then coeff u L else 0)
  simp

private theorem rankOne_top_ne_zero (L : S K) (hD : 0 < L.totalDegree) :
    MvPolynomial.homogeneousComponent L.totalDegree L ≠ 0 := by
  classical
  intro hz
  have hle : L.totalDegree ≤ L.totalDegree - 1 := by
    change L.support.sup (fun u => u.sum fun _ e => e) ≤ _
    apply Finset.sup_le
    intro u hu
    have hb := MvPolynomial.le_totalDegree hu
    have hne : u.degree ≠ L.totalDegree := by
      intro he
      have hc := congrArg (coeff u) hz
      rw [coeff_homogeneousComponent, if_pos he, coeff_zero] at hc
      exact (mem_support_iff.mp hu) hc
    change u.sum (fun _ e => e) ≠ L.totalDegree at hne
    omega
  omega

/-- A homogeneous polynomial vanishing in its pure axis coefficient
vanishes on the whole corresponding coordinate line. -/
private theorem rankOne_homogeneous_axis_zero
    (F : S K) (n : ℕ) (hF : F.IsHomogeneous n)
    (k : Fin 4) (a : K) (h : coeff (Finsupp.single k n) F = 0) :
    MvPolynomial.eval (Pi.single k a) F = 0 := by
  classical
  calc
    _ = ∑ u ∈ F.support, MvPolynomial.eval (Pi.single k a) (monomial u (coeff u F)) := by
      rw [← map_sum, ← F.as_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hcoef := mem_support_iff.mp hu
      have hdeg : u.degree = n := by
        have he := hF hcoef
        simpa only [Finsupp.degree_eq_weight_one] using he
      have hex : ∃ j ∈ u.support, j ≠ k := by
        by_contra hn
        push_neg at hn
        have he : u = Finsupp.single k (u k) := by
          ext j
          by_cases hj : j = k
          · subst j
            simp
          · have hz : u j = 0 := by
              by_contra hne
              exact hj (hn j (Finsupp.mem_support_iff.mpr hne))
            simp [hz, hj, Ne.symm hj]
        have hk : u k = n := by
          rw [he, Finsupp.degree_single] at hdeg
          exact hdeg
        exact hcoef (by rw [he, hk, h])
      obtain ⟨j,hj,hjk⟩ := hex
      rw [MvPolynomial.eval_monomial]
      unfold Finsupp.prod
      have hp : (∏ i ∈ u.support, (Pi.single k a : Fin 4 → K) i ^ u i) = 0 := by
        apply Finset.prod_eq_zero hj
        rw [Pi.single_eq_of_ne hjk]
        exact zero_pow (Finsupp.mem_support_iff.mp hj)
      rw [hp, mul_zero]

/-- The full degree of a nonaffine potential is visible as a
pure power after an actual determinant-one linear substitution. -/
theorem rankOne_exists_purePower_chart (L : S K) (hD : 0 < L.totalDegree) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (k : Fin 4),
      M.det = 1 ∧
      coeff (Finsupp.single k L.totalDegree) (weightedLinearSubstitution M L) ≠ 0 := by
  classical
  let D := L.totalDegree
  let F := MvPolynomial.homogeneousComponent D L
  have hF : F.IsHomogeneous D := homogeneousComponent_isHomogeneous _ _
  have hF0 : F ≠ 0 := rankOne_top_ne_zero L hD
  have hex : ∃ d : Fin 4 → K, MvPolynomial.eval d F ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hF0 (hF.eq_zero_of_forall_eval_eq_zero hn)
  obtain ⟨d,hd⟩ := hex
  have hd0 : d ≠ 0 := by
    intro he
    apply hd
    rw [he, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    change coeff 0 (homogeneousComponent D L) = 0
    rw [coeff_homogeneousComponent, Finsupp.degree_zero, if_neg (by omega)]
  have hdk : ∃ k, d k ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hd0 (funext hn)
  obtain ⟨k,hk⟩ := hdk
  let M := extremalKernelShear d k
  let Q := weightedLinearSubstitution M L
  let G := homogeneousComponent D Q
  have hG : G.IsHomogeneous D := homogeneousComponent_isHomogeneous _ _
  have hGF : G = weightedLinearSubstitution M F := by
    change homogeneousComponent D (weightedLinearSubstitution M L) =
      weightedLinearSubstitution M (homogeneousComponent D L)
    rw [← rankOne_ordinaryInitial_eq_component (weightedLinearSubstitution M L) D,
      ← rankOne_ordinaryInitial_eq_component L D]
    exact weightedLinearSubstitution_initialForm _ M (by simp) _ _
  have hMd : M *ᵥ (Pi.single k (d k) : Fin 4 → K) = d := by
    funext i
    change (∑ j : Fin 4, M i j * (Pi.single k (d k) : Fin 4 → K) j) = d i
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
      change extremalKernelShear d k i k * d k = d i
      rw [extremalKernelShear_column d k hk i, div_mul_cancel₀ _ hk]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · simp
  refine ⟨M,k,extremalKernelShear_det d k,?_⟩
  intro hc
  have hcG : coeff (Finsupp.single k D) G = 0 := by
    change coeff _ (homogeneousComponent D Q) = 0
    rw [coeff_homogeneousComponent, Finsupp.degree_single, if_pos rfl]
    exact hc
  have he := rankOne_homogeneous_axis_zero G D hG k (d k) hcG
  rw [hGF, weightedLinearSubstitution_eval, hMd] at he
  exact hd he

private theorem rankOne_hessian_degree_le (L : S K) (D : ℕ)
    (hD : 2 ≤ D) (hdeg : L.totalDegree ≤ D) (i j : Fin 4) :
    (hessian L i j).totalDegree ≤ D-2 := by
  have hcap : IsWeightLE (fun _ : Fin 4 => (1 : ℤ)) (D : ℤ) L := by
    intro u hu
    rw [weight_allOnes_eq_degree]
    exact_mod_cast (MvPolynomial.le_totalDegree hu).trans hdeg
  have hh := hcap.hessian_entry i j
  change (hessian L i j).support.sup (fun u => u.sum fun _ e => e) ≤ _
  apply Finset.sup_le
  intro u hu
  have he := hh hu
  change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) u ≤ (D : ℤ) - 1 - 1 at he
  rw [weight_allOnes_eq_degree] at he
  omega

private theorem rankOne_purePower_hessian_coeff
    (Q : S K) (n : ℕ) (k : Fin 4)
    (h : coeff (Finsupp.single k (n+2)) Q ≠ 0) :
    coeff (Finsupp.single k n) (hessian Q k k) ≠ 0 := by
  classical
  rw [hessian_apply, coeff_pderiv_backport, coeff_pderiv_backport]
  have he : Finsupp.single k n + Finsupp.single k 1 + Finsupp.single k 1 =
      (Finsupp.single k (n+2) : Fin 4 →₀ ℕ) := by
    rw [← Finsupp.single_add, ← Finsupp.single_add]
  rw [he]
  apply mul_ne_zero (mul_ne_zero h ?_) ?_
  · have hn : (((n+1+1 : ℕ) : K)) ≠ 0 := by exact_mod_cast (show n+1+1 ≠ 0 by omega)
    simpa [Finsupp.add_apply, Finsupp.single_apply, Nat.cast_add] using hn
  · have hn : (((n+1 : ℕ) : K)) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    simpa [Finsupp.single_apply, Nat.cast_add] using hn

/-- Cross-product rank one is retained by every linear chart.
A single surviving original diagonal pivot suffices. -/
theorem rankOne_crossProducts_substitution
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K) (k : Fin 4)
    (hk : hessian L k k ≠ 0)
    (hf : Function.Injective (weightedLinearSubstitution M : S K →ₐ[K] S K))
    (hr : ∀ i j, hessian L k k * hessian L i j = hessian L i k * hessian L k j) :
    ∀ p i j, hessian (weightedLinearSubstitution M L) p p *
        hessian (weightedLinearSubstitution M L) i j =
      hessian (weightedLinearSubstitution M L) i p *
        hessian (weightedLinearSubstitution M L) p j := by
  classical
  let f := weightedLinearSubstitution M
  let T := M.map (MvPolynomial.C : K →+* S K)
  let A := (hessian L).map f.toRingHom
  let G := hessian (f L)
  let a := f (hessian L k k)
  let b (i : Fin 4) := ∑ u : Fin 4, T u i * A u k
  have ha : a ≠ 0 := by
    intro hz
    exact hk (hf (hz.trans (map_zero f).symm))
  have hs (i j : Fin 4) : A i j = A j i := by
    change f (hessian L i j) = f (hessian L j i)
    congr 1
    exact pderiv_comm_backport j i L
  have hA (i j : Fin 4) : a * A i j = A i k * A j k := by
    have hh := congrArg f (hr i j)
    simp only [map_mul] at hh
    change a * A i j = A i k * A k j at hh
    rw [hs k j] at hh
    exact hh
  have hG : G = T.transpose * A * T := weightedLinearSubstitution_hessian M L
  have hfactor (i j : Fin 4) : a * G i j = b i * b j := by
    rw [hG]
    change a * (∑ v : Fin 4, (∑ u : Fin 4, T u i * A u v) * T v j) =
      (∑ u : Fin 4, T u i * A u k) * (∑ v : Fin 4, T v j * A v k)
    calc
      _ = ∑ v : Fin 4, ∑ u : Fin 4, a * (T u i * A u v * T v j) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ v : Fin 4, ∑ u : Fin 4, (T u i * A u k) * (T v j * A v k) := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        calc
          a * (T u i * A u v * T v j) = T u i * T v j * (a * A u v) := by ring
          _ = T u i * T v j * (A u k * A v k) := by rw [hA]
          _ = _ := by ring
      _ = ∑ v : Fin 4, (∑ u : Fin 4, T u i * A u k) * (T v j * A v k) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_mul]
      _ = _ := by rw [Finset.mul_sum]
  intro p i j
  change G p p * G i j = G i p * G p j
  apply mul_left_cancel₀ (mul_ne_zero ha ha)
  calc
    (a*a)*(G p p * G i j) = (a*G p p)*(a*G i j) := by ring
    _ = (b p*b p)*(b i*b j) := by rw [hfactor, hfactor]
    _ = (b i*b p)*(b p*b j) := by ring
    _ = (a*G i p)*(a*G p j) := by rw [hfactor, hfactor]
    _ = (a*a)*(G i p*G p j) := by ring

/-- A determinant-one linear chart is an injective algebra map. -/
private theorem rankOne_substitution_injective (M : Matrix (Fin 4) (Fin 4) K)
    (hM : M.det = 1) : Function.Injective (weightedLinearSubstitution M : S K →ₐ[K] S K) := by
  intro p q h
  have he := congrArg (weightedLinearSubstitution M⁻¹) h
  change weightedLinearSubstitution M⁻¹ (weightedLinearSubstitution M p) =
    weightedLinearSubstitution M⁻¹ (weightedLinearSubstitution M q) at he
  rw [weightedLinearSubstitution_comp, weightedLinearSubstitution_comp,
    Matrix.mul_nonsing_inv M (by rw [hM]; exact isUnit_one),
    weightedLinearSubstitution_one, weightedLinearSubstitution_one] at he
  exact he

/-- A constant column proportionality produces a nonzero constant
kernel independently of how the columns were obtained. -/
private theorem rankOne_kernel_of_proportional_columns
    (Q : S K) (k l : Fin 4) (hl : l ≠ k) (c : K)
    (hcol : ∀ i : Fin 4, hessian Q i l = MvPolynomial.C c * hessian Q i k) :
    ∃ e : Fin 4 → K, e ≠ 0 ∧
      hessian Q *ᵥ (fun i => MvPolynomial.C (e i)) = 0 := by
  classical
  let e : Fin 4 → K := Pi.single l 1 - Pi.single k c
  have he0 : e ≠ 0 := by
    intro hz
    have he := congrFun hz l
    change (Pi.single l (1 : K) : Fin 4 → K) l -
      (Pi.single k c : Fin 4 → K) l = 0 at he
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hl, sub_zero] at he
    exact one_ne_zero he
  let C : K →+* S K := MvPolynomial.C
  have he : hessian Q *ᵥ (fun i => C (e i)) = 0 := by
    have hmap : (fun i => C (e i)) =
        (Pi.single l 1 : Fin 4 → S K) - Pi.single k (C c) := by
      funext i
      by_cases hi : i = l
      · subst i
        simp [e, Pi.single_apply, hl]
      · by_cases hj : i = k
        · subst i
          simp [e, Pi.single_apply, Ne.symm hl]
        · simp [e, Pi.single_apply, hi, hj]
    rw [hmap, Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single]
    funext i
    change hessian Q i l - hessian Q i k * C c = 0
    rw [hcol, mul_comm (C c), sub_self]
  exact ⟨e, he0, he⟩

/-- Use the already verified ratio theorem in a pure-pivot chart. -/
private theorem rankOne_kernel_of_purePivot
    (Q : S K) (k : Fin 4) (n : ℕ)
    (hA : coeff (Finsupp.single k n) (hessian Q k k) ≠ 0)
    (hdeg : ∀ i j : Fin 4, (hessian Q i j).totalDegree ≤ n)
    (hR : ∀ i j : Fin 4, hessian Q k k * hessian Q i j =
      hessian Q i k * hessian Q k j) :
    ∃ e : Fin 4 → K, e ≠ 0 ∧
      hessian Q *ᵥ (fun i => MvPolynomial.C (e i)) = 0 := by
  classical
  have hA0 : hessian Q k k ≠ 0 := by
    intro hz
    exact hA (by rw [hz,coeff_zero])
  obtain ⟨l,hl⟩ : ∃ l : Fin 4, l ≠ k := exists_ne k
  have hminor : hessian Q k k * hessian Q l l = (hessian Q k l)^2 := by
    have he := hR l l
    rw [show hessian Q l k = hessian Q k l from pderiv_comm_backport k l Q] at he
    simpa only [pow_two] using he
  obtain ⟨c,hc⟩ := rankOneHessian_ratio_constant_of_purePivot Q k l n hA
    (hdeg k k) (hdeg k l) hminor
  have hcol (i : Fin 4) : hessian Q i l = MvPolynomial.C c * hessian Q i k := by
    apply mul_left_cancel₀ hA0
    calc
      hessian Q k k * hessian Q i l = hessian Q i k * hessian Q k l := hR i l
      _ = hessian Q k k * (MvPolynomial.C c * hessian Q i k) := by rw [hc]; ring
  exact rankOne_kernel_of_proportional_columns Q k l hl c hcol

/-- Constant directional derivatives transform by the original
ground-field matrix, with no invertibility needed for this identity. -/
theorem rankOne_directionalDerivative_substitution
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K) (e : Fin 4 → K) :
    extremalDirectionalDerivative e (weightedLinearSubstitution M L) =
      weightedLinearSubstitution M (extremalDirectionalDerivative (M *ᵥ e) L) := by
  classical
  let f := weightedLinearSubstitution M
  let C : K →+* S K := MvPolynomial.C
  have hC (a : K) : f (C a) = C a := f.commutes a
  unfold extremalDirectionalDerivative
  change (∑ i : Fin 4, pderiv i (f L) * C (e i)) =
    f (∑ j : Fin 4, pderiv j L * C ((M *ᵥ e) j))
  have hpartial (i : Fin 4) : pderiv i (f L) =
      ∑ j : Fin 4, f (pderiv j L) * C (M j i) :=
    weightedLinearSubstitution_partial M L i
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, f (pderiv j L) * C (M j i) * C (e i) := by
      simp only [hpartial, Finset.sum_mul]
    _ = ∑ j : Fin 4, ∑ i : Fin 4, f (pderiv j L) * C (M j i) * C (e i) :=
      Finset.sum_comm
    _ = ∑ j : Fin 4, f (pderiv j L) * C ((M *ᵥ e) j) := by
      apply Finset.sum_congr rfl
      intro j _
      change (∑ i : Fin 4, f (pderiv j L) * C (M j i) * C (e i)) =
        f (pderiv j L) * C (∑ i : Fin 4, M j i * e i)
      simp only [map_sum, map_mul, Finset.mul_sum, mul_assoc]
    _ = _ := by simp only [map_sum, map_mul, hC]

/-- The converse of directional-derivative integration. -/
theorem rankOne_kernel_of_constant_directionalDerivative
    (L : S K) (d : Fin 4 → K) (c : K)
    (hc : extremalDirectionalDerivative d L = MvPolynomial.C c) :
    hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  funext j
  have he := congrArg (pderiv j) hc
  change pderiv j (extremalDirectionalDerivative d L) = pderiv j (MvPolynomial.C c) at he
  rw [pderiv_C, extremalDirectionalDerivative, map_sum] at he
  change (∑ i : Fin 4, hessian L j i * MvPolynomial.C (d i)) = 0
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (pderiv i L), MvPolynomial.pderiv_C_mul, mul_comm,
    pderiv_comm_backport j i, hessian_apply]

/-- Pull a constant kernel back through an actual determinant-one chart.
Use the integrated directional derivative, so no invertibility or
instance search over polynomial matrices is needed. -/
theorem rankOne_constantKernel_pullback
    (L : S K) (M : Matrix (Fin 4) (Fin 4) K) (hM : M.det = 1)
    (e : Fin 4 → K) (he0 : e ≠ 0)
    (he : hessian (weightedLinearSubstitution M L) *ᵥ
      (fun i => MvPolynomial.C (e i)) = 0) :
    ∃ d : Fin 4 → K, d ≠ 0 ∧ hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  let d := M *ᵥ e
  have hd0 : d ≠ 0 := by
    have hi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hM]; exact isUnit_one))
    intro hz
    apply he0
    apply hi
    rw [Matrix.mulVec_zero]
    exact hz
  obtain ⟨c,hc⟩ := extremalDirectionalDerivative_eq_C_of_kernel e
    (weightedLinearSubstitution M L) he
  rw [rankOne_directionalDerivative_substitution] at hc
  have hf := rankOne_substitution_injective M hM
  have hC : weightedLinearSubstitution M (MvPolynomial.C c) = MvPolynomial.C c :=
    (weightedLinearSubstitution M).commutes c
  have hd : extremalDirectionalDerivative d L = MvPolynomial.C c :=
    hf (hc.trans hC.symm)
  exact ⟨d,hd0,rankOne_kernel_of_constant_directionalDerivative L d c hd⟩

/-- Extract a pure-pivot chart with the rank-one relations and degree
bounds already transported, keeping all witnesses on the same chart. -/
private theorem rankOne_exists_purePivot_chart
    (L : S K) (hD : 2 ≤ L.totalDegree) (p : Fin 4)
    (hp : hessian L p p ≠ 0)
    (hr : ∀ i j : Fin 4, hessian L p p * hessian L i j =
      hessian L i p * hessian L p j) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (k : Fin 4) (n : ℕ),
      M.det = 1 ∧
      let Q := weightedLinearSubstitution M L
      coeff (Finsupp.single k n) (hessian Q k k) ≠ 0 ∧
      (∀ i j : Fin 4, (hessian Q i j).totalDegree ≤ n) ∧
      (∀ i j : Fin 4, hessian Q k k * hessian Q i j =
        hessian Q i k * hessian Q k j) := by
  classical
  obtain ⟨M,k,hM,hpure⟩ := rankOne_exists_purePower_chart L (by omega)
  let Q := weightedLinearSubstitution M L
  let n := L.totalDegree - 2
  have hn : n+2 = L.totalDegree := by dsimp [n]; omega
  have hQdeg : Q.totalDegree ≤ L.totalDegree := weightedLinearSubstitution_totalDegree_le M L
  have hA : coeff (Finsupp.single k n) (hessian Q k k) ≠ 0 :=
    rankOne_purePower_hessian_coeff Q n k (by rw [hn]; exact hpure)
  have hdeg (i j : Fin 4) : (hessian Q i j).totalDegree ≤ n :=
    rankOne_hessian_degree_le Q L.totalDegree hD hQdeg i j
  have hf := rankOne_substitution_injective M hM
  have hR := rankOne_crossProducts_substitution L M p hp hf hr
  exact ⟨M,k,n,hM,hA,hdeg,hR k⟩

/-- A Hessian of rank at most one in four variables has a nonzero
constant kernel vector, without homogeneity assumptions. -/
theorem rankOneHessian_exists_constantKernel
    (L : S K)
    (hr : ∀ k i j : Fin 4, hessian L k k * hessian L i j =
      hessian L i k * hessian L k j) :
    ∃ d : Fin 4 → K, d ≠ 0 ∧ hessian L *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  by_cases hzero : hessian L = 0
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro he
      exact one_ne_zero (congrFun he 0)
    · rw [hzero, Matrix.zero_mulVec]
  have hD : 2 ≤ L.totalDegree := by
    by_contra hn
    apply hzero
    apply Matrix.ext
    intro i j
    exact eq_zero_of_nonnegativeWeight_negative_cap (fun _ : Fin 4 => (1 : ℤ))
      (by simp) _ (by omega) _ ((rankOne_allOnes_cap L).hessian_entry i j)
  have hex : ∃ k : Fin 4, hessian L k k ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hzero
    apply Matrix.ext
    intro i j
    have he := hr i j j
    rw [hn i, zero_mul, show hessian L j i = hessian L i j from
      pderiv_comm_backport i j L] at he
    exact (mul_eq_zero.mp he.symm).elim id id
  obtain ⟨p,hp⟩ := hex
  obtain ⟨M,k,n,hM,hA,hdeg,hR⟩ := rankOne_exists_purePivot_chart L hD p hp (hr p)
  obtain ⟨e,he0,he⟩ := rankOne_kernel_of_purePivot (weightedLinearSubstitution M L)
    k n hA hdeg hR
  exact rankOne_constantKernel_pullback L M hM e he0 he

/-- The rank-at-most-one branch of the actual extremal leading
Hessian is impossible. -/
theorem globalWeightOptimum_not_rankAtMostOne
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1) :
    let H := hessian (initialForm w m P)
    ¬ (∀ k i j : Fin 4, H k k * H i j = H i k * H k j) := by
  dsimp only
  intro hr
  obtain ⟨d,hd,hker⟩ := rankOneHessian_exists_constantKernel (initialForm w m P) hr
  exact hd (globalWeightOptimum_no_constantHessianKernel P w m hw hm hcap hclock hopt hdet d hker)

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankOneHessian_exists_constantKernel
#print axioms HC4.Polynomial.globalWeightOptimum_not_rankAtMostOne
