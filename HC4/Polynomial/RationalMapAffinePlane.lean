import HC4.Polynomial.RationalCharacteristicRankTwoClosure

/-!
# Source-independent rational Jacobian rigidity

Experimental extraction of the algebraic rank-two argument from the
verified anchored proof. The frame and straight-direction arguments
generalize the source-level proofs, without modifying the HC4 proof.
-/

namespace HC4.Polynomial.RankThreeCubic
open MvPolynomial
open scoped Matrix BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
set_option maxHeartbeats 8000000

theorem rankTwo_polynomial_frameTensor
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ M P : Matrix (Fin 3) (Fin 3) (E K), M.det ≠ 0 ∧
      M * P = 1 ∧ P * M = 1 ∧
      rationalCharacteristicJacobian V * M = M * rankTwo_jordanBlock ∧
      (∀ i : Fin 3, (P * rankTwo_matrixDeriv
        (rankTwo_directionalDerivation (fun k => M k 0))
        (rationalCharacteristicJacobian V) * M) i 0 = 0) ∧
      (P * rankTwo_matrixDeriv
        (rankTwo_directionalDerivation (fun k => M k 1))
        (rationalCharacteristicJacobian V) * M) 2 1 = 0 := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := (hessian f).map (algebraMap (B K) (E K))
  let J : Matrix (Fin 3) (Fin 3) (E K) := rankTwo_jordanBlock
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    change algebraMap (B K) (E K) (pderiv i (pderiv j f)) =
      algebraMap (B K) (E K) (pderiv j (pderiv i f))
    rw [HC4.Newton.pderiv_comm_backport]
  have hminor : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h ⟨a, i, b, j, hz⟩
  obtain ⟨_, h2, _, hleft, _⟩ := rankTwo_square_frontier N h3 hminor
  obtain ⟨M, P, hd, hMP, hPM, hNM⟩ := rankTwo_exists_jordanFrame N hleft h2
  let G := M.transpose * H * M
  let D (l : Fin 3) := rankTwo_directionalDerivation (fun k => M k l)
  let U (l : Fin 3) := P * rankTwo_matrixDeriv (D l) N * M
  let T (l : Fin 3) := M.transpose * rankTwo_matrixDeriv (D l) H * M
  have hG : G.transpose = G := by
    change (M.transpose * H * M).transpose = M.transpose * H * M
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hH, Matrix.mul_assoc]
  have hJG : J.transpose * G = G * J := by
    have he : P * N * M = J := by
      rw [Matrix.mul_assoc, hNM, ← Matrix.mul_assoc, hPM, one_mul]
    have h := rationalAffine_similarity_selfAdjoint M P N H hMP hself
    rw [he] at h
    exact h
  have hform := rankTwo_jordan_hessian_form G hG hJG
  have hGdet : G.det ≠ 0 := by
    change (M.transpose * H * M).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hd
      hreg) hd
  have ha : G 0 2 ≠ 0 :=
    rankTwo_jordan_hessian_pivot_ne_zero G hGdet hform
  have hUs (i j l : Fin 3) : U l i j = U j i l := by
    change (P * rankTwo_matrixDeriv (D l) N * M) i j =
      (P * rankTwo_matrixDeriv (D j) N * M) i l
    rw [rankTwo_matrixDeriv_directional, rankTwo_matrixDeriv_directional]
    exact rankTwo_transportTensor_symm P M
      (fun k => rankTwo_matrixDeriv (rationalCharacteristicPartial k) N)
      (rankTwo_velocityTensor_symm V) i j l
  have hTs (i j l : Fin 3) : T l i j = T j i l := by
    change (M.transpose * rankTwo_matrixDeriv (D l) H * M) i j =
      (M.transpose * rankTwo_matrixDeriv (D j) H * M) i l
    rw [rankTwo_matrixDeriv_directional, rankTwo_matrixDeriv_directional]
    apply rankTwo_transportTensor_symm
    intro i j l
    change rankTwo_matrixDeriv (rationalCharacteristicPartial l) H i j =
      rankTwo_matrixDeriv (rationalCharacteristicPartial j) H i l
    exact rankTwo_hessianTensor_symm f i j l
  have hU3 (l : Fin 3) : (J * J) * U l + J * U l * J + U l * (J * J) = 0 :=
    rankTwo_transport_cubeDerivative N M P J _ hMP hPM hNM
      (rankTwo_cubeDerivative (D l) N h3)
  have hHN : (H * N).transpose = H * N := by
    rw [Matrix.transpose_mul, hH, hself]
  have hUT (l : Fin 3) : (T l * J + G * U l).transpose = T l * J + G * U l :=
    rankTwo_transport_selfAdjointDerivative N H M P J _ _ hMP hNM
      (rankTwo_selfAdjointDerivative (D l) H N hHN)
  have hz : U 1 2 1 = 0 := by
    apply rankTwo_jordan_frobenius_tensor (G 0 2) (G 1 2) (G 2 2) ha U T
      hUs hTs hU3
    intro l
    have h := hUT l
    rw [hform] at h
    exact h
  have hc0 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).1
  have hc1 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).2.1
  have hc2 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (U l) (hU3 l)).2.2
  have h01 : U 0 2 1 = 0 := (hUs 2 1 0).trans (hc0 1)
  have h02 : U 0 2 2 = 0 := (hUs 2 2 0).trans (hc0 2)
  have h10 : U 0 1 0 = 0 := by
    have h := hc1 0
    rw [h01, zero_add] at h
    exact h
  have h11 : U 0 1 1 = 0 := by
    have h := hc1 1
    rw [hz, zero_add] at h
    exact (hUs 1 1 0).trans h
  have h00 : U 0 0 0 = 0 := by
    have h := hc2 0
    rw [h02, h11, zero_add, zero_add] at h
    exact h
  refine ⟨M, P, hd, hMP, hPM, hNM, ?_, hz⟩
  intro i
  change U 0 i 0 = 0
  fin_cases i
  · exact h00
  · exact h10
  · exact hc0 0

theorem rankTwo_polynomial_straightDirection
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w : Fin 3 → E K) (k : Fin 3),
      w k = 1 ∧ rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (w i) = 0) ∧
      (∀ z ∈ IntermediateField.adjoin K (Set.range (fun i : Fin 3 => V (.inr i))),
        rankTwo_directionalDerivation w z = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  obtain ⟨M, P, hd, hMP, hPM, hNM, hcol, _⟩ :=
    rankTwo_polynomial_frameTensor f V h3 hreg hself hm
  let u : Fin 3 → E K := fun k => M k 0
  have hu0 : u ≠ 0 := by
    intro h
    apply hd
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    exact congrFun h i
  have hu : N *ᵥ u = 0 := by
    funext i
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (E K) => A i 0) hNM
    change (N *ᵥ u) i = (M * (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K))) i 0 at he
    have hj (k : Fin 3) : (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K)) k 0 = 0 := by
      fin_cases k <;> rfl
    have hz : (M * (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K))) i 0 = 0 := by
      rw [Matrix.mul_apply]
      simp only [hj, mul_zero, Finset.sum_const_zero]
    exact he.trans hz
  have hzero : rankTwo_matrixDeriv (rankTwo_directionalDerivation u) N *ᵥ u = 0 :=
    rankTwo_frame_firstColumn_zero M P _ hMP hcol
  have hex : ∃ k : Fin 3, u k ≠ 0 := by
    by_contra h
    apply hu0
    funext k
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  let s := (u k)⁻¹
  let w : Fin 3 → E K := s • u
  have hwk : w k = 1 := inv_mul_cancel₀ hk
  have hw : N *ᵥ w = 0 := by
    change N *ᵥ (s • u) = 0
    rw [Matrix.mulVec_smul, hu, smul_zero]
  have hscale : rankTwo_matrixDeriv (rankTwo_directionalDerivation w) N =
      s • rankTwo_matrixDeriv (rankTwo_directionalDerivation u) N := by
    apply Matrix.ext
    intro i j
    exact rankTwo_directionalDerivation_scale s u (N i j)
  have hz : rankTwo_matrixDeriv (rankTwo_directionalDerivation w) N *ᵥ w = 0 := by
    rw [hscale, show w = s • u from rfl, Matrix.smul_mulVec,
      Matrix.mulVec_smul, hzero, smul_zero, smul_zero]
  have hacc := rankTwo_acceleration_in_kernel V w hw hz
  have hr : 2 ≤ N.rank := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h (rankTwo_rank_ge_two_of_minor N a i b j hz)
  let z : Fin 3 → E K := fun i => rankTwo_directionalDerivation w (w i)
  have hzk : z k = 0 := by
    change rankTwo_directionalDerivation w (w k) = 0
    rw [hwk, Derivation.map_one_eq_zero]
  refine ⟨w, k, hwk, hw, ?_, ?_⟩
  · intro i
    have he := rankTwo_rightKernel_minors_zero N hr w z hw hacc k i
    rw [hwk, hzk, one_mul, mul_zero] at he
    exact he
  · intro z hz
    apply rationalDerivation_zero_of_mem_adjoin (rankTwo_directionalDerivation w) _ _ z hz
    rintro x ⟨i, rfl⟩
    rw [rankTwo_directionalDerivation_apply]
    have he := congrFun hw i
    change (∑ j : Fin 3, N i j * w j) = 0 at he
    simpa only [N, rationalCharacteristicJacobian, mul_comm] using he

theorem rankTwo_polynomial_normalizedDualDirection
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w b : Fin 3 → E K) (k : Fin 3),
      b k = 1 ∧
      rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      ((hessian f).map (algebraMap (B K) (E K))) *ᵥ w = b ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      b ⬝ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i : Fin 3, rankTwo_directionalDerivation w (V (.inr i)) = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := ((hessian f).map (algebraMap (B K) (E K)))
  have hminor : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h ⟨a, i, b, j, hz⟩
  obtain ⟨hr, hs, _, hl, _⟩ := rankTwo_square_frontier N h3 hminor
  have hex : ∃ i j : Fin 3, (N * N) i j ≠ 0 := by
    by_contra h
    apply hs
    apply Matrix.ext
    intro i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  let u : Fin 3 → E K := fun k => N k j
  let w₀ : Fin 3 → E K := N *ᵥ u
  have hwcol (k : Fin 3) : w₀ k = (N * N) k j := rfl
  have hw₀ : w₀ ≠ 0 := by
    intro hz
    exact hij ((hwcol i).symm.trans (congrFun hz i))
  have hk₀ : N *ᵥ w₀ = 0 := by
    funext k
    change (∑ l : Fin 3, N k l * w₀ l) = 0
    simp only [hwcol]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (E K) => M k j) hl
  let b₀ := H *ᵥ w₀
  obtain ⟨hb₀, hleft₀⟩ := rankTwo_hessian_leftNormal H N
    hreg hself w₀ hw₀ hk₀
  have hexk : ∃ k : Fin 3, b₀ k ≠ 0 := by
    by_contra h
    apply hb₀
    funext k
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hexk
  let w : Fin 3 → E K := (b₀ k)⁻¹ • w₀
  let b : Fin 3 → E K := (b₀ k)⁻¹ • b₀
  have hb : b k = 1 := by
    change (b₀ k)⁻¹ * b₀ k = 1
    exact inv_mul_cancel₀ hk
  have hw : N *ᵥ w = 0 := by
    rw [show w = (b₀ k)⁻¹ • w₀ from rfl, Matrix.mulVec_smul, hk₀, smul_zero]
  have hh : H *ᵥ w = b := by
    rw [show w = (b₀ k)⁻¹ • w₀ from rfl, Matrix.mulVec_smul]
  have hleft : b ᵥ* N = 0 := by
    rw [show b = (b₀ k)⁻¹ • b₀ from rfl, Matrix.smul_vecMul, hleft₀, smul_zero]
  have hnull : b ⬝ᵥ w = 0 := by
    have he : w = N *ᵥ ((b₀ k)⁻¹ • u) := by
      rw [Matrix.mulVec_smul]
    rw [he, Matrix.dotProduct_mulVec, hleft]
    simp [dotProduct]
  refine ⟨w, b, k, hb, hw, hh, hleft, hnull,
    rankTwo_normalizedLeftNormal_invariant V w b hr hw hleft k hb, ?_⟩
  intro i
  rw [rankTwo_directionalDerivation_apply]
  have he := congrFun hw i
  change (∑ j : Fin 3, N i j * w j) = 0 at he
  simpa only [N, rationalCharacteristicJacobian, mul_comm] using he

theorem rankTwo_polynomial_affineGradient
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w b : Fin 3 → E K) (k l : Fin 3) (c : E K),
      w k = 1 ∧ b l = 1 ∧ c ≠ 0 ∧
      rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      b ⬝ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (w i) = 0) ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i, rankTwo_fibreEval w (pderiv i f) =
        _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i f)) +
          _root_.Polynomial.X * _root_.Polynomial.C (c * b i)) ∧
      (∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := ((hessian f).map (algebraMap (B K) (E K)))
  obtain ⟨w, k, hk, hw, hww, _⟩ := rankTwo_polynomial_straightDirection f V h3 hreg hself hm
  obtain ⟨u, b, l, hl, hu, hH, hb, hn, _, _⟩ :=
    rankTwo_polynomial_normalizedDualDirection f V h3 hreg hself hm
  have hr : 2 ≤ N.rank := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h (rankTwo_rank_ge_two_of_minor N a i b j hz)
  have hprop : u = u k • w := by
    funext i
    have he := rankTwo_rightKernel_minors_zero N hr w u hw hu k i
    rw [hk, one_mul] at he
    change u i = u k * w i
    rw [he, mul_comm]
  have huk : u k ≠ 0 := by
    intro hz
    have he : u = 0 := by rw [hprop, hz, zero_smul]
    have hb0 : b = 0 := by rw [← hH, he, Matrix.mulVec_zero]
    have he' := congrFun hb0 l
    rw [hl] at he'
    exact one_ne_zero he'
  let c := (u k)⁻¹
  have hwprop : w = c • u := by
    funext i
    change w i = (u k)⁻¹ * u i
    have he : u i = u k * w i := congrFun hprop i
    rw [he, ← mul_assoc, inv_mul_cancel₀ huk, one_mul]
  have hh : H *ᵥ w = c • b := by
    rw [hwprop, Matrix.mulVec_smul, hH]
  have hn' : b ⬝ᵥ w = 0 := by
    rw [hwprop]
    change (∑ i : Fin 3, b i * (c * u i)) = 0
    have he : (∑ i : Fin 3, b i * (c * u i)) = c * (b ⬝ᵥ u) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hn, mul_zero]
  have hbb := rankTwo_normalizedLeftNormal_invariant V w b hr hw hb l hl
  change ((hessian f).map (algebraMap (B K) (E K))) *ᵥ w = c • b at hh
  obtain ⟨hg, hdw⟩ := rankTwo_fibre_affineGradient f w b c l
    hww hbb hl (inv_ne_zero huk) hn' hh
  exact ⟨w, b, k, l, c, hk, hl, inv_ne_zero huk, hw, hb, hn', hww, hbb, hg, hdw⟩

/-- No four-variable source or transport hypothesis is needed in rank two. -/
theorem rankTwo_polynomial_exists_constant_leftKernel
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  obtain ⟨w,b,k,l,c,hk,hl,hc,hw,hb,hn,hww,_,hg,hdw⟩ :=
    rankTwo_polynomial_affineGradient f V h3 hreg hself hm
  have hr : 2 ≤ (rationalCharacteristicJacobian V).rank := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h (rankTwo_rank_ge_two_of_minor _ a i b j hz)
  by_cases hz : rationalCharacteristicJacobian (rankTwo_directionLift w) = 0
  · obtain ⟨d, hd⟩ := rankTwo_direction_constant w hz
    have he : w = fun i => algebraMap K (E K) (d i) := funext hd
    have hdk : d k = 1 := by
      apply (algebraMap K (E K)).injective
      rw [← hd k, hk, map_one]
    rw [he] at hw hn
    exact rankTwo_constantDirection_leftKernel f V d b k l hr h3 hdk hl hw hb hn hreg hself
  · exact rankTwo_nonconstantDirection_leftKernel V w b k l hr h3 hk hl hw hn hb hww hdw hz

/-- All ranks in the source-independent setting. -/
theorem rationalJacobian_exists_constant_leftKernel
    (f : B K) (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hreg : (hessian f).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * rationalCharacteristicJacobian V) :
    ∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  have hreg' : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0 := by
    change ((algebraMap (B K) (E K)).mapMatrix (hessian f)).det ≠ 0
    rw [← RingHom.map_det]
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hreg
  by_cases hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b
  · by_cases hz : rationalCharacteristicJacobian V = 0
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro h
        exact one_ne_zero (congrFun h (0 : Fin 3))
      · rw [hz, Matrix.vecMul_zero]
    · obtain ⟨t,A,Q,hQ,hv⟩ := rankOne_commonParameter V hz hm
      obtain ⟨U,s,hs,hn⟩ := rationalCharacteristic_commonParameter_factor V t A Q hQ hv
      have hnc (c : K) : t ≠ algebraMap K (E K) c := by
        intro hc
        apply hz
        apply Matrix.ext
        intro i j
        rw [hn, hc, Derivation.map_algebraMap, mul_zero] <;> rfl
      obtain ⟨p,q,hqn,hcop,hpos,hr⟩ := rationalParameter_exists_reduced_nonconstant t hnc
      exact rankOne_exists_constant_leftKernel_of_derivative_factor
        f (rationalCharacteristicJacobian V) p q U s hs hqn hcop hpos
        (by intro i j; rw [hr]; exact hn i j) h3 hself hreg
  · exact rankTwo_polynomial_exists_constant_leftKernel f V h3 hreg' hself hm

/-- Explicit three-variable rational-map rigidity (compare Tang, Theorem 2.1).
The symmetrizer is the Hessian of a polynomial, not an arbitrary matrix. -/
theorem rationalMap_affinePlane
    (f : B K) (v : Fin 3 → E K)
    (h3 : (Matrix.of (fun i j : Fin 3 => rationalCharacteristicPartial j (v i))) ^ 3 = 0)
    (hreg : (hessian f).det ≠ 0)
    (hself : (Matrix.of (fun i j : Fin 3 => rationalCharacteristicPartial j (v i))).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) *
        Matrix.of (fun i j : Fin 3 => rationalCharacteristicPartial j (v i))) :
    ∃ (d : Fin 3 → K) (c : K), d ≠ 0 ∧
      (∑ i : Fin 3, algebraMap K (E K) (d i) * v i) = algebraMap K (E K) c := by
  let V := rankTwo_directionLift v
  obtain ⟨d, hd, hleft⟩ := rationalJacobian_exists_constant_leftKernel f V h3 hreg hself
  obtain ⟨c, hc⟩ := rationalCharacteristic_affine_of_constant_leftKernel V d hleft
  exact ⟨d, c, hd, hc⟩

end
end HC4.Polynomial.RankThreeCubic

#print axioms HC4.Polynomial.RankThreeCubic.rationalMap_affinePlane
