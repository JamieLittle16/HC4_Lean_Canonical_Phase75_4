import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitTiltedSchur
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import Mathlib.Tactic

/-!
# Tilted initial-form closure of the central reflected staircase

The earliest reflected-line departure supplies a unique maximal source
monomial in one honest total-deficit layer.  The preceding module transports
the corresponding affine tilt through the parameter-first Hessian and the
cleared binary Schur block.

This file consumes those two facts.  At parameter order q+s the identically
zero Schur determinant has one strictly maximal tilted contribution:
the selected principal Schur coefficient at order s times the nonzero
first-deficit principal coefficient at order q.  Every other convolution
term is either killed by the first-deficit gaps or is strictly lower in
tilted weight.  The maximal product is nonzero, a contradiction.

No repair state, auxiliary clock, source-coordinate interpretation of the
Schur alignment, or recursive reflected descent is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

/- Avoid the imported reverse aliases for pderiv 2/3 while doing direct
   monomial Hessian calculations below. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

universe u

private theorem isWeightLE_mono'
    {σ K : Type*} [CommRing K]
    {w : σ → ℤ} {a b : ℤ} {P : MvPolynomial σ K}
    (hab : a ≤ b) (hP : HC4.Polynomial.IsWeightLE w a P) :
    HC4.Polynomial.IsWeightLE w b P := by
  intro e he
  exact le_trans (hP he) hab

private theorem isWeightLE_finset_sum'
    {σ K ι : Type*} [CommRing K] [DecidableEq σ]
    (w : σ → ℤ) (M : ℤ) (S : Finset ι)
    (f : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ S, HC4.Polynomial.IsWeightLE w M (f i)) :
    HC4.Polynomial.IsWeightLE w M (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (HC4.Polynomial.isWeightLE_zero (K := K) w M)
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (by simp)).add
        (ih (fun i hi => hf i (by simp [hi])))

private theorem initialForm_finset_sum'
    {σ K ι : Type*} [CommRing K]
    (w : σ → ℤ) (M : ℤ) (S : Finset ι)
    (f : ι → MvPolynomial σ K) :
    HC4.Polynomial.initialForm w M (∑ i ∈ S, f i) =
      ∑ i ∈ S, HC4.Polynomial.initialForm w M (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, HC4.Polynomial.initialForm_add, ih,
        Finset.sum_insert ha]

private theorem coeff_mul_isWeightLE_of_two_zero_constants
    {σ K : Type*} [CommRing K] [DecidableEq σ]
    {w : σ → ℤ}
    {P Q : Polynomial (MvPolynomial σ K)}
    {s : ℕ} {a b : ℤ}
    (hspos : 0 < s)
    (hP0 : P.coeff 0 = 0)
    (hQ0 : Q.coeff 0 = 0)
    (hP : ∀ n : ℕ, 0 < n → n < s →
      HC4.Polynomial.IsWeightLE w a (P.coeff n))
    (hQ : ∀ n : ℕ, 0 < n → n < s →
      HC4.Polynomial.IsWeightLE w b (Q.coeff n)) :
    HC4.Polynomial.IsWeightLE w (a + b) ((P * Q).coeff s) := by
  rw [Polynomial.coeff_mul]
  let A : Finset (ℕ × ℕ) := Finset.antidiagonal s
  let f : (ℕ × ℕ) → MvPolynomial σ K :=
    fun x => P.coeff x.1 * Q.coeff x.2
  change HC4.Polynomial.IsWeightLE w (a + b) (∑ x ∈ A, f x)
  apply isWeightLE_finset_sum' w (a + b) A f
  intro x hx
  have hsum : x.1 + x.2 = s := by
    exact Finset.mem_antidiagonal.mp (by simpa [A] using hx)
  by_cases hx1 : x.1 = 0
  · simp [f, hx1, hP0]
  by_cases hx2 : x.2 = 0
  · simp [f, hx2, hQ0]
  have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hx1
  have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
  have hx1lt : x.1 < s := by omega
  have hx2lt : x.2 < s := by omega
  exact (hP x.1 hx1pos hx1lt).mul (hQ x.2 hx2pos hx2lt)

private theorem coeff_mul_isWeightLE_of_right_positive
    {σ K : Type*} [CommRing K] [DecidableEq σ]
    {w : σ → ℤ}
    {P Q : Polynomial (MvPolynomial σ K)}
    {s : ℕ} {a b : ℤ}
    (hspos : 0 < s)
    (hQ0 : Q.coeff 0 = 0)
    (hP : ∀ n : ℕ, n < s →
      HC4.Polynomial.IsWeightLE w a (P.coeff n))
    (hQ : ∀ n : ℕ, 0 < n → n ≤ s →
      HC4.Polynomial.IsWeightLE w b (Q.coeff n)) :
    HC4.Polynomial.IsWeightLE w (a + b) ((P * Q).coeff s) := by
  rw [Polynomial.coeff_mul]
  let A : Finset (ℕ × ℕ) := Finset.antidiagonal s
  let f : (ℕ × ℕ) → MvPolynomial σ K :=
    fun x => P.coeff x.1 * Q.coeff x.2
  change HC4.Polynomial.IsWeightLE w (a + b) (∑ x ∈ A, f x)
  apply isWeightLE_finset_sum' w (a + b) A f
  intro x hx
  have hsum : x.1 + x.2 = s := by
    exact Finset.mem_antidiagonal.mp (by simpa [A] using hx)
  by_cases hx2 : x.2 = 0
  · simp [f, hx2, hQ0]
  have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
  have hx1lt : x.1 < s := by omega
  have hx2le : x.2 ≤ s := by omega
  exact (hP x.1 hx1lt).mul (hQ x.2 hx2pos hx2le)

private theorem initialForm_coeff_mul_eq_single
    {σ K : Type*} [CommRing K]
    {w : σ → ℤ}
    {P Q : Polynomial (MvPolynomial σ K)}
    {N i₀ j₀ : ℕ} {M : ℤ}
    (hsum : i₀ + j₀ = N)
    (hother :
      ∀ x ∈ Finset.antidiagonal N, x ≠ (i₀, j₀) →
        HC4.Polynomial.initialForm w M
          (P.coeff x.1 * Q.coeff x.2) = 0) :
    HC4.Polynomial.initialForm w M ((P * Q).coeff N) =
      HC4.Polynomial.initialForm w M (P.coeff i₀ * Q.coeff j₀) := by
  classical
  rw [Polynomial.coeff_mul]
  rw [initialForm_finset_sum' w M (Finset.antidiagonal N)
    (fun x => P.coeff x.1 * Q.coeff x.2)]
  apply Finset.sum_eq_single (i₀, j₀)
  · intro x hx hne
    exact hother x hx hne
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr hsum)).elim

private theorem initialForm_coeff_mul_eq_zero
    {σ K : Type*} [CommRing K]
    {w : σ → ℤ}
    {P Q : Polynomial (MvPolynomial σ K)}
    {N : ℕ} {M : ℤ}
    (hall :
      ∀ x ∈ Finset.antidiagonal N,
        HC4.Polynomial.initialForm w M
          (P.coeff x.1 * Q.coeff x.2) = 0) :
    HC4.Polynomial.initialForm w M ((P * Q).coeff N) = 0 := by
  classical
  rw [Polynomial.coeff_mul]
  rw [initialForm_finset_sum' w M (Finset.antidiagonal N)
    (fun x => P.coeff x.1 * Q.coeff x.2)]
  exact Finset.sum_eq_zero (fun x hx => hall x hx)

private theorem tilted_binary_nonCancellation
    {σ K : Type*} [Field K] [CharZero K] [DecidableEq σ]
    {w : σ → ℤ}
    {A B C : Polynomial (MvPolynomial σ K)}
    {N i₀ j₀ : ℕ} {a c : ℤ}
    (hsum : i₀ + j₀ = N)
    (hAiLE : HC4.Polynomial.IsWeightLE w a (A.coeff i₀))
    (hCjLE : HC4.Polynomial.IsWeightLE w c (C.coeff j₀))
    (hAiTop :
      HC4.Polynomial.initialForm w a (A.coeff i₀) ≠ 0)
    (hCjTop :
      HC4.Polynomial.initialForm w c (C.coeff j₀) ≠ 0)
    (hACother :
      ∀ x ∈ Finset.antidiagonal N, x ≠ (i₀, j₀) →
        HC4.Polynomial.initialForm w (a + c)
          (A.coeff x.1 * C.coeff x.2) = 0)
    (hBB :
      ∀ x ∈ Finset.antidiagonal N,
        HC4.Polynomial.initialForm w (a + c)
          (B.coeff x.1 * B.coeff x.2) = 0)
    (hdet : A * C - B * B = 0) :
    False := by
  have hAC :=
    initialForm_coeff_mul_eq_single
      (w := w) (P := A) (Q := C) (M := a + c)
      hsum hACother
  have hBB0 :=
    initialForm_coeff_mul_eq_zero
      (w := w) (P := B) (Q := B) (M := a + c) hBB
  have htop :=
    HC4.Valuation.initialForm_mul_eq_mul_initialForm_of_isWeightLE
      (K := K) hAiLE hCjLE
  have hdesired :
      HC4.Polynomial.initialForm w (a + c)
          (A.coeff i₀ * C.coeff j₀) ≠ 0 := by
    rw [htop]
    exact mul_ne_zero hAiTop hCjTop
  have heq : A * C = B * B := sub_eq_zero.mp hdet
  have hcoeff : (A * C).coeff N = (B * B).coeff N :=
    congrArg (fun P : Polynomial (MvPolynomial σ K) => P.coeff N) heq
  have hzero :
      HC4.Polynomial.initialForm w (a + c) ((A * C).coeff N) = 0 := by
    rw [hcoeff]
    exact hBB0
  rw [hAC] at hzero
  exact hdesired hzero

private theorem eq_monomial_of_support_singleton'
    {K : Type*} [Field K]
    (Q : MvPolynomial (Fin 4) K)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ Q.support)
    (huniq : ∀ f ∈ Q.support, f = e) :
    Q = MvPolynomial.monomial e (MvPolynomial.coeff e Q) := by
  apply MvPolynomial.ext
  intro f
  by_cases hfe : f = e
  · subst f
    simp
  · have hfnot : f ∉ Q.support := by
      intro hf
      exact hfe (huniq f hf)
    have hfzero : MvPolynomial.coeff f Q = 0 :=
      MvPolynomial.notMem_support_iff.mp hfnot
    rw [hfzero, MvPolynomial.coeff_monomial]
    simp [hfe, Ne.symm hfe]

private theorem hessian_monomial_diagonal_ne_zero_of_two_le'
    {K : Type*} [Field K] [CharZero K]
    {e : Fin 4 →₀ ℕ} {z : K} {i : Fin 4}
    (hz : z ≠ 0) (hi : 2 ≤ e i) :
    HC4.Polynomial.hessian
        (MvPolynomial.monomial e z) i i ≠ 0 := by
  intro hzero
  have hmat := HC4.Polynomial.eval_one_hessian_monomial
    (K := K) e z
  have hii := congrFun (congrFun hmat i) i
  change
    MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (HC4.Polynomial.hessian
          (MvPolynomial.monomial e z) i i) =
      (z • HC4.Polynomial.exponentHessianCore (K := K) e) i i at hii
  have hzright :
      (z • HC4.Polynomial.exponentHessianCore (K := K) e) i i = 0 := by
    calc
      _ = MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
          (HC4.Polynomial.hessian
            (MvPolynomial.monomial e z) i i) := hii.symm
      _ = 0 := by rw [hzero]; simp
  have hei0 : (e i : K) ≠ 0 := by
    exact_mod_cast (show e i ≠ 0 by omega)
  have heim1 : (e i : K) - 1 ≠ 0 := by
    intro h
    have heq : (e i : K) = 1 := sub_eq_zero.mp h
    have heqNat : e i = 1 := by exact_mod_cast heq
    omega
  have hcore :
      (e i : K) * (e i : K) - (e i : K) ≠ 0 := by
    rw [show
      (e i : K) * (e i : K) - (e i : K) =
        (e i : K) * ((e i : K) - 1) by ring]
    exact mul_ne_zero hei0 heim1
  have hscalar :
      z * ((e i : K) * (e i : K) - (e i : K)) ≠ 0 :=
    mul_ne_zero hz hcore
  apply hscalar
  simpa [HC4.Polynomial.exponentHessianCore] using hzright

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

include G

set_option maxHeartbeats 800000 in
private theorem centralDeficit_leftTilt_impossible
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s m : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    {depart : Fin 4 →₀ ℕ}
    (hdepart : depart ∈ P.carrier.support)
    (horder : depart 1 + depart 2 = s)
    (hmissing : depart 2 = m)
    (hm3 : 3 ≤ m)
    (hbad : s < q + m * (J - q))
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 2 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 2 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 2 →
        f 1 + f 2 < q + f 2 * (J - q) →
        s ≤ f 1 + f 2)
    (hmax :
      ∀ f ∈ P.carrier.support,
        f 1 + f 2 = s →
        3 ≤ f 2 →
        f 1 + f 2 < q + f 2 * (J - q) →
        f 2 ≤ m) :
    False := by
  let dgap := J - q
  let w := firstDeficitLeftTiltWeight dgap
  let M : ℤ := (dgap : ℤ) * (m : ℤ) - (s : ℤ)
  let WX : ℤ := M - 2 * ((dgap : ℤ) - 1)
  let WC : ℤ := -(q : ℤ) + 2
  let H := G.centralDeficitSchurBlock
  let L := familyParameterLayer P.centralDeficitFamily s

  have hqpos : 0 < q := by
    rw [hq]
    exact G.firstDeficitOrder_pos
  have hdpos : 0 < dgap := by
    dsimp [dgap]
    omega
  have hdepart2 : 2 ≤ depart 2 := by
    rw [hmissing]
    omega
  have hqs : q < s := by
    have h2 := hmin2 depart hdepart hdepart2
    have hdOne : 1 ≤ dgap := by omega
    dsimp [dgap] at h2 hdOne
    omega
  have hspos : 0 < s := lt_trans hqpos hqs
  have hMq : -(q : ℤ) < M := by
    have hbZ :
        (s : ℤ) < (q : ℤ) + (m : ℤ) * (dgap : ℤ) := by
      dsimp [dgap]
      exact_mod_cast hbad
    dsimp [M]
    nlinarith

  have hfirst :
      ∃ e : Fin 4 →₀ ℕ,
        e ∈ G.firstDeficitLayer.support ∧
        e 1 = G.firstDeficitOrder ∧
        e 2 = 0 ∧
        ∀ f ∈ G.firstDeficitLayer.support, f = e := by
    rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
      hleft | hright
    · exact hleft
    · rcases hright with ⟨e, he, he1, he2, huniq⟩
      have heData := G.firstDeficitLayer_support he
      have hJle := hmin1 e heData.1 (by rw [he2, ← hq]; exact hqpos)
      exfalso
      rw [he1, he2, ← hq] at hJle
      omega
  rcases hfirst with ⟨e, he, he1, he2, huniq⟩

  let z := MvPolynomial.coeff e G.firstDeficitLayer
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hfirstMono :
      G.firstDeficitLayer = MvPolynomial.monomial e z :=
    eq_monomial_of_support_singleton' G.firstDeficitLayer he huniq

  have hA0 : H.schurA.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.active_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h
  have hB0 : H.schurB.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.offDiag_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h
  have hC0 : H.schurC.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.kernel_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h

  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a0 := H0 (0 : Fin 4) 0
  let b0 := H0 (0 : Fin 4) 3
  let c0 := H0 (3 : Fin 4) 0
  let d0 := H0 (3 : Fin 4) 3
  let Delta0 := a0 * d0 - b0 * c0

  have hbaseL : ∀ r t : Fin 3,
      (G.firstDeficitLeftActiveHessian r t).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          a0 b0 c0 d0 r t := by
    intro r t
    simpa [a0, b0, c0, d0, H0] using
      G.firstDeficitLeftActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r t
  have hbaseR : ∀ r t : Fin 3,
      (G.firstDeficitRightActiveHessian r t).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          a0 b0 c0 d0 r t := by
    intro r t
    simpa [a0, b0, c0, d0, H0] using
      G.firstDeficitRightActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r t
  have hdiagRightSource :
      HC4.Polynomial.hessian G.firstDeficitLayer
        (2 : Fin 4) 2 = 0 := by
    rw [hfirstMono]
    rw [HC4.Polynomial.hessian_apply]
    simp [MvPolynomial.pderiv_monomial, he2]
  have hdiagRight :
      (G.firstDeficitRightActiveHessian 1 1).coeff
          G.firstDeficitOrder = 0 := by
    unfold firstDeficitRightActiveHessian
    simp [firstDeficitRightActiveIndex]
    rw [parameterFirstHessian_coeff]
    simpa [firstDeficitLayer] using hdiagRightSource
  have hAq0 : H.schurA.coeff q = 0 := by
    change G.centralDeficitSchurBlock.schurA.coeff q = 0
    rw [G.centralDeficitSchurA_eq_rightRoofDet, hq]
    rw [HC4.Polynomial.coeff_det_polynomialMatrix3_gap
      G.firstDeficitOrder_pos
      G.firstDeficitRightActiveHessian
      (fun r t => G.rightActive_gap r t)
      a0 b0 c0 d0 hbaseR]
    rw [hdiagRight]
    simp

  have hCqne : H.schurC.coeff q ≠ 0 := by
    change G.centralDeficitSchurBlock.schurC.coeff q ≠ 0
    rw [G.centralDeficitSchurC_eq_leftRoofDet]
    simpa [hq] using
      G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
        hthree houtThree he he1 he2 huniq

  have hfaceHom :
      MvPolynomial.IsWeightedHomogeneous w G.exposure.face 0 := by
    rw [G.exposure_face_eq]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [weight_firstDeficitLeftTiltWeight]
    simp [w, dgap, G.central_one_zero, G.central_two_zero]
  have ha0Hom :
      MvPolynomial.IsWeightedHomogeneous w a0 0 := by
    dsimp [a0, H0]
    simpa [w, firstDeficitLeftTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (0 : Fin 4) 0
  have hb0Hom :
      MvPolynomial.IsWeightedHomogeneous w b0 0 := by
    dsimp [b0, H0]
    simpa [w, firstDeficitLeftTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (0 : Fin 4) 3
  have hc0Hom :
      MvPolynomial.IsWeightedHomogeneous w c0 0 := by
    dsimp [c0, H0]
    simpa [w, firstDeficitLeftTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (3 : Fin 4) 0
  have hd0Hom :
      MvPolynomial.IsWeightedHomogeneous w d0 0 := by
    dsimp [d0, H0]
    simpa [w, firstDeficitLeftTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (3 : Fin 4) 3
  have ha0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous ha0Hom
  have hb0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hb0Hom
  have hc0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hc0Hom
  have hd0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hd0Hom
  have hDelta0LE : HC4.Polynomial.IsWeightLE w 0 Delta0 := by
    dsimp [Delta0]
    simpa using (ha0LE.mul hd0LE).sub (hb0LE.mul hc0LE)
  have hDelta0Top :
      HC4.Polynomial.initialForm w 0 Delta0 = Delta0 := by
    have hadHom : MvPolynomial.IsWeightedHomogeneous w (a0 * d0) 0 := by
      simpa using MvPolynomial.IsWeightedHomogeneous.mul ha0Hom hd0Hom
    have hbcHom : MvPolynomial.IsWeightedHomogeneous w (b0 * c0) 0 := by
      simpa using MvPolynomial.IsWeightedHomogeneous.mul hb0Hom hc0Hom
    dsimp [Delta0]
    rw [map_sub,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hadHom,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hbcHom]

  have hfirstHom :
      MvPolynomial.IsWeightedHomogeneous w
        G.firstDeficitLayer (-(q : ℤ)) := by
    rw [hfirstMono]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [weight_firstDeficitLeftTiltWeight]
    simp [w, dgap, he1, he2, ← hq]
  let Vq := (G.firstDeficitLeftActiveHessian 1 1).coeff
    G.firstDeficitOrder
  have hVqEq :
      Vq = HC4.Polynomial.hessian G.firstDeficitLayer
        (1 : Fin 4) 1 := by
    dsimp [Vq]
    unfold firstDeficitLeftActiveHessian
    simp [firstDeficitLeftActiveIndex]
    rw [parameterFirstHessian_coeff]
    rfl
  have hVqHom :
      MvPolynomial.IsWeightedHomogeneous w Vq WC := by
    rw [hVqEq]
    have hh :=
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfirstHom (1 : Fin 4) 1
    convert hh using 1 <;>
      simp [WC, w, dgap, firstDeficitLeftTiltWeight] <;> ring
  have hVqLE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hVqHom

  have hCqFormula :
      H.schurC.coeff q = Delta0 * Vq := by
    change G.centralDeficitSchurBlock.schurC.coeff q = Delta0 * Vq
    rw [G.centralDeficitSchurC_eq_leftRoofDet, hq]
    have hform :=
      HC4.Polynomial.coeff_det_polynomialMatrix3_gap
        G.firstDeficitOrder_pos
        G.firstDeficitLeftActiveHessian
        (fun r t => G.leftActive_gap r t)
        a0 b0 c0 d0 hbaseL
    simpa [Delta0, Vq] using hform
  have hCqLE : HC4.Polynomial.IsWeightLE w WC (H.schurC.coeff q) := by
    rw [hCqFormula]
    have hp := hDelta0LE.mul hVqLE
    simpa using hp
  have hCqTop :
      HC4.Polynomial.initialForm w WC (H.schurC.coeff q) =
        H.schurC.coeff q := by
    rw [hCqFormula]
    have hp :=
      HC4.Valuation.initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hDelta0LE hVqLE
    rw [hDelta0Top,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hVqHom] at hp
    simpa using hp
  have hCqTopNe :
      HC4.Polynomial.initialForm w WC (H.schurC.coeff q) ≠ 0 := by
    rw [hCqTop]
    exact hCqne

  have hselected :=
    G.firstDeficitLeftTilt_selectedLayer_top
      hthree houtThree hqJ hdepart horder hmissing hm3 hbad hmax
  have hLLE : HC4.Polynomial.IsWeightLE w M L := by
    simpa [w, M, L, dgap] using hselected.1
  have hLTop :
      HC4.Polynomial.initialForm w M L =
        MvPolynomial.monomial depart (MvPolynomial.coeff depart L) := by
    simpa [w, M, L, dgap] using hselected.2
  have hdepartL : depart ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hdepart, horder⟩
  have hdepartCoeff : MvPolynomial.coeff depart L ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdepartL
  have hselectedHessNe :
      HC4.Polynomial.hessian
        (MvPolynomial.monomial depart (MvPolynomial.coeff depart L))
        (2 : Fin 4) 2 ≠ 0 :=
    hessian_monomial_diagonal_ne_zero_of_two_le'
      hdepartCoeff hdepart2

  have hxCoeff :
      H.x.coeff s = HC4.Polynomial.hessian L (2 : Fin 4) 2 := by
    dsimp [H, L]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_x]
    simp only [centralDeficitSchurPerm_two]
    rw [parameterFirstHessian_coeff]
    rfl
  have hxsLE : HC4.Polynomial.IsWeightLE w WX (H.x.coeff s) := by
    rw [hxCoeff]
    have hh := hLLE.hessian_entry (2 : Fin 4) 2
    convert hh using 1 <;>
      simp [WX, w, dgap, firstDeficitLeftTiltWeight] <;> ring
  have hxsTop :
      HC4.Polynomial.initialForm w WX (H.x.coeff s) =
        HC4.Polynomial.hessian
          (MvPolynomial.monomial depart (MvPolynomial.coeff depart L))
          (2 : Fin 4) 2 := by
    rw [hxCoeff]
    have hh :=
      HC4.Polynomial.hessian_initialForm_entry
        w M L (2 : Fin 4) 2
    rw [hLTop] at hh
    convert hh.symm using 1 <;>
      simp [WX, w, dgap, firstDeficitLeftTiltWeight] <;> ring_nf
  have hxsTopNe :
      HC4.Polynomial.initialForm w WX (H.x.coeff s) ≠ 0 := by
    rw [hxsTop]
    exact hselectedHessNe

  have hH :=
    G.firstDeficitLeftTilt_parameterHessian_bound
      hthree houtThree hq hqJ hmin1 hmin2 hearliest
  have haB : HasTiltedParameterCoeffBoundBelow w q s 0 H.a := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_a]
    simpa [w, dgap, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 0
  have hbB : HasTiltedParameterCoeffBoundBelow w q s 0 H.b := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_b]
    simpa [w, dgap, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 3
  have hdB : HasTiltedParameterCoeffBoundBelow w q s 0 H.d := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_d]
    simpa [w, dgap, firstDeficitLeftTiltWeight] using hH (3 : Fin 4) 3
  have hpB : HasTiltedParameterCoeffBoundBelow w q s
      ((dgap : ℤ) - 1) H.p := by
    dsimp [H]
    rw [G.centralDeficitSchurBlock_p]
    simpa [w, dgap, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 2
  have hrB : HasTiltedParameterCoeffBoundBelow w q s
      ((dgap : ℤ) - 1) H.r := by
    dsimp [H]
    rw [G.centralDeficitSchurBlock_r]
    simpa [w, dgap, firstDeficitLeftTiltWeight] using hH (3 : Fin 4) 2
  have hxB : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((dgap : ℤ) - 1)) H.x := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_x]
    convert hH (2 : Fin 4) 2 using 1 <;>
      simp [w, dgap, firstDeficitLeftTiltWeight] <;> ring
  have hactiveB : HasTiltedParameterCoeffBoundBelow w q s 0 H.activeDet := by
    unfold GeneralFourBlock.activeDet
    simpa using (haB.mul hdB).sub (hbB.mul hbB)

  have hactive0ne : H.activeDet.coeff 0 ≠ 0 := by
    dsimp [H]
    exact G.centralDeficitSchurBlock_activeDet_coeff_zero_ne_zero
      hthree houtThree
  have hD0Eq : H.activeDet.coeff 0 = Delta0 := by
    have hlayer0 :
        familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
      calc
        familyParameterLayer P.centralDeficitFamily 0 =
            MvPolynomial.monomial G.central
              (MvPolynomial.coeff G.central P.carrier) :=
          G.centralDeficitFamily_layer_zero_eq hthree houtThree
        _ = G.exposure.face := G.exposure_face_eq.symm
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    unfold GeneralFourBlock.activeDet
    rw [permutedFamilyHessianFourBlock_a,
      permutedFamilyHessianFourBlock_b,
      permutedFamilyHessianFourBlock_d]
    simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
    rw [centralDeficitActiveDet_coeff_zero_eq, hlayer0]
    dsimp [Delta0, a0, b0, c0, d0, H0]
    rfl
  have hD0LE : HC4.Polynomial.IsWeightLE w 0 (H.activeDet.coeff 0) := by
    rw [hD0Eq]
    exact hDelta0LE
  have hD0Top :
      HC4.Polynomial.initialForm w 0 (H.activeDet.coeff 0) =
        H.activeDet.coeff 0 := by
    rw [hD0Eq, hDelta0Top]

  have hx0 : H.x.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_x_coeff_zero hthree houtThree
  have hp0 : H.p.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_p_coeff_zero hthree houtThree
  have hr0 : H.r.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_r_coeff_zero hthree houtThree

  have hactiveUniform :
      ∀ n : ℕ, n < s →
        HC4.Polynomial.IsWeightLE w 0 (H.activeDet.coeff n) := by
    intro n hn
    have h := hactiveB n hn
    by_cases hn0 : n = 0
    · subst n
      simpa [tiltedParameterPenalty] using h
    · apply isWeightLE_mono' (hP := h)
      simp [tiltedParameterPenalty, hn0]
  have hpPos :
      ∀ n : ℕ, 0 < n → n < s →
        HC4.Polynomial.IsWeightLE w
          (-(q : ℤ) - ((dgap : ℤ) - 1)) (H.p.coeff n) := by
    intro n hnpos hn
    have h := hpB n hn
    simp [tiltedParameterPenalty, Nat.ne_of_gt hnpos] at h
    exact h
  have hrPos :
      ∀ n : ℕ, 0 < n → n < s →
        HC4.Polynomial.IsWeightLE w
          (-(q : ℤ) - ((dgap : ℤ) - 1)) (H.r.coeff n) := by
    intro n hnpos hn
    have h := hrB n hn
    simp [tiltedParameterPenalty, Nat.ne_of_gt hnpos] at h
    exact h

  let cross : ℤ := -(q : ℤ) - ((dgap : ℤ) - 1)
  let corrBound : ℤ := cross + cross
  have hpp :
      HC4.Polynomial.IsWeightLE w corrBound ((H.p * H.p).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hp0 hp0 hpPos hpPos
  have hpr :
      HC4.Polynomial.IsWeightLE w corrBound ((H.p * H.r).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hp0 hr0 hpPos hrPos
  have hrr :
      HC4.Polynomial.IsWeightLE w corrBound ((H.r * H.r).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hr0 hr0 hrPos hrPos

  have hpp0 : (H.p * H.p).coeff 0 = 0 := by simp [hp0]
  have hpr0 : (H.p * H.r).coeff 0 = 0 := by simp [hp0, hr0]
  have hrr0 : (H.r * H.r).coeff 0 = 0 := by simp [hr0]
  have hppPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.p * H.p).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hpp
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hp0 hp0
          (fun k hkpos hklt => hpPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hpPos k hkpos (lt_trans hklt hnlt))
  have hprPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.p * H.r).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hpr
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hp0 hr0
          (fun k hkpos hklt => hpPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hrPos k hkpos (lt_trans hklt hnlt))
  have hrrPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.r * H.r).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hrr
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hr0 hr0
          (fun k hkpos hklt => hrPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hrPos k hkpos (lt_trans hklt hnlt))

  have hdpp :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.d * (H.p * H.p)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hpp0
        (fun n hn => by
          have h := hdB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hppPos
  have hbpr :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.b * (H.p * H.r)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hpr0
        (fun n hn => by
          have h := hbB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hprPos
  have harr :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.a * (H.r * H.r)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hrr0
        (fun n hn => by
          have h := haB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hrrPos

  let correction :=
    H.d * H.p * H.p - 2 * H.b * H.p * H.r + H.a * H.r * H.r
  have hcorrRewrite :
      correction =
        H.d * (H.p * H.p) -
        H.b * (H.p * H.r) -
        H.b * (H.p * H.r) +
        H.a * (H.r * H.r) := by
    dsimp [correction]
    ring
  have hcorrLE :
      HC4.Polynomial.IsWeightLE w corrBound (correction.coeff s) := by
    rw [hcorrRewrite]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
    exact ((hdpp.sub hbpr).sub hbpr).add harr
  have hcorrLt : corrBound < WX := by
    dsimp [corrBound, cross, WX, M]
    nlinarith [hMq, hqpos]
  have hcorrTop :
      HC4.Polynomial.initialForm w WX (correction.coeff s) = 0 :=
    HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hcorrLE hcorrLt

  have hmainLE :
      HC4.Polynomial.IsWeightLE w WX ((H.activeDet * H.x).coeff s) := by
    rw [Polynomial.coeff_mul]
    let A : Finset (ℕ × ℕ) := Finset.antidiagonal s
    let f : (ℕ × ℕ) → MvPolynomial (Fin 4) K :=
      fun x => H.activeDet.coeff x.1 * H.x.coeff x.2
    change HC4.Polynomial.IsWeightLE w WX (∑ x ∈ A, f x)
    apply isWeightLE_finset_sum' w WX A f
    intro x hx
    have hsum : x.1 + x.2 = s := by
      exact Finset.mem_antidiagonal.mp (by simpa [A] using hx)
    by_cases hx1 : x.1 = 0
    · have hx2 : x.2 = s := by omega
      simpa [f, hx1, hx2] using hD0LE.mul hxsLE
    by_cases hx2 : x.2 = 0
    · simp [f, hx2, hx0]
    have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hx1
    have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
    have hx1lt : x.1 < s := by omega
    have hx2lt : x.2 < s := by omega
    have hact := hactiveB x.1 hx1lt
    have hxx := hxB x.2 hx2lt
    have hprod := hact.mul hxx
    apply isWeightLE_mono' (hP := hprod)
    simp [tiltedParameterPenalty, hx1, hx2] at hprod ⊢
    dsimp [WX, M, dgap] at hMq ⊢
    nlinarith [hMq, hqpos]

  have hmainTop :
      HC4.Polynomial.initialForm w WX ((H.activeDet * H.x).coeff s) =
        HC4.Polynomial.initialForm w WX
          (H.activeDet.coeff 0 * H.x.coeff s) := by
    apply initialForm_coeff_mul_eq_single
      (w := w) (P := H.activeDet) (Q := H.x)
      (N := s) (i₀ := 0) (j₀ := s) (M := WX)
    · simp
    · intro x hx hne
      have hsum : x.1 + x.2 = s := Finset.mem_antidiagonal.mp hx
      by_cases hx1 : x.1 = 0
      · have hx2 : x.2 = s := by omega
        exact (hne (Prod.ext hx1 hx2)).elim
      by_cases hx2 : x.2 = 0
      · simp [hx2, hx0]
      have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hx1
      have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
      have hx1lt : x.1 < s := by omega
      have hx2lt : x.2 < s := by omega
      have hact := hactiveB x.1 hx1lt
      have hxx := hxB x.2 hx2lt
      have hprod := hact.mul hxx
      apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
      simp [tiltedParameterPenalty, hx1, hx2]
      dsimp [WX, M, dgap] at hMq ⊢
      nlinarith [hMq, hqpos]

  have hmainTopExact :
      HC4.Polynomial.initialForm w WX ((H.activeDet * H.x).coeff s) =
        H.activeDet.coeff 0 *
          HC4.Polynomial.initialForm w WX (H.x.coeff s) := by
    rw [hmainTop]
    have hp :=
      HC4.Valuation.initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hD0LE hxsLE
    rw [hD0Top] at hp
    simpa using hp

  have hAsLE : HC4.Polynomial.IsWeightLE w WX (H.schurA.coeff s) := by
    unfold GeneralFourBlock.schurA
    rw [Polynomial.coeff_sub]
    apply hmainLE.sub
    apply isWeightLE_mono' (le_of_lt hcorrLt) hcorrLE
  have hAsTop :
      HC4.Polynomial.initialForm w WX (H.schurA.coeff s) =
        H.activeDet.coeff 0 *
          HC4.Polynomial.initialForm w WX (H.x.coeff s) := by
    unfold GeneralFourBlock.schurA
    rw [Polynomial.coeff_sub, map_sub, hmainTopExact, hcorrTop, sub_zero]
  have hAsTopNe :
      HC4.Polynomial.initialForm w WX (H.schurA.coeff s) ≠ 0 := by
    rw [hAsTop]
    exact mul_ne_zero hactive0ne hxsTopNe

  have hSchur :=
    G.firstDeficitLeftTilt_schur_bounds
      hthree houtThree hq hqJ hmin1 hmin2 hearliest
  change
    HasTiltedParameterCoeffBoundBelow w q s
        (2 * ((dgap : ℤ) - 1)) H.schurA ∧
      HasTiltedParameterCoeffBoundBelow w q s
        ((dgap : ℤ) - 2) H.schurB ∧
      HasTiltedParameterCoeffBoundBelow w q s
        (-2) H.schurC at hSchur
  rcases hSchur with ⟨hAbound, hBbound, hCbound⟩

  have hAltq : ∀ n : ℕ, n < q → H.schurA.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact hA0
    · change G.centralDeficitSchurBlock.schurA.coeff n = 0
      rw [G.centralDeficitSchurA_eq_rightRoofDet]
      exact G.firstDeficitRightActiveHessian_det_gap
        n (Nat.pos_of_ne_zero hn0) (by simpa [hq] using hn)
  have hCltq : ∀ n : ℕ, n < q → H.schurC.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact hC0
    · change G.centralDeficitSchurBlock.schurC.coeff n = 0
      rw [G.centralDeficitSchurC_eq_leftRoofDet]
      exact G.firstDeficitLeftActiveHessian_det_gap
        n (Nat.pos_of_ne_zero hn0) (by simpa [hq] using hn)
  have hBleq : ∀ n : ℕ, n ≤ q → H.schurB.coeff n = 0 := by
    rcases G.centralDeficitSchurB_firstOppositeOpening
        hthree houtThree with ⟨JB, hqJB, hBgap, hBopen⟩
    intro n hn
    apply hBgap n
    have hqJB' : q < JB := by simpa [hq] using hqJB
    omega

  let N := q + s
  let target := WX + WC
  have hinterior :
      (-(q : ℤ) - 2 * ((dgap : ℤ) - 1)) +
          (-(q : ℤ) + 2) < target := by
    dsimp [target, WX, WC, M, dgap] at hMq ⊢
    nlinarith
  have hBBinterior :
      (-(q : ℤ) - ((dgap : ℤ) - 2)) +
        (-(q : ℤ) - ((dgap : ℤ) - 2)) < target := by
    dsimp [target, WX, WC, M, dgap] at hMq ⊢
    nlinarith

  have hACother :
      ∀ x ∈ Finset.antidiagonal N, x ≠ (s, q) →
        HC4.Polynomial.initialForm w target
          (H.schurA.coeff x.1 * H.schurC.coeff x.2) = 0 := by
    intro x hx hne
    have hsum : x.1 + x.2 = N := Finset.mem_antidiagonal.mp hx
    by_cases hi0 : x.1 = 0
    · simp [hi0, hA0]
    by_cases hj0 : x.2 = 0
    · simp [hj0, hC0]
    by_cases his : x.1 = s
    · have hjq : x.2 = q := by dsimp [N] at hsum; omega
      exact (hne (Prod.ext his hjq)).elim
    by_cases hige : s < x.1
    · have hjlt : x.2 < q := by dsimp [N] at hsum; omega
      rw [hCltq x.2 hjlt]
      simp
    have hilt : x.1 < s := by omega
    by_cases hjge : s < x.2
    · have hiltq : x.1 < q := by dsimp [N] at hsum; omega
      rw [hAltq x.1 hiltq]
      simp
    by_cases hjs : x.2 = s
    · have hiq : x.1 = q := by dsimp [N] at hsum; omega
      rw [hiq, hAq0]
      simp
    have hjlt : x.2 < s := by omega
    have hiPos : 0 < x.1 := Nat.pos_of_ne_zero hi0
    have hjPos : 0 < x.2 := Nat.pos_of_ne_zero hj0
    have hAi := hAbound x.1 hilt
    have hCj := hCbound x.2 hjlt
    have hprod := hAi.mul hCj
    apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
    simp [tiltedParameterPenalty, Nat.ne_of_gt hiPos,
      Nat.ne_of_gt hjPos] at hprod ⊢
    exact hinterior

  have hBB :
      ∀ x ∈ Finset.antidiagonal N,
        HC4.Polynomial.initialForm w target
          (H.schurB.coeff x.1 * H.schurB.coeff x.2) = 0 := by
    intro x hx
    have hsum : x.1 + x.2 = N := Finset.mem_antidiagonal.mp hx
    by_cases hi0 : x.1 = 0
    · simp [hi0, hB0]
    by_cases hj0 : x.2 = 0
    · simp [hj0, hB0]
    by_cases hige : s ≤ x.1
    · have hjle : x.2 ≤ q := by dsimp [N] at hsum; omega
      rw [hBleq x.2 hjle]
      simp
    by_cases hjge : s ≤ x.2
    · have hile : x.1 ≤ q := by dsimp [N] at hsum; omega
      rw [hBleq x.1 hile]
      simp
    have hilt : x.1 < s := Nat.lt_of_not_ge hige
    have hjlt : x.2 < s := Nat.lt_of_not_ge hjge
    have hiPos : 0 < x.1 := Nat.pos_of_ne_zero hi0
    have hjPos : 0 < x.2 := Nat.pos_of_ne_zero hj0
    have hBi := hBbound x.1 hilt
    have hBj := hBbound x.2 hjlt
    have hprod := hBi.mul hBj
    apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
    simp [tiltedParameterPenalty, Nat.ne_of_gt hiPos,
      Nat.ne_of_gt hjPos] at hprod ⊢
    exact hBBinterior

  have hdet :
      H.schurA * H.schurC - H.schurB * H.schurB = 0 := by
    simpa [H, GeneralFourBlock.schurDetCore] using
      G.centralDeficitSchurBlock_schurDetCore_eq_zero

  exact tilted_binary_nonCancellation
    (w := w) (A := H.schurA) (B := H.schurB) (C := H.schurC)
    (N := N) (i₀ := s) (j₀ := q) (a := WX) (c := WC)
    (by dsimp [N]; omega) hAsLE hCqLE hAsTopNe hCqTopNe
    (by simpa [target] using hACother)
    (by simpa [target] using hBB)
    hdet

set_option maxHeartbeats 800000 in
private theorem centralDeficit_rightTilt_impossible
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s m : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    {depart : Fin 4 →₀ ℕ}
    (hdepart : depart ∈ P.carrier.support)
    (horder : depart 1 + depart 2 = s)
    (hmissing : depart 1 = m)
    (hm3 : 3 ≤ m)
    (hbad : s < q + m * (J - q))
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 1 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 1 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 1 →
        f 1 + f 2 < q + f 1 * (J - q) →
        s ≤ f 1 + f 2)
    (hmax :
      ∀ f ∈ P.carrier.support,
        f 1 + f 2 = s →
        3 ≤ f 1 →
        f 1 + f 2 < q + f 1 * (J - q) →
        f 1 ≤ m) :
    False := by
  let dgap := J - q
  let w := firstDeficitRightTiltWeight dgap
  let M : ℤ := (dgap : ℤ) * (m : ℤ) - (s : ℤ)
  let WZ : ℤ := M - 2 * ((dgap : ℤ) - 1)
  let WA : ℤ := -(q : ℤ) + 2
  let H := G.centralDeficitSchurBlock
  let L := familyParameterLayer P.centralDeficitFamily s

  have hqpos : 0 < q := by
    rw [hq]
    exact G.firstDeficitOrder_pos
  have hdpos : 0 < dgap := by
    dsimp [dgap]
    omega
  have hdepart1 : 2 ≤ depart 1 := by
    rw [hmissing]
    omega
  have hqs : q < s := by
    have h2 := hmin2 depart hdepart hdepart1
    have hdOne : 1 ≤ dgap := by omega
    dsimp [dgap] at h2 hdOne
    omega
  have hspos : 0 < s := lt_trans hqpos hqs
  have hMq : -(q : ℤ) < M := by
    have hbZ :
        (s : ℤ) < (q : ℤ) + (m : ℤ) * (dgap : ℤ) := by
      dsimp [dgap]
      exact_mod_cast hbad
    dsimp [M]
    nlinarith

  have hfirst :
      ∃ e : Fin 4 →₀ ℕ,
        e ∈ G.firstDeficitLayer.support ∧
        e 1 = 0 ∧
        e 2 = G.firstDeficitOrder ∧
        ∀ f ∈ G.firstDeficitLayer.support, f = e := by
    rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
      hleft | hright
    · rcases hleft with ⟨e, he, he1, he2, huniq⟩
      have heData := G.firstDeficitLayer_support he
      have hJle := hmin1 e heData.1 (by rw [he1, ← hq]; exact hqpos)
      exfalso
      rw [he1, he2, ← hq] at hJle
      omega
    · exact hright
  rcases hfirst with ⟨e, he, he1, he2, huniq⟩

  let z := MvPolynomial.coeff e G.firstDeficitLayer
  have hz : z ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hfirstMono :
      G.firstDeficitLayer = MvPolynomial.monomial e z :=
    eq_monomial_of_support_singleton' G.firstDeficitLayer he huniq

  have hA0 : H.schurA.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.active_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h
  have hB0 : H.schurB.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.offDiag_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h
  have hC0 : H.schurC.coeff 0 = 0 := by
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    have h := Z.kernel_coeff_zero
    simpa [Z, H, centralDeficitZeroSchurSeries,
      GeneralFourBlock.polynomialSchurSeries] using h

  let H0 := HC4.Polynomial.hessian G.exposure.face
  let a0 := H0 (0 : Fin 4) 0
  let b0 := H0 (0 : Fin 4) 3
  let c0 := H0 (3 : Fin 4) 0
  let d0 := H0 (3 : Fin 4) 3
  let Delta0 := a0 * d0 - b0 * c0

  have hbaseL : ∀ r t : Fin 3,
      (G.firstDeficitLeftActiveHessian r t).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          a0 b0 c0 d0 r t := by
    intro r t
    simpa [a0, b0, c0, d0, H0] using
      G.firstDeficitLeftActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r t
  have hbaseR : ∀ r t : Fin 3,
      (G.firstDeficitRightActiveHessian r t).coeff 0 =
        HC4.Polynomial.rankTwoRoofZeroKernelBase
          a0 b0 c0 d0 r t := by
    intro r t
    simpa [a0, b0, c0, d0, H0] using
      G.firstDeficitRightActiveHessian_coeff_zero_eq_rankTwoRoofBase
        hthree houtThree r t
  have hdiagLeftSource :
      HC4.Polynomial.hessian G.firstDeficitLayer
        (1 : Fin 4) 1 = 0 := by
    rw [hfirstMono]
    rw [HC4.Polynomial.hessian_apply]
    simp [MvPolynomial.pderiv_monomial, he1]
  have hdiagLeft :
      (G.firstDeficitLeftActiveHessian 1 1).coeff
          G.firstDeficitOrder = 0 := by
    unfold firstDeficitLeftActiveHessian
    simp [firstDeficitLeftActiveIndex]
    rw [parameterFirstHessian_coeff]
    simpa [firstDeficitLayer] using hdiagLeftSource
  have hCq0 : H.schurC.coeff q = 0 := by
    change G.centralDeficitSchurBlock.schurC.coeff q = 0
    rw [G.centralDeficitSchurC_eq_leftRoofDet, hq]
    rw [HC4.Polynomial.coeff_det_polynomialMatrix3_gap
      G.firstDeficitOrder_pos
      G.firstDeficitLeftActiveHessian
      (fun r t => G.leftActive_gap r t)
      a0 b0 c0 d0 hbaseL]
    rw [hdiagLeft]
    simp

  have hAqne : H.schurA.coeff q ≠ 0 := by
    change G.centralDeficitSchurBlock.schurA.coeff q ≠ 0
    rw [G.centralDeficitSchurA_eq_rightRoofDet]
    simpa [hq] using
      G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
        hthree houtThree he he1 he2 huniq

  have hfaceHom :
      MvPolynomial.IsWeightedHomogeneous w G.exposure.face 0 := by
    rw [G.exposure_face_eq]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [weight_firstDeficitRightTiltWeight]
    simp [w, dgap, G.central_one_zero, G.central_two_zero]
  have ha0Hom :
      MvPolynomial.IsWeightedHomogeneous w a0 0 := by
    dsimp [a0, H0]
    simpa [w, firstDeficitRightTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (0 : Fin 4) 0
  have hb0Hom :
      MvPolynomial.IsWeightedHomogeneous w b0 0 := by
    dsimp [b0, H0]
    simpa [w, firstDeficitRightTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (0 : Fin 4) 3
  have hc0Hom :
      MvPolynomial.IsWeightedHomogeneous w c0 0 := by
    dsimp [c0, H0]
    simpa [w, firstDeficitRightTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (3 : Fin 4) 0
  have hd0Hom :
      MvPolynomial.IsWeightedHomogeneous w d0 0 := by
    dsimp [d0, H0]
    simpa [w, firstDeficitRightTiltWeight] using
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfaceHom (3 : Fin 4) 3
  have ha0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous ha0Hom
  have hb0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hb0Hom
  have hc0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hc0Hom
  have hd0LE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hd0Hom
  have hDelta0LE : HC4.Polynomial.IsWeightLE w 0 Delta0 := by
    dsimp [Delta0]
    simpa using (ha0LE.mul hd0LE).sub (hb0LE.mul hc0LE)
  have hDelta0Top :
      HC4.Polynomial.initialForm w 0 Delta0 = Delta0 := by
    have hadHom : MvPolynomial.IsWeightedHomogeneous w (a0 * d0) 0 := by
      simpa using MvPolynomial.IsWeightedHomogeneous.mul ha0Hom hd0Hom
    have hbcHom : MvPolynomial.IsWeightedHomogeneous w (b0 * c0) 0 := by
      simpa using MvPolynomial.IsWeightedHomogeneous.mul hb0Hom hc0Hom
    dsimp [Delta0]
    rw [map_sub,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hadHom,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hbcHom]
  have hfirstHom :
      MvPolynomial.IsWeightedHomogeneous w
        G.firstDeficitLayer (-(q : ℤ)) := by
    rw [hfirstMono]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [weight_firstDeficitRightTiltWeight]
    simp [w, dgap, he1, he2, ← hq]
  let Vq := (G.firstDeficitRightActiveHessian 1 1).coeff
    G.firstDeficitOrder
  have hVqEq :
      Vq = HC4.Polynomial.hessian G.firstDeficitLayer
        (2 : Fin 4) 2 := by
    dsimp [Vq]
    unfold firstDeficitRightActiveHessian
    simp [firstDeficitRightActiveIndex]
    rw [parameterFirstHessian_coeff]
    rfl
  have hVqHom :
      MvPolynomial.IsWeightedHomogeneous w Vq WA := by
    rw [hVqEq]
    have hh :=
      HC4.Polynomial.hessian_entry_isWeightedHomogeneous
        hfirstHom (2 : Fin 4) 2
    convert hh using 1 <;>
      simp [WA, w, dgap, firstDeficitRightTiltWeight] <;> ring
  have hVqLE := HC4.Polynomial.isWeightLE_of_isWeightedHomogeneous hVqHom
  have hAqFormula :
      H.schurA.coeff q = Delta0 * Vq := by
    change G.centralDeficitSchurBlock.schurA.coeff q = Delta0 * Vq
    rw [G.centralDeficitSchurA_eq_rightRoofDet, hq]
    have hform :=
      HC4.Polynomial.coeff_det_polynomialMatrix3_gap
        G.firstDeficitOrder_pos
        G.firstDeficitRightActiveHessian
        (fun r t => G.rightActive_gap r t)
        a0 b0 c0 d0 hbaseR
    simpa [Delta0, Vq] using hform
  have hAqLE : HC4.Polynomial.IsWeightLE w WA (H.schurA.coeff q) := by
    rw [hAqFormula]
    have hp := hDelta0LE.mul hVqLE
    simpa using hp
  have hAqTop :
      HC4.Polynomial.initialForm w WA (H.schurA.coeff q) =
        H.schurA.coeff q := by
    rw [hAqFormula]
    have hp :=
      HC4.Valuation.initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hDelta0LE hVqLE
    rw [hDelta0Top,
      HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hVqHom] at hp
    simpa using hp
  have hAqTopNe :
      HC4.Polynomial.initialForm w WA (H.schurA.coeff q) ≠ 0 := by
    rw [hAqTop]
    exact hAqne

  have hselected :=
    G.firstDeficitRightTilt_selectedLayer_top
      hthree houtThree hqJ hdepart horder hmissing hm3 hbad hmax
  have hLLE : HC4.Polynomial.IsWeightLE w M L := by
    simpa [w, M, L, dgap] using hselected.1
  have hLTop :
      HC4.Polynomial.initialForm w M L =
        MvPolynomial.monomial depart (MvPolynomial.coeff depart L) := by
    simpa [w, M, L, dgap] using hselected.2
  have hdepartL : depart ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hdepart, horder⟩
  have hdepartCoeff : MvPolynomial.coeff depart L ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdepartL
  have hselectedHessNe :
      HC4.Polynomial.hessian
        (MvPolynomial.monomial depart (MvPolynomial.coeff depart L))
        (1 : Fin 4) 1 ≠ 0 :=
    hessian_monomial_diagonal_ne_zero_of_two_le'
      hdepartCoeff hdepart1

  have hzCoeff :
      H.z.coeff s = HC4.Polynomial.hessian L (1 : Fin 4) 1 := by
    dsimp [H, L]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_z]
    simp only [centralDeficitSchurPerm_three]
    rw [parameterFirstHessian_coeff]
    rfl
  have hzsLE : HC4.Polynomial.IsWeightLE w WZ (H.z.coeff s) := by
    rw [hzCoeff]
    have hh := hLLE.hessian_entry (1 : Fin 4) 1
    convert hh using 1 <;>
      simp [WZ, w, dgap, firstDeficitRightTiltWeight] <;> ring
  have hzsTop :
      HC4.Polynomial.initialForm w WZ (H.z.coeff s) =
        HC4.Polynomial.hessian
          (MvPolynomial.monomial depart (MvPolynomial.coeff depart L))
          (1 : Fin 4) 1 := by
    rw [hzCoeff]
    have hh :=
      HC4.Polynomial.hessian_initialForm_entry
        w M L (1 : Fin 4) 1
    rw [hLTop] at hh
    convert hh.symm using 1 <;>
      simp [WZ, w, dgap, firstDeficitRightTiltWeight] <;> ring_nf
  have hzsTopNe :
      HC4.Polynomial.initialForm w WZ (H.z.coeff s) ≠ 0 := by
    rw [hzsTop]
    exact hselectedHessNe

  have hH :=
    G.firstDeficitRightTilt_parameterHessian_bound
      hthree houtThree hq hqJ hmin1 hmin2 hearliest
  have haB : HasTiltedParameterCoeffBoundBelow w q s 0 H.a := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_a]
    simpa [w, dgap, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 0
  have hbB : HasTiltedParameterCoeffBoundBelow w q s 0 H.b := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_b]
    simpa [w, dgap, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 3
  have hdB : HasTiltedParameterCoeffBoundBelow w q s 0 H.d := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_d]
    simpa [w, dgap, firstDeficitRightTiltWeight] using hH (3 : Fin 4) 3
  have hqB : HasTiltedParameterCoeffBoundBelow w q s
      ((dgap : ℤ) - 1) H.q := by
    dsimp [H]
    rw [G.centralDeficitSchurBlock_q]
    simpa [w, dgap, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 1
  have hsB : HasTiltedParameterCoeffBoundBelow w q s
      ((dgap : ℤ) - 1) H.s := by
    dsimp [H]
    rw [G.centralDeficitSchurBlock_s]
    simpa [w, dgap, firstDeficitRightTiltWeight] using hH (3 : Fin 4) 1
  have hzB : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((dgap : ℤ) - 1)) H.z := by
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_z]
    convert hH (1 : Fin 4) 1 using 1 <;>
      simp [w, dgap, firstDeficitRightTiltWeight] <;> ring
  have hactiveB : HasTiltedParameterCoeffBoundBelow w q s 0 H.activeDet := by
    unfold GeneralFourBlock.activeDet
    simpa using (haB.mul hdB).sub (hbB.mul hbB)

  have hactive0ne : H.activeDet.coeff 0 ≠ 0 := by
    dsimp [H]
    exact G.centralDeficitSchurBlock_activeDet_coeff_zero_ne_zero
      hthree houtThree
  have hD0Eq : H.activeDet.coeff 0 = Delta0 := by
    have hlayer0 :
        familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
      calc
        familyParameterLayer P.centralDeficitFamily 0 =
            MvPolynomial.monomial G.central
              (MvPolynomial.coeff G.central P.carrier) :=
          G.centralDeficitFamily_layer_zero_eq hthree houtThree
        _ = G.exposure.face := G.exposure_face_eq.symm
    dsimp [H]
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    unfold GeneralFourBlock.activeDet
    rw [permutedFamilyHessianFourBlock_a,
      permutedFamilyHessianFourBlock_b,
      permutedFamilyHessianFourBlock_d]
    simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
    rw [centralDeficitActiveDet_coeff_zero_eq, hlayer0]
    dsimp [Delta0, a0, b0, c0, d0, H0]
    rfl
  have hD0LE : HC4.Polynomial.IsWeightLE w 0 (H.activeDet.coeff 0) := by
    rw [hD0Eq]
    exact hDelta0LE
  have hD0Top :
      HC4.Polynomial.initialForm w 0 (H.activeDet.coeff 0) =
        H.activeDet.coeff 0 := by
    rw [hD0Eq, hDelta0Top]

  have hz0 : H.z.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_z_coeff_zero hthree houtThree
  have hq0 : H.q.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_q_coeff_zero hthree houtThree
  have hs0 : H.s.coeff 0 = 0 := by
    dsimp [H]
    exact G.centralDeficit_s_coeff_zero hthree houtThree

  have hqPos :
      ∀ n : ℕ, 0 < n → n < s →
        HC4.Polynomial.IsWeightLE w
          (-(q : ℤ) - ((dgap : ℤ) - 1)) (H.q.coeff n) := by
    intro n hnpos hn
    have h := hqB n hn
    simp [tiltedParameterPenalty, Nat.ne_of_gt hnpos] at h
    exact h
  have hsPos :
      ∀ n : ℕ, 0 < n → n < s →
        HC4.Polynomial.IsWeightLE w
          (-(q : ℤ) - ((dgap : ℤ) - 1)) (H.s.coeff n) := by
    intro n hnpos hn
    have h := hsB n hn
    simp [tiltedParameterPenalty, Nat.ne_of_gt hnpos] at h
    exact h

  let cross : ℤ := -(q : ℤ) - ((dgap : ℤ) - 1)
  let corrBound : ℤ := cross + cross
  have hqq :
      HC4.Polynomial.IsWeightLE w corrBound ((H.q * H.q).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hq0 hq0 hqPos hqPos
  have hqsProd :
      HC4.Polynomial.IsWeightLE w corrBound ((H.q * H.s).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hq0 hs0 hqPos hsPos
  have hss :
      HC4.Polynomial.IsWeightLE w corrBound ((H.s * H.s).coeff s) := by
    simpa [corrBound, cross] using
      coeff_mul_isWeightLE_of_two_zero_constants
        (w := w) (s := s) hspos hs0 hs0 hsPos hsPos
  have hqq0 : (H.q * H.q).coeff 0 = 0 := by simp [hq0]
  have hqs0 : (H.q * H.s).coeff 0 = 0 := by simp [hq0, hs0]
  have hss0 : (H.s * H.s).coeff 0 = 0 := by simp [hs0]
  have hqqPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.q * H.q).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hqq
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hq0 hq0
          (fun k hkpos hklt => hqPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hqPos k hkpos (lt_trans hklt hnlt))
  have hqsPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.q * H.s).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hqsProd
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hq0 hs0
          (fun k hkpos hklt => hqPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hsPos k hkpos (lt_trans hklt hnlt))
  have hssPos :
      ∀ n : ℕ, 0 < n → n ≤ s →
        HC4.Polynomial.IsWeightLE w corrBound ((H.s * H.s).coeff n) := by
    intro n hnpos hnle
    by_cases hns : n = s
    · subst n
      exact hss
    · have hnlt : n < s := by omega
      simpa [corrBound, cross] using
        coeff_mul_isWeightLE_of_two_zero_constants
          (w := w) (s := n) hnpos hs0 hs0
          (fun k hkpos hklt => hsPos k hkpos (lt_trans hklt hnlt))
          (fun k hkpos hklt => hsPos k hkpos (lt_trans hklt hnlt))

  have hdqq :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.d * (H.q * H.q)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hqq0
        (fun n hn => by
          have h := hdB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hqqPos
  have hbqs :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.b * (H.q * H.s)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hqs0
        (fun n hn => by
          have h := hbB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hqsPos
  have hass :
      HC4.Polynomial.IsWeightLE w corrBound
        ((H.a * (H.s * H.s)).coeff s) := by
    rw [← zero_add corrBound]
    exact
      coeff_mul_isWeightLE_of_right_positive
        (w := w) (s := s) hspos hss0
        (fun n hn => by
          have h := haB n hn
          apply isWeightLE_mono' (b := 0) (hP := h)
          by_cases hn0 : n = 0
          · subst n
            simp [tiltedParameterPenalty]
          · simp [tiltedParameterPenalty, hn0])
        hssPos

  let correction :=
    H.d * H.q * H.q - 2 * H.b * H.q * H.s + H.a * H.s * H.s
  have hcorrRewrite :
      correction =
        H.d * (H.q * H.q) -
        H.b * (H.q * H.s) -
        H.b * (H.q * H.s) +
        H.a * (H.s * H.s) := by
    dsimp [correction]
    ring
  have hcorrLE :
      HC4.Polynomial.IsWeightLE w corrBound (correction.coeff s) := by
    rw [hcorrRewrite]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
    exact ((hdqq.sub hbqs).sub hbqs).add hass
  have hcorrLt : corrBound < WZ := by
    dsimp [corrBound, cross, WZ, M]
    nlinarith [hMq, hqpos]
  have hcorrTop :
      HC4.Polynomial.initialForm w WZ (correction.coeff s) = 0 :=
    HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hcorrLE hcorrLt

  have hmainLE :
      HC4.Polynomial.IsWeightLE w WZ ((H.activeDet * H.z).coeff s) := by
    rw [Polynomial.coeff_mul]
    let A : Finset (ℕ × ℕ) := Finset.antidiagonal s
    let f : (ℕ × ℕ) → MvPolynomial (Fin 4) K :=
      fun x => H.activeDet.coeff x.1 * H.z.coeff x.2
    change HC4.Polynomial.IsWeightLE w WZ (∑ x ∈ A, f x)
    apply isWeightLE_finset_sum' w WZ A f
    intro x hx
    have hsum : x.1 + x.2 = s := by
      exact Finset.mem_antidiagonal.mp (by simpa [A] using hx)
    by_cases hx1 : x.1 = 0
    · have hx2 : x.2 = s := by omega
      simpa [f, hx1, hx2] using hD0LE.mul hzsLE
    by_cases hx2 : x.2 = 0
    · simp [f, hx2, hz0]
    have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hx1
    have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
    have hx1lt : x.1 < s := by omega
    have hx2lt : x.2 < s := by omega
    have hact := hactiveB x.1 hx1lt
    have hzz := hzB x.2 hx2lt
    have hprod := hact.mul hzz
    apply isWeightLE_mono' (hP := hprod)
    simp [tiltedParameterPenalty, hx1, hx2] at hprod ⊢
    dsimp [WZ, M, dgap] at hMq ⊢
    nlinarith [hMq, hqpos]

  have hmainTop :
      HC4.Polynomial.initialForm w WZ ((H.activeDet * H.z).coeff s) =
        HC4.Polynomial.initialForm w WZ
          (H.activeDet.coeff 0 * H.z.coeff s) := by
    apply initialForm_coeff_mul_eq_single
      (w := w) (P := H.activeDet) (Q := H.z)
      (N := s) (i₀ := 0) (j₀ := s) (M := WZ)
    · simp
    · intro x hx hne
      have hsum : x.1 + x.2 = s := Finset.mem_antidiagonal.mp hx
      by_cases hx1 : x.1 = 0
      · have hx2 : x.2 = s := by omega
        exact (hne (Prod.ext hx1 hx2)).elim
      by_cases hx2 : x.2 = 0
      · simp [hx2, hz0]
      have hx1pos : 0 < x.1 := Nat.pos_of_ne_zero hx1
      have hx2pos : 0 < x.2 := Nat.pos_of_ne_zero hx2
      have hx1lt : x.1 < s := by omega
      have hx2lt : x.2 < s := by omega
      have hact := hactiveB x.1 hx1lt
      have hzz := hzB x.2 hx2lt
      have hprod := hact.mul hzz
      apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
      simp [tiltedParameterPenalty, hx1, hx2]
      dsimp [WZ, M, dgap] at hMq ⊢
      nlinarith [hMq, hqpos]

  have hmainTopExact :
      HC4.Polynomial.initialForm w WZ ((H.activeDet * H.z).coeff s) =
        H.activeDet.coeff 0 *
          HC4.Polynomial.initialForm w WZ (H.z.coeff s) := by
    rw [hmainTop]
    have hp :=
      HC4.Valuation.initialForm_mul_eq_mul_initialForm_of_isWeightLE
        (K := K) hD0LE hzsLE
    rw [hD0Top] at hp
    simpa using hp

  have hCsLE : HC4.Polynomial.IsWeightLE w WZ (H.schurC.coeff s) := by
    unfold GeneralFourBlock.schurC
    rw [Polynomial.coeff_sub]
    apply hmainLE.sub
    apply isWeightLE_mono' (le_of_lt hcorrLt) hcorrLE
  have hCsTop :
      HC4.Polynomial.initialForm w WZ (H.schurC.coeff s) =
        H.activeDet.coeff 0 *
          HC4.Polynomial.initialForm w WZ (H.z.coeff s) := by
    unfold GeneralFourBlock.schurC
    rw [Polynomial.coeff_sub, map_sub, hmainTopExact, hcorrTop, sub_zero]
  have hCsTopNe :
      HC4.Polynomial.initialForm w WZ (H.schurC.coeff s) ≠ 0 := by
    rw [hCsTop]
    exact mul_ne_zero hactive0ne hzsTopNe

  have hSchur :=
    G.firstDeficitRightTilt_schur_bounds
      hthree houtThree hq hqJ hmin1 hmin2 hearliest
  change
    HasTiltedParameterCoeffBoundBelow w q s
        (-2) H.schurA ∧
      HasTiltedParameterCoeffBoundBelow w q s
        ((dgap : ℤ) - 2) H.schurB ∧
      HasTiltedParameterCoeffBoundBelow w q s
        (2 * ((dgap : ℤ) - 1)) H.schurC at hSchur
  rcases hSchur with ⟨hAbound, hBbound, hCbound⟩

  have hAltq : ∀ n : ℕ, n < q → H.schurA.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact hA0
    · change G.centralDeficitSchurBlock.schurA.coeff n = 0
      rw [G.centralDeficitSchurA_eq_rightRoofDet]
      exact G.firstDeficitRightActiveHessian_det_gap
        n (Nat.pos_of_ne_zero hn0) (by simpa [hq] using hn)
  have hCltq : ∀ n : ℕ, n < q → H.schurC.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact hC0
    · change G.centralDeficitSchurBlock.schurC.coeff n = 0
      rw [G.centralDeficitSchurC_eq_leftRoofDet]
      exact G.firstDeficitLeftActiveHessian_det_gap
        n (Nat.pos_of_ne_zero hn0) (by simpa [hq] using hn)
  have hBleq : ∀ n : ℕ, n ≤ q → H.schurB.coeff n = 0 := by
    rcases G.centralDeficitSchurB_firstOppositeOpening
        hthree houtThree with ⟨JB, hqJB, hBgap, hBopen⟩
    intro n hn
    apply hBgap n
    have hqJB' : q < JB := by simpa [hq] using hqJB
    omega

  let N := q + s
  let target := WA + WZ
  have hinterior :
      (-(q : ℤ) + 2) +
          (-(q : ℤ) - 2 * ((dgap : ℤ) - 1)) < target := by
    dsimp [target, WA, WZ, M, dgap] at hMq ⊢
    nlinarith
  have hBBinterior :
      (-(q : ℤ) - ((dgap : ℤ) - 2)) +
        (-(q : ℤ) - ((dgap : ℤ) - 2)) < target := by
    dsimp [target, WA, WZ, M, dgap] at hMq ⊢
    nlinarith

  have hACother :
      ∀ x ∈ Finset.antidiagonal N, x ≠ (q, s) →
        HC4.Polynomial.initialForm w target
          (H.schurA.coeff x.1 * H.schurC.coeff x.2) = 0 := by
    intro x hx hne
    have hsum : x.1 + x.2 = N := Finset.mem_antidiagonal.mp hx
    by_cases hi0 : x.1 = 0
    · simp [hi0, hA0]
    by_cases hj0 : x.2 = 0
    · simp [hj0, hC0]
    by_cases hjs : x.2 = s
    · have hiq : x.1 = q := by dsimp [N] at hsum; omega
      exact (hne (Prod.ext hiq hjs)).elim
    by_cases hjge : s < x.2
    · have hilt : x.1 < q := by dsimp [N] at hsum; omega
      rw [hAltq x.1 hilt]
      simp
    have hjlt : x.2 < s := by omega
    by_cases hige : s < x.1
    · have hjltq : x.2 < q := by dsimp [N] at hsum; omega
      rw [hCltq x.2 hjltq]
      simp
    by_cases his : x.1 = s
    · have hjq : x.2 = q := by dsimp [N] at hsum; omega
      rw [hjq, hCq0]
      simp
    have hilt : x.1 < s := by omega
    have hiPos : 0 < x.1 := Nat.pos_of_ne_zero hi0
    have hjPos : 0 < x.2 := Nat.pos_of_ne_zero hj0
    have hAi := hAbound x.1 hilt
    have hCj := hCbound x.2 hjlt
    have hprod := hAi.mul hCj
    apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
    simp [tiltedParameterPenalty, Nat.ne_of_gt hiPos,
      Nat.ne_of_gt hjPos] at hprod ⊢
    exact hinterior

  have hBB :
      ∀ x ∈ Finset.antidiagonal N,
        HC4.Polynomial.initialForm w target
          (H.schurB.coeff x.1 * H.schurB.coeff x.2) = 0 := by
    intro x hx
    have hsum : x.1 + x.2 = N := Finset.mem_antidiagonal.mp hx
    by_cases hi0 : x.1 = 0
    · simp [hi0, hB0]
    by_cases hj0 : x.2 = 0
    · simp [hj0, hB0]
    by_cases hige : s ≤ x.1
    · have hjle : x.2 ≤ q := by dsimp [N] at hsum; omega
      rw [hBleq x.2 hjle]
      simp
    by_cases hjge : s ≤ x.2
    · have hile : x.1 ≤ q := by dsimp [N] at hsum; omega
      rw [hBleq x.1 hile]
      simp
    have hilt : x.1 < s := Nat.lt_of_not_ge hige
    have hjlt : x.2 < s := Nat.lt_of_not_ge hjge
    have hiPos : 0 < x.1 := Nat.pos_of_ne_zero hi0
    have hjPos : 0 < x.2 := Nat.pos_of_ne_zero hj0
    have hBi := hBbound x.1 hilt
    have hBj := hBbound x.2 hjlt
    have hprod := hBi.mul hBj
    apply HC4.Polynomial.initialForm_eq_zero_of_isWeightLE hprod
    simp [tiltedParameterPenalty, Nat.ne_of_gt hiPos,
      Nat.ne_of_gt hjPos] at hprod ⊢
    exact hBBinterior

  have hdet :
      H.schurA * H.schurC - H.schurB * H.schurB = 0 := by
    simpa [H, GeneralFourBlock.schurDetCore] using
      G.centralDeficitSchurBlock_schurDetCore_eq_zero

  exact tilted_binary_nonCancellation
    (w := w) (A := H.schurA) (B := H.schurB) (C := H.schurC)
    (N := N) (i₀ := q) (j₀ := s) (a := WA) (c := WZ)
    (by rfl) hAqLE hCsLE hAqTopNe hCsTopNe
    (by simpa [target] using hACother)
    (by simpa [target] using hBB)
    hdet

/-- **Finite reflected closure of the central V>1 staircase.**

The earliest honest reflected-line departure is impossible in either
orientation.  This is the final local contradiction promised by Commit C. -/
theorem centralDeficit_impossible
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    False := by
  cases G.firstDeficit_earliestReflectedLineDeparture
      hthree houtThree with
  | left q J s m hq hqJ depart hdepart horder hmissing hm3 hbad
      hmin1 hmin2 hearliest hmax =>
      exact G.centralDeficit_leftTilt_impossible
        hthree houtThree hq hqJ hdepart horder hmissing hm3 hbad
        hmin1 hmin2 hearliest hmax
  | right q J s m hq hqJ depart hdepart horder hmissing hm3 hbad
      hmin1 hmin2 hearliest hmax =>
      exact G.centralDeficit_rightTilt_impossible
        hthree houtThree hq hqJ hdepart horder hmissing hm3 hbad
        hmin1 hmin2 hearliest hmax

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
