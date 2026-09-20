import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitTiltedSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitSourceContinuation
import HC4.Polynomial.DerivativeBounds
import Mathlib.Tactic

/-!
# Tilted coefficient bounds for the central Schur series

The source-facing earliest-departure selector gives a uniform tilted-weight
bound on every positive source layer strictly before the selected bad order
`s`.  This file transports that bound through the parameter-first Hessian
and the denominator-cleared Schur formulas.

A positive parameter coefficient pays one copy of the first-deficit order
`q`; coefficient zero pays none.  This penalty is subadditive under
parameter convolution, so the coefficient bounds are closed under ring
operations.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u

def tiltedParameterPenalty (q n : ℕ) : ℤ :=
  if n = 0 then 0 else (q : ℤ)

theorem tiltedParameterPenalty_add_le (q i j : ℕ) :
    tiltedParameterPenalty q (i + j) ≤
      tiltedParameterPenalty q i + tiltedParameterPenalty q j := by
  unfold tiltedParameterPenalty
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [hi, hj] <;> omega

private theorem isWeightLE_mono
    {σ K : Type*} [CommRing K]
    {w : σ → ℤ} {a b : ℤ} {P : MvPolynomial σ K}
    (hab : a ≤ b) (hP : HC4.Polynomial.IsWeightLE w a P) :
    HC4.Polynomial.IsWeightLE w b P := by
  intro e he
  exact le_trans (hP he) hab

private theorem isWeightLE_finset_sum
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

def HasTiltedParameterCoeffBoundBelow
    {σ K : Type*} [CommRing K]
    (w : σ → ℤ) (q s : ℕ) (shift : ℤ)
    (P : Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ n : ℕ, n < s →
    HC4.Polynomial.IsWeightLE w
      (- tiltedParameterPenalty q n - shift) (P.coeff n)

namespace HasTiltedParameterCoeffBoundBelow

variable {σ K : Type*} [CommRing K] [DecidableEq σ]
variable {w : σ → ℤ} {q s : ℕ}

theorem zero (shift : ℤ) :
    HasTiltedParameterCoeffBoundBelow w q s shift
      (0 : Polynomial (MvPolynomial σ K)) := by
  intro n hn
  simp [HC4.Polynomial.isWeightLE_zero]

theorem add
    {a : ℤ} {P Q : Polynomial (MvPolynomial σ K)}
    (hP : HasTiltedParameterCoeffBoundBelow w q s a P)
    (hQ : HasTiltedParameterCoeffBoundBelow w q s a Q) :
    HasTiltedParameterCoeffBoundBelow w q s a (P + Q) := by
  intro n hn
  rw [Polynomial.coeff_add]
  exact (hP n hn).add (hQ n hn)

theorem neg
    {a : ℤ} {P : Polynomial (MvPolynomial σ K)}
    (hP : HasTiltedParameterCoeffBoundBelow w q s a P) :
    HasTiltedParameterCoeffBoundBelow w q s a (-P) := by
  intro n hn
  rw [Polynomial.coeff_neg]
  exact (hP n hn).neg

theorem sub
    {a : ℤ} {P Q : Polynomial (MvPolynomial σ K)}
    (hP : HasTiltedParameterCoeffBoundBelow w q s a P)
    (hQ : HasTiltedParameterCoeffBoundBelow w q s a Q) :
    HasTiltedParameterCoeffBoundBelow w q s a (P - Q) := by
  simpa [sub_eq_add_neg] using hP.add hQ.neg

theorem mul
    {a b : ℤ} {P Q : Polynomial (MvPolynomial σ K)}
    (hP : HasTiltedParameterCoeffBoundBelow w q s a P)
    (hQ : HasTiltedParameterCoeffBoundBelow w q s b Q) :
    HasTiltedParameterCoeffBoundBelow w q s (a + b) (P * Q) := by
  intro n hn
  rw [Polynomial.coeff_mul]
  let A : Finset (ℕ × ℕ) := Finset.antidiagonal n
  let f : (ℕ × ℕ) → MvPolynomial σ K :=
    fun x => P.coeff x.1 * Q.coeff x.2
  change HC4.Polynomial.IsWeightLE w
    (- tiltedParameterPenalty q n - (a + b))
    (∑ x ∈ A, f x)
  apply isWeightLE_finset_sum w
    (- tiltedParameterPenalty q n - (a + b)) A f
  intro x hx
  have hsum : x.1 + x.2 = n := by
    exact Finset.mem_antidiagonal.mp (by simpa [A] using hx)
  have hi : x.1 < s := by omega
  have hj : x.2 < s := by omega
  have hmul := (hP x.1 hi).mul (hQ x.2 hj)
  have hpen := tiltedParameterPenalty_add_le q x.1 x.2
  rw [hsum] at hpen
  apply isWeightLE_mono (hP := hmul)
  nlinarith

end HasTiltedParameterCoeffBoundBelow

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

private theorem firstDeficitLeftTilt_layerZero_isWeightLE
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (d : ℕ) :
    HC4.Polynomial.IsWeightLE
      (firstDeficitLeftTiltWeight d) 0
      (familyParameterLayer P.centralDeficitFamily 0) := by
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  intro e he
  have hne :
      MvPolynomial.coeff e
        (MvPolynomial.monomial G.central
          (MvPolynomial.coeff G.central P.carrier)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have heq : e = G.central := by
    by_contra hnot
    have hce : G.central ≠ e := fun h => hnot h.symm
    rw [MvPolynomial.coeff_monomial] at hne
    simp [hce] at hne
  subst e
  rw [weight_firstDeficitLeftTiltWeight,
    G.central_one_zero, G.central_two_zero]
  norm_num

private theorem firstDeficitRightTilt_layerZero_isWeightLE
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (d : ℕ) :
    HC4.Polynomial.IsWeightLE
      (firstDeficitRightTiltWeight d) 0
      (familyParameterLayer P.centralDeficitFamily 0) := by
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  intro e he
  have hne :
      MvPolynomial.coeff e
        (MvPolynomial.monomial G.central
          (MvPolynomial.coeff G.central P.carrier)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have heq : e = G.central := by
    by_contra hnot
    have hce : G.central ≠ e := fun h => hnot h.symm
    rw [MvPolynomial.coeff_monomial] at hne
    simp [hce] at hne
  subst e
  rw [weight_firstDeficitRightTiltWeight,
    G.central_one_zero, G.central_two_zero]
  norm_num

theorem firstDeficitLeftTilt_parameterHessian_bound
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
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
    (i j : Fin 4) :
    let w := firstDeficitLeftTiltWeight (J - q)
    HasTiltedParameterCoeffBoundBelow w q s (w i + w j)
      (parameterFirstHessian P.centralDeficitFamily i j) := by
  let w := firstDeficitLeftTiltWeight (J - q)
  intro n hn
  rw [parameterFirstHessian_coeff]
  by_cases hn0 : n = 0
  · subst n
    have h0 := G.firstDeficitLeftTilt_layerZero_isWeightLE
      hthree houtThree (J - q)
    have hh := h0.hessian_entry i j
    simpa [w, tiltedParameterPenalty] using hh
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hL := G.firstDeficitLeftTilt_earlierLayer_isWeightLE
      hq hqJ hmin1 hmin2 hearliest hnpos hn
    have hh := hL.hessian_entry i j
    simpa [w, tiltedParameterPenalty, hn0,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh

theorem firstDeficitRightTilt_parameterHessian_bound
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
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
    (i j : Fin 4) :
    let w := firstDeficitRightTiltWeight (J - q)
    HasTiltedParameterCoeffBoundBelow w q s (w i + w j)
      (parameterFirstHessian P.centralDeficitFamily i j) := by
  let w := firstDeficitRightTiltWeight (J - q)
  intro n hn
  rw [parameterFirstHessian_coeff]
  by_cases hn0 : n = 0
  · subst n
    have h0 := G.firstDeficitRightTilt_layerZero_isWeightLE
      hthree houtThree (J - q)
    have hh := h0.hessian_entry i j
    simpa [w, tiltedParameterPenalty] using hh
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hL := G.firstDeficitRightTilt_earlierLayer_isWeightLE
      hq hqJ hmin1 hmin2 hearliest hnpos hn
    have hh := hL.hessian_entry i j
    simpa [w, tiltedParameterPenalty, hn0,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh

theorem firstDeficitLeftTilt_schur_bounds
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 2 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 2 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 2 →
        f 1 + f 2 < q + f 2 * (J - q) →
        s ≤ f 1 + f 2) :
    let d := J - q
    let w := firstDeficitLeftTiltWeight d
    HasTiltedParameterCoeffBoundBelow w q s
        (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.schurA ∧
      HasTiltedParameterCoeffBoundBelow w q s
        ((d : ℤ) - 2) G.centralDeficitSchurBlock.schurB ∧
      HasTiltedParameterCoeffBoundBelow w q s
        (-2) G.centralDeficitSchurBlock.schurC := by
  let d := J - q
  let w := firstDeficitLeftTiltWeight d
  have hH := G.firstDeficitLeftTilt_parameterHessian_bound
    hthree houtThree hq hqJ hmin1 hmin2 hearliest
  have ha : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.a := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_a]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 0
  have hb : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.b := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_b]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 3
  have hd0 : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.d := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_d]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (3 : Fin 4) 3
  have hp : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 1)
      G.centralDeficitSchurBlock.p := by
    rw [G.centralDeficitSchurBlock_p]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 2
  have hq0 : HasTiltedParameterCoeffBoundBelow w q s (-1)
      G.centralDeficitSchurBlock.q := by
    rw [G.centralDeficitSchurBlock_q]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (0 : Fin 4) 1
  have hr : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 1)
      G.centralDeficitSchurBlock.r := by
    rw [G.centralDeficitSchurBlock_r]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (3 : Fin 4) 2
  have hs : HasTiltedParameterCoeffBoundBelow w q s (-1)
      G.centralDeficitSchurBlock.s := by
    rw [G.centralDeficitSchurBlock_s]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (3 : Fin 4) 1
  have hx : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.x := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_x]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (2 : Fin 4) 2
  have hy : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 2)
      G.centralDeficitSchurBlock.y := by
    rw [G.centralDeficitSchurBlock_y]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (2 : Fin 4) 1
  have hz : HasTiltedParameterCoeffBoundBelow w q s (-2)
      G.centralDeficitSchurBlock.z := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_z]
    simpa [w, d, firstDeficitLeftTiltWeight] using hH (1 : Fin 4) 1

  have hA : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.schurA := by
    rw [schurA_eq_sourceRoofFormula]
    have haxd := (ha.mul hx).mul hd0
    have harr := (ha.mul hr).mul hr
    have hppd := (hp.mul hp).mul hd0
    have hprb := (hp.mul hr).mul hb
    have hbpr := (hb.mul hp).mul hr
    have hbxb := (hb.mul hx).mul hb
    convert ((((haxd.sub harr).sub hppd).add hprb).add hbpr).sub hbxb using 1 <;>
      ring
  have hB : HasTiltedParameterCoeffBoundBelow w q s
      ((d : ℤ) - 2) G.centralDeficitSchurBlock.schurB := by
    unfold GeneralFourBlock.schurB
    have hactive : HasTiltedParameterCoeffBoundBelow w q s 0
        G.centralDeficitSchurBlock.activeDet := by
      unfold GeneralFourBlock.activeDet
      simpa using (ha.mul hd0).sub (hb.mul hb)
    have hinside :
        HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 2)
          (G.centralDeficitSchurBlock.d * G.centralDeficitSchurBlock.p *
              G.centralDeficitSchurBlock.q -
            G.centralDeficitSchurBlock.b *
              (G.centralDeficitSchurBlock.p * G.centralDeficitSchurBlock.s +
                G.centralDeficitSchurBlock.q * G.centralDeficitSchurBlock.r) +
            G.centralDeficitSchurBlock.a *
              G.centralDeficitSchurBlock.r * G.centralDeficitSchurBlock.s) := by
      have h1 := (hd0.mul hp).mul hq0
      have h2 := hb.mul ((hp.mul hs).add (hq0.mul hr))
      have h3 := (ha.mul hr).mul hs
      convert (h1.sub h2).add h3 using 1 <;> ring
    exact (hactive.mul hy).sub hinside
  have hC : HasTiltedParameterCoeffBoundBelow w q s (-2)
      G.centralDeficitSchurBlock.schurC := by
    rw [schurC_eq_sourceRoofFormula]
    have hazd := (ha.mul hz).mul hd0
    have hass := (ha.mul hs).mul hs
    have hqqd := (hq0.mul hq0).mul hd0
    have hqsb := (hq0.mul hs).mul hb
    have hbqs := (hb.mul hq0).mul hs
    have hbzb := (hb.mul hz).mul hb
    convert ((((hazd.sub hass).sub hqqd).add hqsb).add hbqs).sub hbzb using 1 <;>
      ring
  exact ⟨hA, hB, hC⟩

theorem firstDeficitRightTilt_schur_bounds
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {q J s : ℕ}
    (hq : q = G.firstDeficitOrder)
    (hqJ : q < J)
    (hmin1 :
      ∀ f ∈ P.carrier.support, 0 < f 1 → J ≤ f 1 + f 2)
    (hmin2 :
      ∀ f ∈ P.carrier.support,
        2 ≤ f 1 → q + 2 * (J - q) ≤ f 1 + f 2)
    (hearliest :
      ∀ f ∈ P.carrier.support,
        3 ≤ f 1 →
        f 1 + f 2 < q + f 1 * (J - q) →
        s ≤ f 1 + f 2) :
    let d := J - q
    let w := firstDeficitRightTiltWeight d
    HasTiltedParameterCoeffBoundBelow w q s
        (-2) G.centralDeficitSchurBlock.schurA ∧
      HasTiltedParameterCoeffBoundBelow w q s
        ((d : ℤ) - 2) G.centralDeficitSchurBlock.schurB ∧
      HasTiltedParameterCoeffBoundBelow w q s
        (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.schurC := by
  let d := J - q
  let w := firstDeficitRightTiltWeight d
  have hH := G.firstDeficitRightTilt_parameterHessian_bound
    hthree houtThree hq hqJ hmin1 hmin2 hearliest
  have ha : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.a := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_a]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 0
  have hb : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.b := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_b]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 3
  have hd0 : HasTiltedParameterCoeffBoundBelow w q s 0
      G.centralDeficitSchurBlock.d := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_d]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (3 : Fin 4) 3
  have hp : HasTiltedParameterCoeffBoundBelow w q s (-1)
      G.centralDeficitSchurBlock.p := by
    rw [G.centralDeficitSchurBlock_p]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 2
  have hq0 : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 1)
      G.centralDeficitSchurBlock.q := by
    rw [G.centralDeficitSchurBlock_q]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (0 : Fin 4) 1
  have hr : HasTiltedParameterCoeffBoundBelow w q s (-1)
      G.centralDeficitSchurBlock.r := by
    rw [G.centralDeficitSchurBlock_r]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (3 : Fin 4) 2
  have hs : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 1)
      G.centralDeficitSchurBlock.s := by
    rw [G.centralDeficitSchurBlock_s]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (3 : Fin 4) 1
  have hx : HasTiltedParameterCoeffBoundBelow w q s (-2)
      G.centralDeficitSchurBlock.x := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_x]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (2 : Fin 4) 2
  have hy : HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 2)
      G.centralDeficitSchurBlock.y := by
    rw [G.centralDeficitSchurBlock_y]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (2 : Fin 4) 1
  have hz : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.z := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    rw [permutedFamilyHessianFourBlock_z]
    simpa [w, d, firstDeficitRightTiltWeight] using hH (1 : Fin 4) 1

  have hA : HasTiltedParameterCoeffBoundBelow w q s (-2)
      G.centralDeficitSchurBlock.schurA := by
    rw [schurA_eq_sourceRoofFormula]
    have haxd := (ha.mul hx).mul hd0
    have harr := (ha.mul hr).mul hr
    have hppd := (hp.mul hp).mul hd0
    have hprb := (hp.mul hr).mul hb
    have hbpr := (hb.mul hp).mul hr
    have hbxb := (hb.mul hx).mul hb
    convert ((((haxd.sub harr).sub hppd).add hprb).add hbpr).sub hbxb using 1 <;>
      ring
  have hB : HasTiltedParameterCoeffBoundBelow w q s
      ((d : ℤ) - 2) G.centralDeficitSchurBlock.schurB := by
    unfold GeneralFourBlock.schurB
    have hactive : HasTiltedParameterCoeffBoundBelow w q s 0
        G.centralDeficitSchurBlock.activeDet := by
      unfold GeneralFourBlock.activeDet
      simpa using (ha.mul hd0).sub (hb.mul hb)
    have hinside :
        HasTiltedParameterCoeffBoundBelow w q s ((d : ℤ) - 2)
          (G.centralDeficitSchurBlock.d * G.centralDeficitSchurBlock.p *
              G.centralDeficitSchurBlock.q -
            G.centralDeficitSchurBlock.b *
              (G.centralDeficitSchurBlock.p * G.centralDeficitSchurBlock.s +
                G.centralDeficitSchurBlock.q * G.centralDeficitSchurBlock.r) +
            G.centralDeficitSchurBlock.a *
              G.centralDeficitSchurBlock.r * G.centralDeficitSchurBlock.s) := by
      have h1 := (hd0.mul hp).mul hq0
      have h2 := hb.mul ((hp.mul hs).add (hq0.mul hr))
      have h3 := (ha.mul hr).mul hs
      convert (h1.sub h2).add h3 using 1 <;> ring
    exact (hactive.mul hy).sub hinside
  have hC : HasTiltedParameterCoeffBoundBelow w q s
      (2 * ((d : ℤ) - 1)) G.centralDeficitSchurBlock.schurC := by
    rw [schurC_eq_sourceRoofFormula]
    have hazd := (ha.mul hz).mul hd0
    have hass := (ha.mul hs).mul hs
    have hqqd := (hq0.mul hq0).mul hd0
    have hqsb := (hq0.mul hs).mul hb
    have hbqs := (hb.mul hq0).mul hs
    have hbzb := (hb.mul hz).mul hb
    convert ((((hazd.sub hass).sub hqqd).add hqsb).add hbqs).sub hbzb using 1 <;>
      ring
  exact ⟨hA, hB, hC⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
