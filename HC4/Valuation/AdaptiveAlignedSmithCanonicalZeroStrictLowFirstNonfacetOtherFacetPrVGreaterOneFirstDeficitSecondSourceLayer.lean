import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSecondInteraction
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Honest source layer forced by the second staggered interaction

The second-interaction theorem is a statement about one diagonal coefficient
of the complete total-deficit Hessian series.  This file converts that
coefficient back to literal source support.

If the missing diagonal is nonzero at parameter order

    k = 2*j - q,

then the exact parameter layer at order `k` has a nonzero second derivative
in the missing source coordinate.  Therefore an actual monomial of that layer
uses the missing coordinate with exponent at least two.  Since the
total-deficit Rees family has exact source-layer provenance, the monomial lies
in the original planar carrier and has total deficit exactly `k`.

No reflected-deficit formula is asserted here.  In particular, the missing
exponent is only proved to be at least two; proving that it is exactly two is
a separate finite-staircase step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero pure second derivative must come from an actual source monomial
using the differentiated coordinate at least twice. -/
theorem exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
    (i : Fin 4)
    (Q : MvPolynomial (Fin 4) K)
    (hsecond :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) ≠ 0) :
    ∃ d ∈ Q.support, 2 ≤ d i := by
  by_contra hnone
  push_neg at hnone
  have hfirstSupport :
      ∀ m : Fin 4 →₀ ℕ,
        MvPolynomial.coeff m (MvPolynomial.pderiv i Q) ≠ 0 →
          m i = 0 := by
    intro m hm
    rw [coeff_pderiv_backport] at hm
    let d : Fin 4 →₀ ℕ := m + Finsupp.single i 1
    have hdcoeff : MvPolynomial.coeff d Q ≠ 0 := by
      intro hz
      dsimp [d] at hz
      rw [hz, zero_mul] at hm
      exact hm rfl
    have hdmem : d ∈ Q.support :=
      MvPolynomial.mem_support_iff.mpr hdcoeff
    have hdlt : d i < 2 := hnone d hdmem
    have hdi : d i = m i + 1 := by
      simp [d]
    omega
  have hzero :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) = 0 := by
    exact pderiv_eq_zero_of_all_supported_exponents_zero
      i (MvPolynomial.pderiv i Q) hfirstSupport
  exact hsecond hzero

/-- A supported exponent at least three in one coordinate forces the third
pure derivative in that coordinate to be nonzero. -/
theorem pderiv_pderiv_pderiv_ne_zero_of_support_exponent_ge_three
    (i : Fin 4)
    (Q : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ Q.support)
    (hd3 : 3 ≤ d i) :
    MvPolynomial.pderiv i
      (MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) ≠ 0 := by
  let d₁ : Fin 4 →₀ ℕ := d - Finsupp.single i 1
  have hdi : d i ≠ 0 := by omega
  have hadd : d₁ + Finsupp.single i 1 = d := by
    dsimp [d₁]
    exact Finsupp.sub_add_single_one_cancel hdi
  have hdne : MvPolynomial.coeff d Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hd₁coeff :
      MvPolynomial.coeff d₁ (MvPolynomial.pderiv i Q) ≠ 0 := by
    rw [coeff_pderiv_backport, hadd]
    apply mul_ne_zero hdne
    exact_mod_cast Nat.succ_ne_zero (d₁ i)
  have hd₁mem :
      d₁ ∈ (MvPolynomial.pderiv i Q).support :=
    MvPolynomial.mem_support_iff.mpr hd₁coeff
  have hd₁i : d₁ i = d i - 1 := by
    simp [d₁]
  have hd₁two : 2 ≤ d₁ i := by omega
  exact pderiv_pderiv_ne_zero_of_support_exponent_ge_two
    (K := K) i (MvPolynomial.pderiv i Q) d₁ hd₁mem hd₁two


/-- Differentiate a product-square identity without exposing a large ambient
proof context to the simplifier. -/
theorem pderiv_right_eq_zero_of_mul_eq_square
    (i : Fin 4)
    (A Z S : MvPolynomial (Fin 4) K)
    (hidentity : A * Z = S * S)
    (hA : MvPolynomial.pderiv i A = 0)
    (hS : MvPolynomial.pderiv i S = 0)
    (hAne : A ≠ 0) :
    MvPolynomial.pderiv i Z = 0 := by
  have hdiff := congrArg (MvPolynomial.pderiv i) hidentity
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul] at hdiff
  rw [hA, hS] at hdiff
  simp only [zero_mul, zero_add, mul_zero, add_zero] at hdiff
  exact (mul_eq_zero.mp hdiff).resolve_left hAne


/-- A monomial which is linear in one coordinate has zero second pure
derivative in that coordinate.  Keeping this calculation state-free prevents
large source-provenance contexts from entering monomial simplification. -/
theorem pderiv_pderiv_monomial_eq_zero_of_exponent_eq_one
    (i : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (a : K)
    (hdi : d i = 1) :
    MvPolynomial.pderiv i
      (MvPolynomial.pderiv i (MvPolynomial.monomial d a)) = 0 := by
  simp [MvPolynomial.pderiv_monomial, hdi]


/-- If a polynomial is constant in coordinate `i`, then every pure Hessian
entry in another coordinate remains constant in `i`. -/
theorem pderiv_hessian_diag_eq_zero_of_pderiv_eq_zero
    (i j : Fin 4)
    (Q : MvPolynomial (Fin 4) K)
    (hi : MvPolynomial.pderiv i Q = 0) :
    MvPolynomial.pderiv i (HC4.Polynomial.hessian Q j j) = 0 := by
  simp only [HC4.Polynomial.hessian_apply]
  calc
    MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv j Q)) =
      MvPolynomial.pderiv j
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)) := by
          rw [pderiv_comm_commRing i j
            (MvPolynomial.pderiv j Q)]
          rw [pderiv_comm_commRing i j Q]
    _ = 0 := by rw [hi]; simp

/-- If the pure second derivative in coordinate `i` vanishes, then the
`i`-derivative of any Hessian entry with one `i` slot also vanishes. -/
theorem pderiv_hessian_mixed_eq_zero_of_second_pderiv_eq_zero
    (i j : Fin 4)
    (Q : MvPolynomial (Fin 4) K)
    (hii :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) = 0) :
    MvPolynomial.pderiv i (HC4.Polynomial.hessian Q j i) = 0 := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [pderiv_comm_commRing i j Q]
  rw [pderiv_comm_commRing i j (MvPolynomial.pderiv i Q)]
  rw [hii]
  simp


/-- Tiny arithmetic core of the reflected left deficit identity. -/
theorem reflected_left_deficit_arithmetic
    {q j k o₁ o₂ s₁ s₂ : ℕ}
    (hj : j = o₁ + o₂)
    (hk : k = 2 * j - q)
    (ho₂ : o₂ = 1)
    (hqj : q < j)
    (hs : s₁ + s₂ = k)
    (hs₂ : s₂ = 2) :
    q + s₁ = 2 * o₁ := by
  omega

/-- Tiny arithmetic core of the reflected right deficit identity. -/
theorem reflected_right_deficit_arithmetic
    {q j k o₁ o₂ s₁ s₂ : ℕ}
    (hj : j = o₁ + o₂)
    (hk : k = 2 * j - q)
    (ho₁ : o₁ = 1)
    (hqj : q < j)
    (hs : s₁ + s₂ = k)
    (hs₁ : s₁ = 2) :
    q + s₂ = 2 * o₂ := by
  omega

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

/-- Left active-middle entry is the honest `(1,1)` Hessian entry of
the exact total-deficit layer. -/
theorem firstDeficitLeftStaggeredBlock_d_coeff
    (n : ℕ) :
    G.firstDeficitLeftStaggeredBlock.d.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (1 : Fin 4) 1 := by
  unfold firstDeficitLeftStaggeredBlock
    firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply, firstDeficitLeftStaggeredPerm_one]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (1 : Fin 4) 1

/-- Left mixed entry is the honest `(1,2)` Hessian entry of the exact
total-deficit layer. -/
theorem firstDeficitLeftStaggeredBlock_s_coeff
    (n : ℕ) :
    G.firstDeficitLeftStaggeredBlock.s.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (1 : Fin 4) 2 := by
  unfold firstDeficitLeftStaggeredBlock
    firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    firstDeficitLeftStaggeredPerm_one,
    firstDeficitLeftStaggeredPerm_three]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (1 : Fin 4) 2

/-- Right active-middle entry is the honest `(2,2)` Hessian entry. -/
theorem firstDeficitRightStaggeredBlock_d_coeff
    (n : ℕ) :
    G.firstDeficitRightStaggeredBlock.d.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (2 : Fin 4) 2 := by
  unfold firstDeficitRightStaggeredBlock
    firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply, firstDeficitRightStaggeredPerm_one]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (2 : Fin 4) 2

/-- Right mixed entry is the honest `(2,1)` Hessian entry. -/
theorem firstDeficitRightStaggeredBlock_s_coeff
    (n : ℕ) :
    G.firstDeficitRightStaggeredBlock.s.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (2 : Fin 4) 1 := by
  unfold firstDeficitRightStaggeredBlock
    firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    firstDeficitRightStaggeredPerm_one,
    firstDeficitRightStaggeredPerm_three]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (2 : Fin 4) 1

/-- The left staggered missing diagonal is literally the `(2,2)` Hessian
entry of the exact total-deficit source layer. -/
theorem firstDeficitLeftStaggeredBlock_z_coeff
    (n : ℕ) :
    G.firstDeficitLeftStaggeredBlock.z.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (2 : Fin 4) 2 := by
  unfold firstDeficitLeftStaggeredBlock
    firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply, firstDeficitLeftStaggeredPerm_three]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (2 : Fin 4) 2

/-- Right-oriented mirror: the missing diagonal is the `(1,1)` Hessian
entry of the exact source layer. -/
theorem firstDeficitRightStaggeredBlock_z_coeff
    (n : ℕ) :
    G.firstDeficitRightStaggeredBlock.z.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (1 : Fin 4) 1 := by
  unfold firstDeficitRightStaggeredBlock
    firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply, firstDeficitRightStaggeredPerm_three]
  exact parameterFirstHessian_coeff
    P.centralDeficitFamily n (1 : Fin 4) 1

/-- Provenance-rich source monomial forced at the second interaction order. -/
inductive FirstDeficitSecondSourceLayerGeometry : Prop
  | left
      (first opposite second : Fin 4 →₀ ℕ)
      (B : K)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = q)
      (first_two : first 2 = 0)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (opposite_coefficient_ne_zero : B ≠ 0)
      (opposite_layer_eq :
        familyParameterLayer P.centralDeficitFamily j =
          MvPolynomial.monomial opposite B)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_two_ge : 2 ≤ second 2)
      (hessian_identity :
        HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily k)
              (2 : Fin 4) 2 =
          HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (1 : Fin 4) 2 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (1 : Fin 4) 2)
  | right
      (first opposite second : Fin 4 →₀ ℕ)
      (B : K)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = q)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (opposite_coefficient_ne_zero : B ≠ 0)
      (opposite_layer_eq :
        familyParameterLayer P.centralDeficitFamily j =
          MvPolynomial.monomial opposite B)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_one_ge : 2 ≤ second 1)
      (hessian_identity :
        HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily k)
              (1 : Fin 4) 1 =
          HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (2 : Fin 4) 1 *
            HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (2 : Fin 4) 1)

/-- **Second interaction -> honest source layer.**

The forced diagonal coefficient at `2*j-q` is realized by an actual source
monomial in precisely that total-deficit layer, with missing-coordinate
exponent at least two. -/
theorem firstDeficit_secondSourceLayerGeometry
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitSecondSourceLayerGeometry := by
  rcases G.firstDeficit_secondInteractionGeometry hthree houtThree with O
  cases O with
  | left first opposite B hfirst hfirst1 hfirst2 huniq hop hop2
      hstrict hminimal hB hlayer hmixed hz heq =>
      let q := G.firstDeficitOrder
      let j := opposite 1 + opposite 2
      let k := 2 * j - q
      have hderiv :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily k)) ≠ 0 := by
        have hz' := hz
        change G.firstDeficitLeftStaggeredBlock.z.coeff k ≠ 0 at hz'
        rw [G.firstDeficitLeftStaggeredBlock_z_coeff k] at hz'
        simpa only [HC4.Polynomial.hessian_apply] using hz'
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily k) hderiv with
        ⟨second, hsecondLayer, hsecond2⟩
      have hsource :=
        (P.centralDeficitFamily_layer_mem_iff k second).1 hsecondLayer
      have heqSource := heq
      rw [G.firstDeficitLeftStaggeredBlock_d_coeff,
        G.firstDeficitLeftStaggeredBlock_z_coeff,
        G.firstDeficitLeftStaggeredBlock_s_coeff] at heqSource
      have heqSource' :
          HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily k)
                (2 : Fin 4) 2 =
            HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily j)
                (1 : Fin 4) 2 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily j)
                (1 : Fin 4) 2 := by
        simpa [q, j, k, firstDeficitLayer] using heqSource
      exact .left first opposite second B q j k
        rfl rfl rfl hfirst
        (by simpa [q] using hfirst1) hfirst2 huniq
        hop hop2 hB (by simpa [j] using hlayer)
        (by simpa [q, j] using hstrict)
        hsource.1 hsource.2 hsecond2 heqSource'
  | right first opposite B hfirst hfirst1 hfirst2 huniq hop hop1
      hstrict hminimal hB hlayer hmixed hz heq =>
      let q := G.firstDeficitOrder
      let j := opposite 1 + opposite 2
      let k := 2 * j - q
      have hderiv :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily k)) ≠ 0 := by
        have hz' := hz
        change G.firstDeficitRightStaggeredBlock.z.coeff k ≠ 0 at hz'
        rw [G.firstDeficitRightStaggeredBlock_z_coeff k] at hz'
        simpa only [HC4.Polynomial.hessian_apply] using hz'
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily k) hderiv with
        ⟨second, hsecondLayer, hsecond1⟩
      have hsource :=
        (P.centralDeficitFamily_layer_mem_iff k second).1 hsecondLayer
      have heqSource := heq
      rw [G.firstDeficitRightStaggeredBlock_d_coeff,
        G.firstDeficitRightStaggeredBlock_z_coeff,
        G.firstDeficitRightStaggeredBlock_s_coeff] at heqSource
      have heqSource' :
          HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily k)
                (1 : Fin 4) 1 =
            HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily j)
                (2 : Fin 4) 1 *
              HC4.Polynomial.hessian
                (familyParameterLayer P.centralDeficitFamily j)
                (2 : Fin 4) 1 := by
        simpa [q, j, k, firstDeficitLayer] using heqSource
      exact .right first opposite second B q j k
        rfl rfl rfl hfirst hfirst1
        (by simpa [q] using hfirst2) huniq
        hop hop1 hB (by simpa [j] using hlayer)
        (by simpa [q, j] using hstrict)
        hsource.1 hsource.2 hsecond1 heqSource'

/-- Exact reflected second-layer deficit geometry forced by the
second-interaction Hessian identity. -/
inductive FirstDeficitReflectedSecondLayerGeometry : Prop
  | left
      (first opposite second : Fin 4 →₀ ℕ)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = q)
      (first_two : first 2 = 0)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_two : second 2 = 2)
      (reflected_one : q + second 1 = 2 * opposite 1)
  | right
      (first opposite second : Fin 4 →₀ ℕ)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = q)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_one : second 1 = 2)
      (reflected_two : q + second 2 = 2 * opposite 2)

/-- **Exact reflected deficit layer.**

Differentiating the second-interaction identity once more in the missing
coordinate shows that the third pure derivative of the forced second layer
vanishes.  Hence its missing-coordinate exponent is at most two; the existing
second-derivative witness gives the reverse inequality. -/
theorem firstDeficit_reflectedSecondLayerGeometry
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitReflectedSecondLayerGeometry := by
  rcases G.firstDeficit_secondSourceLayerGeometry hthree houtThree with O
  cases O with
  | left first opposite second B q j k hq hj hk
      hfirst hfirst1 hfirst2 huniq hop hop2 hB hlayer hqj
      hsecond hsecondOrder hsecond2 hid =>
      have hfirstKernel :
          MvPolynomial.pderiv (2 : Fin 4) G.firstDeficitLayer = 0 := by
        apply pderiv_eq_zero_of_all_supported_exponents_zero
        intro d hd
        rw [huniq d hd, hfirst2]
      have hA0 :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1) = 0 := by
        exact pderiv_hessian_diag_eq_zero_of_pderiv_eq_zero
          (K := K) (2 : Fin 4) (1 : Fin 4)
          G.firstDeficitLayer hfirstKernel
      have hOppSecond :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily j)) = 0 := by
        rw [hlayer]
        exact pderiv_pderiv_monomial_eq_zero_of_exponent_eq_one
          (K := K) (2 : Fin 4) opposite B hop2
      have hS0 :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (1 : Fin 4) 2) = 0 := by
        exact pderiv_hessian_mixed_eq_zero_of_second_pderiv_eq_zero
          (K := K) (2 : Fin 4) (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily j) hOppSecond
      have hqTwo : 2 ≤ q := by
        rw [hq]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hAne :
          HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1 ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (1 : Fin 4) G.firstDeficitLayer first
            hfirst (by rw [hfirst1]; exact hqTwo))
      have hthirdHessian :
          MvPolynomial.pderiv (2 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily k)
              (2 : Fin 4) 2) = 0 := by
        exact pderiv_right_eq_zero_of_mul_eq_square
          (K := K) (2 : Fin 4)
          (HC4.Polynomial.hessian G.firstDeficitLayer (1 : Fin 4) 1)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily k)
            (2 : Fin 4) 2)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily j)
            (1 : Fin 4) 2)
          hid hA0 hS0 hAne
      have hthird :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (MvPolynomial.pderiv (2 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily k))) = 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using hthirdHessian
      have hsecondLayer :
          second ∈
            (familyParameterLayer P.centralDeficitFamily k).support := by
        rw [P.centralDeficitFamily_layer_mem_iff]
        exact ⟨hsecond, hsecondOrder⟩
      have hsecondLe : second 2 ≤ 2 := by
        by_contra hnot
        have hthreeExp : 3 ≤ second 2 := by
          exact Nat.lt_of_not_ge hnot
        exact
          (pderiv_pderiv_pderiv_ne_zero_of_support_exponent_ge_three
            (K := K) (2 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily k)
            second hsecondLayer hthreeExp) hthird
      have hsecondEq : second 2 = 2 :=
        Nat.le_antisymm hsecondLe hsecond2
      have hreflect : q + second 1 = 2 * opposite 1 :=
        reflected_left_deficit_arithmetic
          hj hk hop2 hqj hsecondOrder hsecondEq
      exact .left first opposite second q j k
        hq hj hk hfirst hfirst1 hfirst2 hop hop2 hqj
        hsecond hsecondOrder hsecondEq hreflect
  | right first opposite second B q j k hq hj hk
      hfirst hfirst1 hfirst2 huniq hop hop1 hB hlayer hqj
      hsecond hsecondOrder hsecond1 hid =>
      have hfirstKernel :
          MvPolynomial.pderiv (1 : Fin 4) G.firstDeficitLayer = 0 := by
        apply pderiv_eq_zero_of_all_supported_exponents_zero
        intro d hd
        rw [huniq d hd, hfirst1]
      have hA0 :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2) = 0 := by
        exact pderiv_hessian_diag_eq_zero_of_pderiv_eq_zero
          (K := K) (1 : Fin 4) (2 : Fin 4)
          G.firstDeficitLayer hfirstKernel
      have hOppSecond :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily j)) = 0 := by
        rw [hlayer]
        exact pderiv_pderiv_monomial_eq_zero_of_exponent_eq_one
          (K := K) (1 : Fin 4) opposite B hop1
      have hS0 :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily j)
              (2 : Fin 4) 1) = 0 := by
        exact pderiv_hessian_mixed_eq_zero_of_second_pderiv_eq_zero
          (K := K) (1 : Fin 4) (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily j) hOppSecond
      have hqTwo : 2 ≤ q := by
        rw [hq]
        exact firstDeficitOrder_two_le G hthree houtThree
      have hAne :
          HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2 ≠ 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using
          (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
            (K := K) (2 : Fin 4) G.firstDeficitLayer first
            hfirst (by rw [hfirst2]; exact hqTwo))
      have hthirdHessian :
          MvPolynomial.pderiv (1 : Fin 4)
            (HC4.Polynomial.hessian
              (familyParameterLayer P.centralDeficitFamily k)
              (1 : Fin 4) 1) = 0 := by
        exact pderiv_right_eq_zero_of_mul_eq_square
          (K := K) (1 : Fin 4)
          (HC4.Polynomial.hessian G.firstDeficitLayer (2 : Fin 4) 2)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily k)
            (1 : Fin 4) 1)
          (HC4.Polynomial.hessian
            (familyParameterLayer P.centralDeficitFamily j)
            (2 : Fin 4) 1)
          hid hA0 hS0 hAne
      have hthird :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (MvPolynomial.pderiv (1 : Fin 4)
                (familyParameterLayer P.centralDeficitFamily k))) = 0 := by
        simpa only [HC4.Polynomial.hessian_apply] using hthirdHessian
      have hsecondLayer :
          second ∈
            (familyParameterLayer P.centralDeficitFamily k).support := by
        rw [P.centralDeficitFamily_layer_mem_iff]
        exact ⟨hsecond, hsecondOrder⟩
      have hsecondLe : second 1 ≤ 2 := by
        by_contra hnot
        have hthreeExp : 3 ≤ second 1 := by
          exact Nat.lt_of_not_ge hnot
        exact
          (pderiv_pderiv_pderiv_ne_zero_of_support_exponent_ge_three
            (K := K) (1 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily k)
            second hsecondLayer hthreeExp) hthird
      have hsecondEq : second 1 = 2 :=
        Nat.le_antisymm hsecondLe hsecond1
      have hreflect : q + second 2 = 2 * opposite 2 :=
        reflected_right_deficit_arithmetic
          hj hk hop1 hqj hsecondOrder hsecondEq
      exact .right first opposite second q j k
        hq hj hk hfirst hfirst1 hfirst2 hop hop1 hqj
        hsecond hsecondOrder hsecondEq hreflect

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
