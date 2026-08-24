import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidSourceCompression
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurHomogeneousLinearPower
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# Final assembly A17.3B: canonical top layer of the source-complete rigid branch

A17.3A leaves one source-complete rigid obstruction on the literal
right-recentered special fibre `G`.  We must not isolate its abstract packet
by a positive longitudinal source weight: that would move the marked point
`e₀` and is not, by itself, a collision-preserving state move.

Instead this file stays on `G` itself.  From the complete all-`2 x 2`-minors
identity we prove that the maximal ordinary homogeneous component `H_D`
still has Hessian rank at most one.  The retained rigid packet guarantees
`D >= 2`.  The already-proved homogeneous logarithmic-gradient argument,
together with a four-variable affine-line globalisation, then gives

    H_D = a * L^D

for one nonzero linear form `L`.

This is the canonical direction needed by the finite mixed-degree direction
lock.  No family, marked section, determinant clock, or collision is changed
in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open Polynomial
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Ordinary homogeneous layers in four source variables -/

/-- Ordinary integer weight on `Fin 4`. -/
def fourOrdinaryIntegerWeight (_ : Fin 4) : ℤ := 1

/-- The four-variable ordinary integer weight is `ordinaryDegree4`. -/
theorem fourOrdinaryIntegerWeight_eq_ordinaryDegree4
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight fourOrdinaryIntegerWeight d =
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
  rw [Finsupp.weight_apply]
  simp [fourOrdinaryIntegerWeight, Finsupp.sum_fintype,
    HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]

/-- Exact ordinary-degree component of a four-variable polynomial. -/
noncomputable def fourOrdinaryDegreeComponent
    (G : MvPolynomial (Fin 4) K)
    (D : ℕ) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm fourOrdinaryIntegerWeight D G

/-- Every exact ordinary-degree component is homogeneous in the usual sense. -/
theorem fourOrdinaryDegreeComponent_isHomogeneous
    (G : MvPolynomial (Fin 4) K)
    (D : ℕ) :
    (fourOrdinaryDegreeComponent G D).IsHomogeneous D := by
  intro d hd
  unfold fourOrdinaryDegreeComponent at hd
  rw [HC4.Polynomial.coeff_initialForm] at hd
  split at hd
  next hw =>
    have hdeg : HC4.Polynomial.ordinaryDegree4 d = D := by
      rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4] at hw
      exact_mod_cast hw
    have hweight :
        Finsupp.weight (1 : Fin 4 → ℕ) d =
          HC4.Polynomial.ordinaryDegree4 d := by
      rw [← finsuppDegree_eq_ordinaryDegree4 d]
      exact (congrFun Finsupp.degree_eq_weight_one d).symm
    exact hweight.trans hdeg
  next hfalse =>
    exact (hd rfl).elim

/-- A nonzero four-variable polynomial has a maximal ordinary homogeneous
component. -/
theorem exists_maximal_fourOrdinaryDegreeComponent
    (G : MvPolynomial (Fin 4) K)
    (hG : G ≠ 0) :
    ∃ D : ℕ,
      fourOrdinaryDegreeComponent G D ≠ 0 ∧
      (∀ d ∈ G.support, HC4.Polynomial.ordinaryDegree4 d ≤ D) := by
  classical
  have hsupp : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  rcases Finset.exists_max_image G.support HC4.Polynomial.ordinaryDegree4 hsupp with
    ⟨d, hd, hmax⟩
  refine ⟨HC4.Polynomial.ordinaryDegree4 d, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg
      (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff d P) hzero
    change MvPolynomial.coeff d
      (fourOrdinaryDegreeComponent G (HC4.Polynomial.ordinaryDegree4 d)) = 0 at hcoeff
    unfold fourOrdinaryDegreeComponent at hcoeff
    rw [HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4] at hcoeff
    simp at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
  · intro q hq
    exact hmax q hq

/-- A maximal ordinary-degree bound gives the corresponding weighted bound. -/
theorem isWeightLE_fourOrdinary_of_degree_le
    (G : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax : ∀ d ∈ G.support, HC4.Polynomial.ordinaryDegree4 d ≤ D) :
    HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight D G := by
  intro d hd
  rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4]
  exact_mod_cast hmax d hd

/-- The top homogeneous layer inherits every `2 x 2` Hessian-minor identity
from the full polynomial. -/
theorem fourOrdinaryDegreeComponent_allMinors_zero_of_maximal
    (G : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax : ∀ d ∈ G.support, HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hall :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l -
          HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j = 0) :
    ∀ i j k l : Fin 4,
      HC4.Polynomial.hessian (fourOrdinaryDegreeComponent G D) i j *
          HC4.Polynomial.hessian (fourOrdinaryDegreeComponent G D) k l -
        HC4.Polynomial.hessian (fourOrdinaryDegreeComponent G D) i l *
          HC4.Polynomial.hessian (fourOrdinaryDegreeComponent G D) k j = 0 := by
  intro i j k l
  let H := fourOrdinaryDegreeComponent G D
  have hGLE : HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight D G :=
    isWeightLE_fourOrdinary_of_degree_le G D hmax
  have hentryWeight (a b : Fin 4) :
      (D : ℤ) - fourOrdinaryIntegerWeight a - fourOrdinaryIntegerWeight b =
        (D : ℤ) - 2 := by
    simp [fourOrdinaryIntegerWeight]
    ring
  have hijLE : HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight
      ((D : ℤ) - 2) (HC4.Polynomial.hessian G i j) := by
    simpa [hentryWeight] using hGLE.hessian_entry i j
  have hklLE : HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight
      ((D : ℤ) - 2) (HC4.Polynomial.hessian G k l) := by
    simpa [hentryWeight] using hGLE.hessian_entry k l
  have hilLE : HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight
      ((D : ℤ) - 2) (HC4.Polynomial.hessian G i l) := by
    simpa [hentryWeight] using hGLE.hessian_entry i l
  have hkjLE : HC4.Polynomial.IsWeightLE fourOrdinaryIntegerWeight
      ((D : ℤ) - 2) (HC4.Polynomial.hessian G k j) := by
    simpa [hentryWeight] using hGLE.hessian_entry k j
  have hprod1 :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hijLE hklLE
  have hprod2 :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hilLE hkjLE
  have hminorEq :
      HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l =
        HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j :=
    sub_eq_zero.mp (hall i j k l)
  have htopEq := congrArg
    (HC4.Polynomial.initialForm fourOrdinaryIntegerWeight
      (((D : ℤ) - 2) + ((D : ℤ) - 2))) hminorEq
  have hprod1' :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight
          (((D : ℤ) - 2) + ((D : ℤ) - 2))
          (HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l) =
        HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
            (HC4.Polynomial.hessian G i j) *
          HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
            (HC4.Polynomial.hessian G k l) := by
    simpa [fourOrdinaryIntegerWeight] using hprod1
  have hprod2' :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight
          (((D : ℤ) - 2) + ((D : ℤ) - 2))
          (HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j) =
        HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
            (HC4.Polynomial.hessian G i l) *
          HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
            (HC4.Polynomial.hessian G k j) := by
    simpa [fourOrdinaryIntegerWeight] using hprod2
  rw [hprod1', hprod2'] at htopEq
  have hHij :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
          (HC4.Polynomial.hessian G i j) =
        HC4.Polynomial.hessian H i j := by
    dsimp [H, fourOrdinaryDegreeComponent]
    simpa [hentryWeight] using
      (HC4.Polynomial.hessian_initialForm_entry
        fourOrdinaryIntegerWeight (D : ℤ) G i j).symm
  have hHkl :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
          (HC4.Polynomial.hessian G k l) =
        HC4.Polynomial.hessian H k l := by
    dsimp [H, fourOrdinaryDegreeComponent]
    simpa [hentryWeight] using
      (HC4.Polynomial.hessian_initialForm_entry
        fourOrdinaryIntegerWeight (D : ℤ) G k l).symm
  have hHil :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
          (HC4.Polynomial.hessian G i l) =
        HC4.Polynomial.hessian H i l := by
    dsimp [H, fourOrdinaryDegreeComponent]
    simpa [hentryWeight] using
      (HC4.Polynomial.hessian_initialForm_entry
        fourOrdinaryIntegerWeight (D : ℤ) G i l).symm
  have hHkj :
      HC4.Polynomial.initialForm fourOrdinaryIntegerWeight ((D : ℤ) - 2)
          (HC4.Polynomial.hessian G k j) =
        HC4.Polynomial.hessian H k j := by
    dsimp [H, fourOrdinaryDegreeComponent]
    simpa [hentryWeight] using
      (HC4.Polynomial.hessian_initialForm_entry
        fourOrdinaryIntegerWeight (D : ℤ) G k j).symm
  rw [hHij, hHkl, hHil, hHkj] at htopEq
  exact sub_eq_zero.mpr htopEq

/-! ## Four-variable affine-line globalisation -/

/-- Substitute `X_i = a_i + v_i T` into a four-variable polynomial. -/
def fourAffineLineSpecialisation
    (a v : Fin 4 → K) :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

@[simp] theorem fourAffineLineSpecialisation_C
    (a v : Fin 4 → K) (c : K) :
    fourAffineLineSpecialisation a v (MvPolynomial.C c) = Polynomial.C c := by
  simp [fourAffineLineSpecialisation]

@[simp] theorem fourAffineLineSpecialisation_X
    (a v : Fin 4 → K) (i : Fin 4) :
    fourAffineLineSpecialisation a v (MvPolynomial.X i) =
      Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X := by
  simp [fourAffineLineSpecialisation]

/-- Formal chain rule for affine-line substitution in four variables. -/
theorem derivative_fourAffineLineSpecialisation
    (a v : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    (fourAffineLineSpecialisation a v F).derivative =
      ∑ i : Fin 4,
        Polynomial.C (v i) *
          fourAffineLineSpecialisation a v (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [fourAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq, mul_add, Finset.sum_add_distrib]
  · intro p n hp
    simp only [map_mul, fourAffineLineSpecialisation_X,
      Polynomial.derivative_mul, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases n <;> simp [Fin.sum_univ_succ] <;> ring

/-- Multivariate logarithmic-derivative cross identities restrict to one
variable on every affine line. -/
theorem fourAffineLine_logDerivative_cross
    (P Q : MvPolynomial (Fin 4) K)
    (hcross :
      ∀ j : Fin 4,
        P * MvPolynomial.pderiv j Q = Q * MvPolynomial.pderiv j P)
    (a v : Fin 4 → K) :
    fourAffineLineSpecialisation a v P *
        (fourAffineLineSpecialisation a v Q).derivative =
      fourAffineLineSpecialisation a v Q *
        (fourAffineLineSpecialisation a v P).derivative := by
  rw [derivative_fourAffineLineSpecialisation,
    derivative_fourAffineLineSpecialisation]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmap := congrArg (fourAffineLineSpecialisation a v) (hcross j)
  simp only [map_mul] at hmap
  calc
    fourAffineLineSpecialisation a v P *
          (Polynomial.C (v j) *
            fourAffineLineSpecialisation a v (MvPolynomial.pderiv j Q)) =
        Polynomial.C (v j) *
          (fourAffineLineSpecialisation a v P *
            fourAffineLineSpecialisation a v (MvPolynomial.pderiv j Q)) := by ring
    _ = Polynomial.C (v j) *
          (fourAffineLineSpecialisation a v Q *
            fourAffineLineSpecialisation a v (MvPolynomial.pderiv j P)) := by rw [hmap]
    _ = fourAffineLineSpecialisation a v Q *
          (Polynomial.C (v j) *
            fourAffineLineSpecialisation a v (MvPolynomial.pderiv j P)) := by ring

/-- Four-variable affine-line proportionality from logarithmic derivatives. -/
theorem fourAffineLine_eq_C_mul_of_logDerivative_cross
    (P Q : MvPolynomial (Fin 4) K)
    (hcross :
      ∀ j : Fin 4,
        P * MvPolynomial.pderiv j Q = Q * MvPolynomial.pderiv j P)
    (a v : Fin 4 → K)
    (hPline : fourAffineLineSpecialisation a v P ≠ 0) :
    ∃ c : K,
      fourAffineLineSpecialisation a v Q =
        Polynomial.C c * fourAffineLineSpecialisation a v P := by
  exact polynomial_eq_C_mul_of_logDerivative_cross
    (fourAffineLineSpecialisation a v P)
    (fourAffineLineSpecialisation a v Q)
    hPline
    (fourAffineLine_logDerivative_cross P Q hcross a v)

@[simp] theorem eval_fourAffineLineSpecialisation
    (a v : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K)
    (t : K) :
    Polynomial.eval t (fourAffineLineSpecialisation a v F) =
      MvPolynomial.eval (fun i => a i + v i * t) F := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [fourAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    have hvar :
        Polynomial.eval t
            (fourAffineLineSpecialisation a v (MvPolynomial.X i)) =
          MvPolynomial.eval (fun j => a j + v j * t) (MvPolynomial.X i) := by
      simp [fourAffineLineSpecialisation]
    have hmul := congrArg₂ (fun x y : K => x * y) hp hvar
    simpa only [map_mul, Polynomial.eval_mul] using hmul

/-- A nonzero four-variable polynomial is nonzero at some point over the
characteristic-zero field. -/
theorem exists_eval_four_ne_zero_of_ne_zero
    (P : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0) :
    ∃ a : Fin 4 → K, MvPolynomial.eval a P ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hP
  apply MvPolynomial.funext
  intro a
  simp [hnone a]

/-- Globalise four-variable affine-line proportionality to one scalar. -/
theorem mvPolynomial_four_eq_C_mul_of_affineLine_proportional
    (P Q : MvPolynomial (Fin 4) K)
    (hP : P ≠ 0)
    (hline :
      ∀ (a v : Fin 4 → K),
        fourAffineLineSpecialisation a v P ≠ 0 →
          ∃ c : K,
            fourAffineLineSpecialisation a v Q =
              Polynomial.C c * fourAffineLineSpecialisation a v P) :
    ∃ c : K, Q = MvPolynomial.C c * P := by
  classical
  rcases exists_eval_four_ne_zero_of_ne_zero P hP with ⟨a, ha⟩
  let c : K := MvPolynomial.eval a Q / MvPolynomial.eval a P
  refine ⟨c, ?_⟩
  apply MvPolynomial.funext
  intro b
  let v : Fin 4 → K := fun i => b i - a i
  have hPline : fourAffineLineSpecialisation a v P ≠ 0 := by
    intro hzero
    have hzero0 := congrArg (Polynomial.eval (0 : K)) hzero
    have hzeroEval : MvPolynomial.eval a P = 0 := by
      simpa [v] using hzero0
    exact ha hzeroEval
  rcases hline a v hPline with ⟨d, hd⟩
  have h0 : MvPolynomial.eval a Q = d * MvPolynomial.eval a P := by
    have h := congrArg (Polynomial.eval (0 : K)) hd
    simpa [v] using h
  have hd_eq : d = c := by
    dsimp [c]
    apply (eq_div_iff ha).2
    simpa using h0.symm
  have h1 : MvPolynomial.eval b Q = d * MvPolynomial.eval b P := by
    have h := congrArg (Polynomial.eval (1 : K)) hd
    simpa [v] using h
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simpa [hd_eq] using h1

/-- The generic rank-one homogeneous log-gradient packet globalises in four
variables exactly as in the already-green ternary argument. -/
theorem rankOneHomogeneousLogGradientData_four_global
    {H : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m) :
    ∃ c : Fin 4 → K,
      ∀ i : Fin 4,
        MvPolynomial.pderiv i H =
          MvPolynomial.C (c i) * MvPolynomial.pderiv G.pivot H := by
  classical
  have hone :
      ∀ i : Fin 4, ∃ c : K,
        MvPolynomial.pderiv i H =
          MvPolynomial.C c * MvPolynomial.pderiv G.pivot H := by
    intro i
    apply mvPolynomial_four_eq_C_mul_of_affineLine_proportional
      (MvPolynomial.pderiv G.pivot H)
      (MvPolynomial.pderiv i H)
      G.pivot_ne_zero
    intro a v hpivotLine
    apply fourAffineLine_eq_C_mul_of_logDerivative_cross
    · intro j
      simpa [HC4.Polynomial.hessian_apply] using G.cross i j
    · exact hpivotLine
  choose c hc using hone
  exact ⟨c, hc⟩

/-! ## The rigid top-layer packet -/

/-- The canonical maximal nonlinear layer of a source-complete rigid
obstruction.  All fields refer to the literal right-recentered special fibre
of `S`; no exposure family is introduced. -/
structure AdaptiveAlignedSmithCanonicalRigidTopLayerData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) where
  rigid : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S
  degree : ℕ
  top : MvPolynomial (Fin 4) K
  top_eq :
    top = fourOrdinaryDegreeComponent
      (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber) degree
  top_ne_zero : top ≠ 0
  maximal :
    ∀ d ∈ (longitudinalRightRecenterHom
      (K := K) S.blocker.aligned.endpoint.rawSpecialFiber).support,
      HC4.Polynomial.ordinaryDegree4 d ≤ degree
  degree_ge_two : 2 ≤ degree
  coefficient : K
  ratio : Fin 4 → K
  linearPower :
    top = MvPolynomial.C coefficient * (gradientRatioLinearForm ratio) ^ degree

namespace AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction

/-- The literal right-recentered special fibre is nonzero, witnessed by the
actual rigid packet retained inside the obstruction. -/
theorem literalSpecialFiber_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    longitudinalRightRecenterHom
      (K := K) S.blocker.aligned.endpoint.rawSpecialFiber ≠ 0 := by
  rcases R.mixedDegree_pair with ⟨d₀, d₁, hd₀, hd₁, hdegree⟩
  have hd₀G :
      d₀ ∈ (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber).support := by
    rw [← S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    exact hd₀
  intro hzero
  rw [hzero] at hd₀G
  simp at hd₀G

/-- The rigid packet witnesses that the maximal ordinary degree of the full
special fibre is at least two. -/
theorem rigidPacket_forces_two_le_maximalDegree
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)
    (D : ℕ)
    (hmax :
      ∀ d ∈ (longitudinalRightRecenterHom
        (K := K) S.blocker.aligned.endpoint.rawSpecialFiber).support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D) :
    2 ≤ D := by
  let G := longitudinalRightRecenterHom
    (K := K) S.blocker.aligned.endpoint.rawSpecialFiber
  cases R.packet with
  | planar P hrigid =>
      rcases MvPolynomial.support_nonempty.mpr P.provenance.packet_ne_zero with
        ⟨d, hdQ⟩
      have hcoeffQ := MvPolynomial.mem_support_iff.mp hdQ
      have hcoeffG : MvPolynomial.coeff d G ≠ 0 := by
        rw [P.provenance.packet_eq, coeff_smithSubfaceDegreeComponent] at hcoeffQ
        split at hcoeffQ
        next hsel => exact hcoeffQ
        next hnot => exact (hcoeffQ rfl).elim
      have hdG : d ∈ G.support := MvPolynomial.mem_support_iff.mpr hcoeffG
      have hdeg : HC4.Polynomial.ordinaryDegree4 d = P.degree :=
        ordinaryDegree4_eq_of_isHomogeneous P.provenance.packet_homogeneous hdQ
      have hle := hmax d (by simpa [G] using hdG)
      rw [hdeg] at hle
      exact le_trans P.degree_ge_two hle
  | wSquare P hrigid =>
      have hdG : P.sourceExponent ∈ G.support :=
        MvPolynomial.mem_support_iff.mpr (by simpa [G] using P.sourceCoeff_ne)
      have hle := hmax P.sourceExponent (by simpa [G] using hdG)
      rw [← P.degree_eq] at hle
      exact le_trans P.degree_ge_two hle

/-- **A17.3B rigid top-layer theorem.**

The maximal ordinary homogeneous layer of the honest rigid special fibre is
nonlinear and is exactly a scalar multiple of a power of one linear form. -/
theorem toRigidTopLayerData
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    Nonempty (AdaptiveAlignedSmithCanonicalRigidTopLayerData S) := by
  let G := longitudinalRightRecenterHom
    (K := K) S.blocker.aligned.endpoint.rawSpecialFiber
  have hG : G ≠ 0 := by
    simpa [G] using R.literalSpecialFiber_ne_zero
  rcases exists_maximal_fourOrdinaryDegreeComponent G hG with
    ⟨D, hHne, hmax⟩
  let H := fourOrdinaryDegreeComponent G D
  have hD : 2 ≤ D := R.rigidPacket_forces_two_le_maximalDegree D (by simpa [G] using hmax)
  have hhom : H.IsHomogeneous D :=
    fourOrdinaryDegreeComponent_isHomogeneous G D
  have hallG :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l -
          HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j = 0 := by
    simpa [G] using R.raw_allMinors
  have hallH :
      ∀ i j k l : Fin 4,
        HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
          HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0 := by
    simpa [H] using
      fourOrdinaryDegreeComponent_allMinors_zero_of_maximal G D hmax hallG
  rcases rankOneHomogeneousLogGradientData_of_allMinors
      H D hhom (by simpa [H] using hHne) hD hallH with ⟨L⟩
  rcases rankOneHomogeneousLogGradientData_four_global L with ⟨c, hc⟩
  rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
      D H hhom (by omega) L.pivot L.pivot_ne_zero c hc with
    ⟨a, ha⟩
  exact ⟨{
    rigid := R
    degree := D
    top := H
    top_eq := by rfl
    top_ne_zero := by simpa [H] using hHne
    maximal := by simpa [G] using hmax
    degree_ge_two := hD
    coefficient := a
    ratio := c
    linearPower := ha
  }⟩

end AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction

end

end HC4.Valuation
