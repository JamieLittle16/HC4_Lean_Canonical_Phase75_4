import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroJet
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurHomogeneousLinearPower
import Mathlib.Tactic

/-!
# Marked-collision and binary Hesse bridge for the stationary planar core

After zero-jet elimination, the canonical equality-wall contribution is a
one- or two-variable special-fibre core.  The transverse core has identically
singular binary Hessian.  This file records two pieces of provenance needed to
settle whether that core can still reach the general planar JC2 terminal.

First, every aligned square source retains the canonical special-fibre exact
gradient collision between `0` and `-e₀`; its zero linear jet is already stored
on the source carrier.

Second, we extract the carrier-independent algebra beneath the earlier
first-key machinery in the genuinely binary case: a nonzero homogeneous
binary polynomial of degree at least two with zero Hessian determinant is a
scalar multiple of a power of one linear form.  This uses the existing
rank-one homogeneous logarithmic-gradient and linear-power arguments, but no
first-key carrier and no JC2 assumption.

The remaining nonhomogeneous task is therefore sharply isolated: show that
successive homogeneous slices of the marked stationary binary core share the
same linear direction, or use the retained moving-family provenance to force
strict progress before that classification is needed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-! ## The aligned source still carries the marked special-fibre collision -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Specialisation of an honest aligned square source retains the canonical
collision between the source origin and the negative longitudinal axis point. -/
theorem DirectClosingAlignedSquareSourceData.specialFiber_markedCollision
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber D.family)
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  have h := polynomialFamilyExactGradientCollision_specialFiber
    D.family (zeroPolynomialSection (K := K)) D.rightSection D.exactCollision
  rw [D.rightSpecialPoint] at h
  simpa [polynomialSectionSpecialPoint, zeroPolynomialSection] using h

/-- Every linear coefficient of a longitudinal zero-jet core vanishes. -/
theorem longitudinalZeroJetCore_linearCoeff_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (face : MvPolynomial (Fin 4) K)
    (face_eq :
      face = Polynomial.initialForm pureLongitudinalTransverseWeight 0
        (polynomialFamilySpecialFiber D.family))
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1) face = 0 := by
  rw [face_eq, HC4.Polynomial.coeff_initialForm]
  split
  · exact D.specialFiber_linearCoeff_zero i
  · rfl

/-- Every linear coefficient of a transverse zero-jet core vanishes as well. -/
theorem transverseZeroJetCore_linearCoeff_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (face : MvPolynomial (Fin 4) K)
    (face_eq :
      face = Polynomial.initialForm
        (directClosingTransverseComplementWeight D.index) 0
        (polynomialFamilySpecialFiber D.family))
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1) face = 0 := by
  rw [face_eq, HC4.Polynomial.coeff_initialForm]
  split
  · exact D.specialFiber_linearCoeff_zero i
  · rfl

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Binary affine-line globalisation -/

/-- Substitute an affine line `Xᵢ = aᵢ + vᵢ T` into a binary polynomial. -/
def binaryAffineLineSpecialisation
    (a v : Fin 2 → K) :
    MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)

@[simp] theorem binaryAffineLineSpecialisation_C
    (a v : Fin 2 → K) (c : K) :
    binaryAffineLineSpecialisation a v (MvPolynomial.C c) =
      Polynomial.C c := by
  simp [binaryAffineLineSpecialisation]

@[simp] theorem binaryAffineLineSpecialisation_X
    (a v : Fin 2 → K) (i : Fin 2) :
    binaryAffineLineSpecialisation a v (MvPolynomial.X i) =
      Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X := by
  simp [binaryAffineLineSpecialisation]

/-- Formal chain rule for binary affine-line specialisation. -/
theorem derivative_binaryAffineLineSpecialisation
    (a v : Fin 2 → K)
    (F : MvPolynomial (Fin 2) K) :
    (binaryAffineLineSpecialisation a v F).derivative =
      ∑ i : Fin 2,
        Polynomial.C (v i) *
          binaryAffineLineSpecialisation a v (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [binaryAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq, mul_add, Finset.sum_add_distrib]
  · intro p n hp
    simp only [map_mul, binaryAffineLineSpecialisation_X,
      Polynomial.derivative_mul, MvPolynomial.pderiv_mul, map_add, hp]
    fin_cases n <;> simp [Fin.sum_univ_succ] <;> ring

/-- A complete binary logarithmic-derivative cross system restricts to the
same one-variable identity on every affine line. -/
theorem binaryAffineLine_logDerivative_cross
    (P Q : MvPolynomial (Fin 2) K)
    (hcross :
      ∀ j : Fin 2,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 2 → K) :
    binaryAffineLineSpecialisation a v P *
        (binaryAffineLineSpecialisation a v Q).derivative =
      binaryAffineLineSpecialisation a v Q *
        (binaryAffineLineSpecialisation a v P).derivative := by
  rw [derivative_binaryAffineLineSpecialisation,
    derivative_binaryAffineLineSpecialisation]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmap := congrArg (binaryAffineLineSpecialisation a v) (hcross j)
  simp only [map_mul] at hmap
  calc
    binaryAffineLineSpecialisation a v P *
          (Polynomial.C (v j) *
            binaryAffineLineSpecialisation a v (MvPolynomial.pderiv j Q)) =
        Polynomial.C (v j) *
          (binaryAffineLineSpecialisation a v P *
            binaryAffineLineSpecialisation a v (MvPolynomial.pderiv j Q)) := by
      ring
    _ = Polynomial.C (v j) *
          (binaryAffineLineSpecialisation a v Q *
            binaryAffineLineSpecialisation a v (MvPolynomial.pderiv j P)) := by
      rw [hmap]
    _ = binaryAffineLineSpecialisation a v Q *
          (Polynomial.C (v j) *
            binaryAffineLineSpecialisation a v (MvPolynomial.pderiv j P)) := by
      ring

/-- Binary affine-line logarithmic rigidity. -/
theorem binaryAffineLine_eq_C_mul_of_logDerivative_cross
    (P Q : MvPolynomial (Fin 2) K)
    (hcross :
      ∀ j : Fin 2,
        P * MvPolynomial.pderiv j Q =
          Q * MvPolynomial.pderiv j P)
    (a v : Fin 2 → K)
    (hPline : binaryAffineLineSpecialisation a v P ≠ 0) :
    ∃ c : K,
      binaryAffineLineSpecialisation a v Q =
        Polynomial.C c * binaryAffineLineSpecialisation a v P := by
  exact polynomial_eq_C_mul_of_logDerivative_cross
    (binaryAffineLineSpecialisation a v P)
    (binaryAffineLineSpecialisation a v Q)
    hPline
    (binaryAffineLine_logDerivative_cross P Q hcross a v)

/-- A nonzero binary polynomial is nonzero at some point. -/
theorem exists_eval_ne_zero_of_ne_zero_finTwo
    (P : MvPolynomial (Fin 2) K)
    (hP : P ≠ 0) :
    ∃ a : Fin 2 → K, MvPolynomial.eval a P ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hP
  apply MvPolynomial.funext
  intro a
  simp [hnone a]

@[simp] theorem eval_binaryAffineLineSpecialisation
    (a v : Fin 2 → K)
    (F : MvPolynomial (Fin 2) K)
    (t : K) :
    Polynomial.eval t (binaryAffineLineSpecialisation a v F) =
      MvPolynomial.eval (fun i => a i + v i * t) F := by
  apply MvPolynomial.induction_on F
  · intro c
    simp [binaryAffineLineSpecialisation]
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    have hvar :
        Polynomial.eval t
            (binaryAffineLineSpecialisation a v (MvPolynomial.X i)) =
          MvPolynomial.eval (fun j => a j + v j * t) (MvPolynomial.X i) := by
      simp [binaryAffineLineSpecialisation]
    have hmul := congrArg₂ (fun x y : K => x * y) hp hvar
    simpa only [map_mul, Polynomial.eval_mul] using hmul

@[simp] theorem eval_zero_binaryAffineLineSpecialisation_sub
    (a b : Fin 2 → K)
    (F : MvPolynomial (Fin 2) K) :
    Polynomial.eval 0
        (binaryAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval a F := by
  rw [eval_binaryAffineLineSpecialisation]
  apply congrArg (fun x : Fin 2 → K => MvPolynomial.eval x F)
  funext i
  ring

@[simp] theorem eval_one_binaryAffineLineSpecialisation_sub
    (a b : Fin 2 → K)
    (F : MvPolynomial (Fin 2) K) :
    Polynomial.eval 1
        (binaryAffineLineSpecialisation a (fun i => b i - a i) F) =
      MvPolynomial.eval b F := by
  rw [eval_binaryAffineLineSpecialisation]
  apply congrArg (fun x : Fin 2 → K => MvPolynomial.eval x F)
  funext i
  ring

/-- Linewise proportionality of two binary polynomials to a nonzero pivot
has one global scalar. -/
theorem mvPolynomial_finTwo_eq_C_mul_of_affineLine_proportional
    (P Q : MvPolynomial (Fin 2) K)
    (hP : P ≠ 0)
    (hline :
      ∀ (a v : Fin 2 → K),
        binaryAffineLineSpecialisation a v P ≠ 0 →
          ∃ c : K,
            binaryAffineLineSpecialisation a v Q =
              Polynomial.C c * binaryAffineLineSpecialisation a v P) :
    ∃ c : K, Q = MvPolynomial.C c * P := by
  classical
  rcases exists_eval_ne_zero_of_ne_zero_finTwo P hP with ⟨a, ha⟩
  let c : K := MvPolynomial.eval a Q / MvPolynomial.eval a P
  refine ⟨c, ?_⟩
  apply MvPolynomial.funext
  intro b
  let v : Fin 2 → K := fun i => b i - a i
  have hPline : binaryAffineLineSpecialisation a v P ≠ 0 := by
    intro hzero
    have hzero0 := congrArg (Polynomial.eval (0 : K)) hzero
    have : MvPolynomial.eval a P = 0 := by
      simpa [v] using hzero0
    exact ha this
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

/-- In two variables, the generic homogeneous logarithmic-gradient packet
already globalises to constant gradient ratios. -/
theorem RankOneHomogeneousLogGradientData.finTwo_globalGradientRatios
    {H : MvPolynomial (Fin 2) K}
    {m : ℕ}
    (G : RankOneHomogeneousLogGradientData H m) :
    ∃ c : Fin 2 → K,
      ∀ i : Fin 2,
        MvPolynomial.pderiv i H =
          MvPolynomial.C (c i) * MvPolynomial.pderiv G.pivot H := by
  classical
  have hone :
      ∀ i : Fin 2,
        ∃ c : K,
          MvPolynomial.pderiv i H =
            MvPolynomial.C c * MvPolynomial.pderiv G.pivot H := by
    intro i
    apply mvPolynomial_finTwo_eq_C_mul_of_affineLine_proportional
      (MvPolynomial.pderiv G.pivot H)
      (MvPolynomial.pderiv i H)
      G.pivot_ne_zero
    intro a v hpivotLine
    apply binaryAffineLine_eq_C_mul_of_logDerivative_cross
    · intro j
      simpa [HC4.Polynomial.hessian_apply] using G.cross i j
    · exact hpivotLine
  choose c hc using hone
  exact ⟨c, hc⟩

/-! ## Binary singular-Hessian homogeneous classification -/

/-- In a symmetric two-by-two Hessian, vanishing of the single determinant
is equivalent to vanishing of every two-by-two minor with repeated indices
allowed. -/
theorem finTwo_allHessianMinorsZero_of_binaryDet_zero
    (H : MvPolynomial (Fin 2) K)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    ∀ i j k l : Fin 2,
      HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
        HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0 := by
  have hsym :
      HC4.Polynomial.hessian H (1 : Fin 2) 0 =
        HC4.Polynomial.hessian H 0 1 := by
    simp only [HC4.Polynomial.hessian_apply]
    exact pderiv_comm_backport 0 1 H
  have hdet' :
      HC4.Polynomial.hessian H 0 0 * HC4.Polynomial.hessian H 1 1 -
        HC4.Polynomial.hessian H 0 1 * HC4.Polynomial.hessian H 0 1 = 0 := by
    change
      HC4.Polynomial.hessian H 0 0 * HC4.Polynomial.hessian H 1 1 -
        (HC4.Polynomial.hessian H 1 0) ^ 2 = 0 at hdet
    rw [hsym] at hdet
    simpa [pow_two] using hdet
  have hprod :
      HC4.Polynomial.hessian H 0 0 * HC4.Polynomial.hessian H 1 1 =
        HC4.Polynomial.hessian H 0 1 * HC4.Polynomial.hessian H 0 1 :=
    sub_eq_zero.mp hdet'
  have hprod_comm :
      HC4.Polynomial.hessian H 1 1 * HC4.Polynomial.hessian H 0 0 =
        HC4.Polynomial.hessian H 0 1 * HC4.Polynomial.hessian H 0 1 := by
    simpa only [mul_comm] using hprod
  have hfinTwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x <;> simp
  intro i j k l
  rcases hfinTwo i with rfl | rfl
  <;> rcases hfinTwo j with rfl | rfl
  <;> rcases hfinTwo k with rfl | rfl
  <;> rcases hfinTwo l with rfl | rfl
  all_goals try simp only [hsym]
  all_goals try simp only [pow_two, hprod, hprod_comm]
  all_goals ring

/-- **Binary homogeneous Hesse collapse.**

A nonzero homogeneous binary polynomial of degree at least two whose Hessian
determinant vanishes is a scalar multiple of a power of one linear form.
This is the exact binary algebraic statement needed by the stationary
zero-jet planar core; it is independent of every HC4 carrier. -/
theorem binaryHomogeneous_eq_linearFormPow_of_hessianDet_zero
    (H : MvPolynomial (Fin 2) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (hH : H ≠ 0)
    (hm : 2 ≤ m)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    ∃ (a : K) (c : Fin 2 → K),
      H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ m := by
  have hall := finTwo_allHessianMinorsZero_of_binaryDet_zero H hdet
  rcases rankOneHomogeneousLogGradientData_of_allMinors
      H m hhom hH hm hall with ⟨G⟩
  rcases G.finTwo_globalGradientRatios with ⟨c, hc⟩
  have hmpos : 0 < m := by omega
  rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
      m H hhom hmpos G.pivot G.pivot_ne_zero c hc with ⟨a, ha⟩
  exact ⟨a, c, ha⟩

/-! ## Provenance package for the remaining canonical wall core -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The exact information retained by a canonical zero-jet wall core before
performing the final nonhomogeneous binary Hesse analysis.  In particular the
ambient aligned source still has the marked collision, while the face itself
has no linear jet. -/
inductive DirectClosingCanonicalSquareMarkedStationaryPlanarCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight 0
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (base_support : IsLongitudinalBaseSupport face)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index) 0
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (base_support : IsTransverseBaseSupport D.index face)
      (base_det_zero :
        binaryDirectionalHessianDet (0 : Fin 4) D.index face = 0)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

/-- Upgrade the zero-jet stationary wall packet with the marked source
collision and explicit vanishing of the face linear jet. -/
theorem DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData.toMarkedCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData C heq) :
    DirectClosingCanonicalSquareMarkedStationaryPlanarCoreData C heq := by
  cases L with
  | longitudinalCore D face face_eq face_ne_zero base_support =>
      exact .longitudinal D face face_eq face_ne_zero base_support
        D.specialFiber_markedCollision
        (longitudinalZeroJetCore_linearCoeff_zero D face face_eq)
  | transverseCore D hindex face face_eq face_ne_zero base_support base_det_zero =>
      exact .transverse D hindex face face_eq face_ne_zero base_support base_det_zero
        D.specialFiber_markedCollision
        (transverseZeroJetCore_linearCoeff_zero D face face_eq)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
