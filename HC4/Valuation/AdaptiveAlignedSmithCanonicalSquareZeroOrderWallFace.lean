import HC4.Valuation.AdaptiveAlignedSmithCanonicalSquareZeroOrderFamilyWallShape
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# Exact affine face carried by a zero-order canonical square wall

The preceding zero-order wall classifier shows that an offending special-fibre
monomial has degree at most one in the coordinates complementary to the
canonical square axis.  For the restart argument a single monomial is not the
right object: the exact weighted face containing it is.

This file promotes the witness to that whole special-fibre face.  The face is
nonzero, every one of its monomials has the same complementary degree (hence
that degree is still at most one), and consequently every second derivative
in two complementary directions vanishes identically.

Thus the equality-wall residue is now a genuine polynomial
`affine/separated` face, ready for the already-existing mixed-pivot versus
affine-channel machinery.  No new geometric hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Negative weight which ignores the marked coordinate `0` and a transverse
square axis `ell`, and measures total degree in the two complementary
coordinates. -/
def directClosingTransverseComplementWeight
    (ell : Fin 4) (i : Fin 4) : ℤ :=
  if i = (0 : Fin 4) ∨ i = ell then 0 else -1

/-- The complementary negative weight is exactly minus complementary degree. -/
theorem weight_directClosingTransverseComplementWeight
    (ell : Fin 4) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (directClosingTransverseComplementWeight ell) d =
      -(directClosingTransverseComplementDegree ell d : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · fin_cases ell
    · simp [directClosingTransverseComplementWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
    · simp [directClosingTransverseComplementWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
    · simp [directClosingTransverseComplementWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
    · simp [directClosingTransverseComplementWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
  · intro i
    simp

/-- A supported monomial of the exact longitudinal-transverse initial form
has exactly the selected transverse degree. -/
theorem support_initialForm_pureLongitudinalTransverseDegree_eq
    (F : MvPolynomial (Fin 4) K) (m : ℕ)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈
      (initialForm pureLongitudinalTransverseWeight (-(m : ℤ)) F).support) :
    directClosingLongitudinalTransverseDegree d = m := by
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_initialForm] at hc
  by_cases hw :
      Finsupp.weight pureLongitudinalTransverseWeight d = -(m : ℤ)
  · have hdeg : pureLongitudinalTransverseDegree d = m := by
      rw [weight_pureLongitudinalTransverseWeight] at hw
      have hcast : (pureLongitudinalTransverseDegree d : ℤ) = (m : ℤ) := by
        omega
      exact_mod_cast hcast
    simpa [pureLongitudinalTransverseDegree,
      directClosingLongitudinalTransverseDegree] using hdeg
  · simp [hw] at hc

/-- A supported monomial of the exact complementary initial form has exactly
the selected complementary degree. -/
theorem support_initialForm_transverseComplementDegree_eq
    (ell : Fin 4) (F : MvPolynomial (Fin 4) K) (m : ℕ)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈
      (initialForm (directClosingTransverseComplementWeight ell)
        (-(m : ℤ)) F).support) :
    directClosingTransverseComplementDegree ell d = m := by
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_initialForm] at hc
  by_cases hw :
      Finsupp.weight (directClosingTransverseComplementWeight ell) d =
        -(m : ℤ)
  · rw [weight_directClosingTransverseComplementWeight] at hw
    have hcast :
        (directClosingTransverseComplementDegree ell d : ℤ) = (m : ℤ) := by
      omega
    exact_mod_cast hcast
  · simp [hw] at hc

/-- If a support witness has the selected weight, the corresponding exact
initial form is nonzero. -/
theorem initialForm_ne_zero_of_support_weight
    (w : Fin 4 → ℤ) (m : ℤ)
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hw : Finsupp.weight w d = m) :
    initialForm w m F ≠ 0 := by
  intro hz
  have hcoeff := congrArg (MvPolynomial.coeff d) hz
  rw [coeff_initialForm, if_pos hw] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- Adding one genuinely complementary variable raises complementary degree by
exactly one. -/
theorem directClosingTransverseComplementDegree_add_single
    (ell i : Fin 4)
    (hi0 : i ≠ (0 : Fin 4))
    (hiel : i ≠ ell)
    (d : Fin 4 →₀ ℕ) :
    directClosingTransverseComplementDegree ell
        (d + Finsupp.single i 1) =
      directClosingTransverseComplementDegree ell d + 1 := by
  fin_cases ell <;> fin_cases i <;>
    simp [directClosingTransverseComplementDegree, Fin.sum_univ_four,
      Finsupp.add_apply] at * <;> omega

/-- A polynomial whose support has total transverse degree at most one has no
second derivative in two transverse directions. -/
theorem pderiv_pderiv_eq_zero_of_longitudinalTransverseDegree_le_one
    (F : MvPolynomial (Fin 4) K)
    (hsupp :
      ∀ d ∈ F.support,
        directClosingLongitudinalTransverseDegree d ≤ 1)
    (j k : Fin 3) :
    MvPolynomial.pderiv k.succ (MvPolynomial.pderiv j.succ F) = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_zero]
  by_contra hcoeff2
  have hcoeff1 :
      MvPolynomial.coeff (d + Finsupp.single k.succ 1)
        (MvPolynomial.pderiv j.succ F) ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) k.succ
      (MvPolynomial.pderiv j.succ F) d] at hcoeff2
    intro hz
    apply hcoeff2
    simp [hz]
  have hsourceCoeff :
      MvPolynomial.coeff
        ((d + Finsupp.single k.succ 1) + Finsupp.single j.succ 1) F ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) j.succ F
      (d + Finsupp.single k.succ 1)] at hcoeff1
    intro hz
    apply hcoeff1
    simp [hz]
  have hsourceSupport :
      (d + Finsupp.single k.succ 1) + Finsupp.single j.succ 1 ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hdeg := hsupp _ hsourceSupport
  have hk := directClosingLongitudinalTransverseDegree_add_single_succ d k
  have hj := directClosingLongitudinalTransverseDegree_add_single_succ
    (d + Finsupp.single k.succ 1) j
  rw [hj, hk] at hdeg
  omega

/-- If the support has complementary degree at most one, then every Hessian
entry using two coordinates complementary to `{0, ell}` vanishes. -/
theorem pderiv_pderiv_eq_zero_of_transverseComplementDegree_le_one
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (hsupp :
      ∀ d ∈ F.support,
        directClosingTransverseComplementDegree ell d ≤ 1)
    (i j : Fin 4)
    (hi0 : i ≠ (0 : Fin 4)) (hiel : i ≠ ell)
    (hj0 : j ≠ (0 : Fin 4)) (hjel : j ≠ ell) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i F) = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_zero]
  by_contra hcoeff2
  have hcoeff1 :
      MvPolynomial.coeff (d + Finsupp.single j 1)
        (MvPolynomial.pderiv i F) ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) j
      (MvPolynomial.pderiv i F) d] at hcoeff2
    intro hz
    apply hcoeff2
    simp [hz]
  have hsourceCoeff :
      MvPolynomial.coeff
        ((d + Finsupp.single j 1) + Finsupp.single i 1) F ≠ 0 := by
    rw [coeff_pderiv_mixedDegree (K := K) i F
      (d + Finsupp.single j 1)] at hcoeff1
    intro hz
    apply hcoeff1
    simp [hz]
  have hsourceSupport :
      (d + Finsupp.single j 1) + Finsupp.single i 1 ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hsourceCoeff
  have hdeg := hsupp _ hsourceSupport
  have hj := directClosingTransverseComplementDegree_add_single
    ell j hj0 hjel d
  have hi := directClosingTransverseComplementDegree_add_single
    ell i hi0 hiel (d + Finsupp.single j 1)
  rw [hi, hj] at hdeg
  omega

/-- Polynomial face exposed by a zero-order equality wall.  The face is
nonzero and has affine support in the coordinates complementary to the square
axis.  The derivative-vanishing fields are included explicitly so the next
Schur/mixed-pivot adapter does not have to redo support arithmetic. -/
inductive DirectClosingCanonicalSquareZeroOrderWallFaceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (d : Fin 4 →₀ ℕ)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (m : ℕ)
      (hm : directClosingLongitudinalTransverseDegree d = m)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (support_degree :
        ∀ e ∈ face.support,
          directClosingLongitudinalTransverseDegree e = m)
      (transverseHessian_zero :
        ∀ j k : Fin 3,
          MvPolynomial.pderiv k.succ (MvPolynomial.pderiv j.succ face) = 0)

  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (m : ℕ)
      (hm : directClosingTransverseComplementDegree D.index d = m)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = initialForm (directClosingTransverseComplementWeight D.index)
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (support_degree :
        ∀ e ∈ face.support,
          directClosingTransverseComplementDegree D.index e = m)
      (complementHessian_zero :
        ∀ i j : Fin 4,
          i ≠ (0 : Fin 4) → i ≠ D.index →
          j ≠ (0 : Fin 4) → j ≠ D.index →
          MvPolynomial.pderiv j (MvPolynomial.pderiv i face) = 0)

/-- Promote a single low-degree zero-order wall witness to the entire exact
special-fibre face carrying it. -/
theorem DirectClosingCanonicalSquareZeroOrderFamilyWallShape.toWallFaceData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (Z : DirectClosingCanonicalSquareZeroOrderFamilyWallShape C heq) :
    DirectClosingCanonicalSquareZeroOrderWallFaceData C heq := by
  cases Z with
  | longitudinal D hindex d hd hlt horder0 hdSpecial hdegree =>
      let m := directClosingLongitudinalTransverseDegree d
      let F0 := polynomialFamilySpecialFiber D.family
      let face := initialForm pureLongitudinalTransverseWeight
        (-(m : ℤ)) F0
      have hw :
          Finsupp.weight pureLongitudinalTransverseWeight d = -(m : ℤ) := by
        rw [weight_pureLongitudinalTransverseWeight]
        simp [m, pureLongitudinalTransverseDegree,
          directClosingLongitudinalTransverseDegree]
      have hface_ne : face ≠ 0 := by
        exact initialForm_ne_zero_of_support_weight
          pureLongitudinalTransverseWeight (-(m : ℤ)) F0 d hdSpecial hw
      have hsupport :
          ∀ e ∈ face.support,
            directClosingLongitudinalTransverseDegree e = m := by
        intro e he
        exact support_initialForm_pureLongitudinalTransverseDegree_eq
          F0 m (by simpa [face] using he)
      have hsupp_le :
          ∀ e ∈ face.support,
            directClosingLongitudinalTransverseDegree e ≤ 1 := by
        intro e he
        rw [hsupport e he]
        simpa [m] using hdegree
      have hhess :
          ∀ j k : Fin 3,
            MvPolynomial.pderiv k.succ (MvPolynomial.pderiv j.succ face) = 0 := by
        intro j k
        exact pderiv_pderiv_eq_zero_of_longitudinalTransverseDegree_le_one
          face hsupp_le j k
      have hm_le : m ≤ 1 := by
        simpa [m] using hdegree
      exact .longitudinal D d hdSpecial m rfl hm_le face rfl
        hface_ne hsupport hhess

  | transverse D hindex d hd hlt horder0 hdSpecial hdegree =>
      let m := directClosingTransverseComplementDegree D.index d
      let F0 := polynomialFamilySpecialFiber D.family
      let face := initialForm (directClosingTransverseComplementWeight D.index)
        (-(m : ℤ)) F0
      have hw :
          Finsupp.weight (directClosingTransverseComplementWeight D.index) d =
            -(m : ℤ) := by
        rw [weight_directClosingTransverseComplementWeight]
      have hface_ne : face ≠ 0 := by
        exact initialForm_ne_zero_of_support_weight
          (directClosingTransverseComplementWeight D.index)
          (-(m : ℤ)) F0 d hdSpecial hw
      have hsupport :
          ∀ e ∈ face.support,
            directClosingTransverseComplementDegree D.index e = m := by
        intro e he
        exact support_initialForm_transverseComplementDegree_eq
          D.index F0 m (by simpa [face] using he)
      have hsupp_le :
          ∀ e ∈ face.support,
            directClosingTransverseComplementDegree D.index e ≤ 1 := by
        intro e he
        rw [hsupport e he]
        simpa [m] using hdegree
      have hhess :
          ∀ i j : Fin 4,
            i ≠ (0 : Fin 4) → i ≠ D.index →
            j ≠ (0 : Fin 4) → j ≠ D.index →
            MvPolynomial.pderiv j (MvPolynomial.pderiv i face) = 0 := by
        intro i j hi0 hiel hj0 hjel
        exact pderiv_pderiv_eq_zero_of_transverseComplementDegree_le_one
          D.index face hsupp_le i j hi0 hiel hj0 hjel
      have hm_le : m ≤ 1 := by
        simpa [m] using hdegree
      exact .transverse D hindex d hdSpecial m rfl hm_le face rfl
        hface_ne hsupport hhess

/-- Refine the equality-wall frontier one step further: positive section walls
remain honest pointed gauge steps, while every zero-order family wall now
carries a nonzero affine special-fibre face with its complementary Hessian
block already proved zero. -/
inductive DirectClosingCanonicalSquareEqualityAffineFaceFrontier
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop
  | wallFace
      (F : DirectClosingCanonicalSquareZeroOrderWallFaceData C heq)
  | sectionGauge
      (G : DirectClosingPositiveSectionGaugeStep C)

/-- Complete refinement of the canonical equality spill into an affine face
or a positive pointed source-gauge step. -/
theorem DirectClosingCanonicalSquareEarlierWallNormalForm.toAffineFaceFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (N : DirectClosingCanonicalSquareEarlierWallNormalForm C heq) :
    DirectClosingCanonicalSquareEqualityAffineFaceFrontier C heq := by
  cases N.toReducedFrontier with
  | zeroOrderFamily Z =>
      exact .wallFace Z.toWallFaceData
  | sectionGauge G =>
      exact .sectionGauge G

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
