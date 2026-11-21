import HC4.Newton.TwoZeroDoublingHessianSquareGeneral
import HC4.Newton.TerminalTwoZeroKellerReduction
import HC4.Newton.TerminalTwoZeroGradientConjugacy
import Mathlib.Tactic

/-!
# A19.3: planar Keller maps embed into four-dimensional Hessian gradients

This file records the exact hardness seam at the final two-zero endpoint.
For planar coordinate polynomials `A,C`, define the four-variable potential

    F = X₂ * A(X₀,X₁) + X₃ * C(X₀,X₁).

The renamed coefficients depend only on `X₀,X₁`, so A19.2 applies and gives

    det Hess(F) = Jac(A,C)^2.

Moreover, on the zero fibre `(X₂,X₃)=(0,0)`, the first two gradient
coordinates vanish and the last two are exactly the planar map `(A,C)`.
Thus every collision of a planar Keller map with Jacobian one is literally a
collision of a four-dimensional determinant-one Hessian gradient.

A general nonzero constant planar Jacobian is reduced to Jacobian one by
scaling the second target coordinate.  Consequently unrestricted HC4 gradient
injectivity implies the planar JC2 injectivity interface.  This theorem is a
soundness guard for final assembly: the two-zero terminal cannot be removed by
a purely formal rank label or support wrapper.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/- The imported reflexive derivative aliases point in the opposite direction
from the definitions unfolded below.  Keeping both active makes simp cycle. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

/-- Renaming an honest planar polynomial into coordinates `0,1` introduces no
support in coordinates `2,3`. -/
theorem rename_standardZeroPair_dependsOnly
    (P : MvPolynomial (Fin 2) K) :
    DependsOnlyOnStandardZeroPair
      (MvPolynomial.rename standardZeroPairEmbedding P) := by
  intro m hm
  rcases MvPolynomial.coeff_rename_ne_zero
      standardZeroPairEmbedding P m hm with
    ⟨u, hu, _hu⟩
  constructor
  · by_contra h2
    have hm2 : (2 : Fin 4) ∈ m.support :=
      Finsupp.mem_support_iff.mpr h2
    rw [← hu] at hm2
    have himage := Finsupp.mapDomain_support hm2
    rw [Finset.mem_image] at himage
    rcases himage with ⟨i, _hi, hmap⟩
    fin_cases i <;> simp [standardZeroPairEmbedding] at hmap
  · by_contra h3
    have hm3 : (3 : Fin 4) ∈ m.support :=
      Finsupp.mem_support_iff.mpr h3
    rw [← hu] at hm3
    have himage := Finsupp.mapDomain_support hm3
    rw [Finset.mem_image] at himage
    rcases himage with ⟨i, _hi, hmap⟩
    fin_cases i <;> simp [standardZeroPairEmbedding] at hmap

/-- The renamed planar polynomial has zero derivatives in the two fibre
coordinates. -/
theorem pderiv_two_rename_standardZeroPair_eq_zero
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv 2
      (MvPolynomial.rename standardZeroPairEmbedding P) = 0 := by
  exact
    pderiv_eq_zero_of_all_supported_exponents_zero
      2 (MvPolynomial.rename standardZeroPairEmbedding P)
      (fun m hm => (rename_standardZeroPair_dependsOnly P m hm).1)

theorem pderiv_three_rename_standardZeroPair_eq_zero
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv 3
      (MvPolynomial.rename standardZeroPairEmbedding P) = 0 := by
  exact
    pderiv_eq_zero_of_all_supported_exponents_zero
      3 (MvPolynomial.rename standardZeroPairEmbedding P)
      (fun m hm => (rename_standardZeroPair_dependsOnly P m hm).2)

/-- Four-dimensional Hessian-doubling potential attached to a planar pair. -/
def planarDoublingPotential
    (A C : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.X 2 *
      MvPolynomial.rename standardZeroPairEmbedding A +
    MvPolynomial.X 3 *
      MvPolynomial.rename standardZeroPairEmbedding C

@[simp] theorem standardTwoZeroA_planarDoublingPotential
    (A C : MvPolynomial (Fin 2) K) :
    standardTwoZeroA (planarDoublingPotential A C) =
      MvPolynomial.rename standardZeroPairEmbedding A := by
  simp [standardTwoZeroA, planarDoublingPotential,
    pderiv_two_rename_standardZeroPair_eq_zero,
    pderiv_three_rename_standardZeroPair_eq_zero]

@[simp] theorem standardTwoZeroC_planarDoublingPotential
    (A C : MvPolynomial (Fin 2) K) :
    standardTwoZeroC (planarDoublingPotential A C) =
      MvPolynomial.rename standardZeroPairEmbedding C := by
  simp [standardTwoZeroC, planarDoublingPotential,
    pderiv_two_rename_standardZeroPair_eq_zero,
    pderiv_three_rename_standardZeroPair_eq_zero]

/-- The constructed potential is literally an honest two-zero doubling form. -/
theorem planarDoublingPotential_hasDoublingForm
    (A C : MvPolynomial (Fin 2) K) :
    HasStandardTwoZeroDoublingForm
      (planarDoublingPotential A C) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [standardTwoZeroA_planarDoublingPotential,
      standardTwoZeroC_planarDoublingPotential]
    rfl
  · rw [standardTwoZeroA_planarDoublingPotential]
    exact rename_standardZeroPair_dependsOnly A
  · rw [standardTwoZeroC_planarDoublingPotential]
    exact rename_standardZeroPair_dependsOnly C

/-- The ambient cross determinant of the doubling potential is exactly the
rename of the planar Jacobian determinant. -/
theorem standardTwoZeroCrossDet_planarDoublingPotential
    (A C : MvPolynomial (Fin 2) K) :
    standardTwoZeroCrossDet (planarDoublingPotential A C) =
      MvPolynomial.rename standardZeroPairEmbedding
        (HC4.planarJacobianDetPolynomial
          (standardPlanarPairMap A C)) := by
  unfold standardTwoZeroCrossDet
  rw [standardTwoZeroA_planarDoublingPotential,
    standardTwoZeroC_planarDoublingPotential]
  exact (rename_planarJacobianDet_standardPair A C).symm

/-- Exact Hessian/Jacobian square identity for the planar embedding. -/
theorem planarDoublingPotential_hessianDeterminant
    (A C : MvPolynomial (Fin 2) K) :
    HC4.Polynomial.hessianDeterminant
        (planarDoublingPotential A C) =
      (MvPolynomial.rename standardZeroPairEmbedding
        (HC4.planarJacobianDetPolynomial
          (standardPlanarPairMap A C))) ^ 2 := by
  rw [standardTwoZero_hessianDeterminant_eq_crossDet_sq_of_doublingForm
    (planarDoublingPotential_hasDoublingForm A C)]
  rw [standardTwoZeroCrossDet_planarDoublingPotential]

/-- A planar Jacobian-one pair gives a determinant-one four-dimensional
Hessian potential. -/
theorem planarDoublingPotential_hessianDeterminant_one
    (A C : MvPolynomial (Fin 2) K)
    (hJ :
      HC4.planarJacobianDetPolynomial
          (standardPlanarPairMap A C) =
        MvPolynomial.C (1 : K)) :
    HC4.Polynomial.hessianDeterminant
        (planarDoublingPotential A C) = 1 := by
  rw [planarDoublingPotential_hessianDeterminant, hJ]
  rw [MvPolynomial.rename_C]
  simp

/-- On the zero fibre, the first two gradient coordinates of the doubling
potential vanish. -/
theorem planarDoublingPotential_gradient_zeroPair_at_zeroFibre
    (A C : MvPolynomial (Fin 2) K)
    (u : HC4.Point2 K) :
    standardBasePoint
        (mvGradientMap (planarDoublingPotential A C)
          (standardJoinPoint (u, fun _ : Fin 2 => (0 : K)))) =
      (fun _ : Fin 2 => (0 : K)) := by
  funext i
  fin_cases i
  · change
      MvPolynomial.eval
          (standardJoinPoint (u, fun _ : Fin 2 => (0 : K)))
          (MvPolynomial.pderiv 0 (planarDoublingPotential A C)) = 0
    simp [planarDoublingPotential, standardJoinPoint]
  · change
      MvPolynomial.eval
          (standardJoinPoint (u, fun _ : Fin 2 => (0 : K)))
          (MvPolynomial.pderiv 1 (planarDoublingPotential A C)) = 0
    simp [planarDoublingPotential, standardJoinPoint]

/-- Every planar collision lifts to an exact gradient collision of the
four-dimensional doubling potential on the zero fibre. -/
theorem planarDoublingPotential_exactCollision_of_planarCollision
    (A C : MvPolynomial (Fin 2) K)
    {u v : HC4.Point2 K}
    (hcollision :
      HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) u =
        HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) v) :
    HasExactGradientCollision
      (planarDoublingPotential A C)
      (standardJoinPoint (u, fun _ : Fin 2 => (0 : K)))
      (standardJoinPoint (v, fun _ : Fin 2 => (0 : K))) := by
  let F := planarDoublingPotential A C
  let z : HC4.Point2 K := fun _ => 0
  let p : Fin 4 → K := standardJoinPoint (u, z)
  let q : Fin 4 → K := standardJoinPoint (v, z)
  have hA :
      MvPolynomial.rename standardZeroPairEmbedding A =
        standardTwoZeroA F := by
    simpa [F] using (standardTwoZeroA_planarDoublingPotential A C).symm
  have hC :
      MvPolynomial.rename standardZeroPairEmbedding C =
        standardTwoZeroC F := by
    simpa [F] using (standardTwoZeroC_planarDoublingPotential A C).symm
  have hzeroP :
      standardBasePoint (mvGradientMap F p) = z := by
    simpa [F, p, z] using
      planarDoublingPotential_gradient_zeroPair_at_zeroFibre A C u
  have hzeroQ :
      standardBasePoint (mvGradientMap F q) = z := by
    simpa [F, q, z] using
      planarDoublingPotential_gradient_zeroPair_at_zeroFibre A C v
  have hbaseP : standardBasePoint p = u := by
    have hs := congrArg Prod.fst (standardSplitPoint_join u z)
    simpa [standardSplitPoint, p] using hs
  have hbaseQ : standardBasePoint q = v := by
    have hs := congrArg Prod.fst (standardSplitPoint_join v z)
    simpa [standardSplitPoint, q] using hs
  have hposP :
      standardFibrePoint (mvGradientMap F p) =
        HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) u := by
    have h := standardTwoZero_gradient_positive_eq_planar hA hC p
    rw [hbaseP] at h
    exact h
  have hposQ :
      standardFibrePoint (mvGradientMap F q) =
        HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) v := by
    have h := standardTwoZero_gradient_positive_eq_planar hA hC q
    rw [hbaseQ] at h
    exact h
  have hsplit :
      standardSplitPoint (mvGradientMap F p) =
        standardSplitPoint (mvGradientMap F q) := by
    apply Prod.ext
    · exact hzeroP.trans hzeroQ.symm
    · exact hposP.trans (hcollision.trans hposQ.symm)
  have hgrad : mvGradientMap F p = mvGradientMap F q :=
    standardSplitPoint_injective hsplit
  intro i
  simpa [F, p, q, z] using congrFun hgrad i

/-- Distinct planar base points remain distinct after joining the zero fibre. -/
theorem standardJoinPoint_zeroFibre_ne_of_ne
    {u v : HC4.Point2 K}
    (huv : u ≠ v) :
    standardJoinPoint (u, fun _ : Fin 2 => (0 : K)) ≠
      standardJoinPoint (v, fun _ : Fin 2 => (0 : K)) := by
  intro h
  apply huv
  have hs := congrArg standardSplitPoint h
  rw [standardSplitPoint_join, standardSplitPoint_join] at hs
  exact congrArg Prod.fst hs

end

end HC4.Newton

namespace HC4

noncomputable section

variable {K : Type*} [Field K]

/-- Normalize a planar map with nonzero constant Jacobian `c` by multiplying
its second target coordinate by `c⁻¹`. -/
def normalizePlanarKellerMap
    (c : K) (G : PlanarPolynomialMap K) :
    PlanarPolynomialMap K
  | 0 => G 0
  | 1 => MvPolynomial.C c⁻¹ * G 1

/-- The normalized map's Jacobian is scaled by `c⁻¹`. -/
theorem planarJacobianDetPolynomial_normalizePlanarKellerMap
    (c : K) (G : PlanarPolynomialMap K) :
    planarJacobianDetPolynomial (normalizePlanarKellerMap c G) =
      MvPolynomial.C c⁻¹ * planarJacobianDetPolynomial G := by
  unfold planarJacobianDetPolynomial
  simp [normalizePlanarKellerMap]
  ring

/-- A nonzero constant-Jacobian certificate becomes literal Jacobian one. -/
theorem normalizePlanarKellerMap_jacobian_one
    {c : K} (hc : c ≠ 0)
    {G : PlanarPolynomialMap K}
    (hJ : planarJacobianDetPolynomial G = MvPolynomial.C c) :
    planarJacobianDetPolynomial (normalizePlanarKellerMap c G) =
      MvPolynomial.C (1 : K) := by
  rw [planarJacobianDetPolynomial_normalizePlanarKellerMap, hJ]
  have hcinv : c⁻¹ * c = (1 : K) := inv_mul_cancel₀ hc
  calc
    MvPolynomial.C c⁻¹ * MvPolynomial.C c =
        MvPolynomial.C (c⁻¹ * c) := by
          exact (map_mul (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) c⁻¹ c).symm
    _ = MvPolynomial.C (1 : K) := by rw [hcinv]

/-- Target scaling preserves every planar collision. -/
theorem normalizePlanarKellerMap_collision
    {c : K} {G : PlanarPolynomialMap K}
    {u v : Point2 K}
    (hcollision :
      planarPolynomialMapEval G u =
        planarPolynomialMapEval G v) :
    planarPolynomialMapEval (normalizePlanarKellerMap c G) u =
      planarPolynomialMapEval (normalizePlanarKellerMap c G) v := by
  funext i
  fin_cases i
  · exact congrFun hcollision 0
  · have h := congrFun hcollision 1
    change
      MvPolynomial.eval u (MvPolynomial.C c⁻¹ * G 1) =
        MvPolynomial.eval v (MvPolynomial.C c⁻¹ * G 1)
    simpa using congrArg (fun x : K => c⁻¹ * x) h

/-- Every `Fin 2` planar map is definitionally recovered from its two
coordinate polynomials. -/
theorem standardPlanarPairMap_components
    (G : PlanarPolynomialMap K) :
    HC4.Newton.standardPlanarPairMap (G 0) (G 1) = G := by
  funext i
  fin_cases i <;> rfl

/-- **Planar JC2 is a consequence of unrestricted HC4 gradient injectivity.**

This is the precise formal hardness theorem behind the final two-zero
terminal.  Any proof that every four-variable determinant-one Hessian gradient
is injective automatically proves the planar Jacobian conjecture injectivity
interface. -/
theorem planarJC2_of_hessianFour_gradient_injective
    (hHC4 :
      ∀ F : MvPolynomial (Fin 4) K,
        HC4.Polynomial.hessianDeterminant F = 1 →
          Function.Injective (HC4.Newton.mvGradientMap F)) :
    PlanarJC2Injectivity K := by
  intro G hKeller
  rcases hKeller with ⟨c, hc, hJ⟩
  intro u v hcollision
  by_contra huv
  let Gn : PlanarPolynomialMap K := normalizePlanarKellerMap c G
  have hJn :
      planarJacobianDetPolynomial Gn = MvPolynomial.C (1 : K) := by
    dsimp [Gn]
    exact normalizePlanarKellerMap_jacobian_one hc hJ
  have hcollisionN :
      planarPolynomialMapEval Gn u =
        planarPolynomialMapEval Gn v := by
    dsimp [Gn]
    exact normalizePlanarKellerMap_collision hcollision
  have hpair :
      HC4.Newton.standardPlanarPairMap (Gn 0) (Gn 1) = Gn :=
    standardPlanarPairMap_components Gn
  have hJpair :
      planarJacobianDetPolynomial
          (HC4.Newton.standardPlanarPairMap (Gn 0) (Gn 1)) =
        MvPolynomial.C (1 : K) := by
    rw [hpair]
    exact hJn
  have hcollisionPair :
      planarPolynomialMapEval
          (HC4.Newton.standardPlanarPairMap (Gn 0) (Gn 1)) u =
        planarPolynomialMapEval
          (HC4.Newton.standardPlanarPairMap (Gn 0) (Gn 1)) v := by
    rw [hpair]
    exact hcollisionN
  let F : MvPolynomial (Fin 4) K :=
    HC4.Newton.planarDoublingPotential (Gn 0) (Gn 1)
  have hF : HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    exact HC4.Newton.planarDoublingPotential_hessianDeterminant_one
      (Gn 0) (Gn 1) hJpair
  have hcoll4 :
      HC4.Newton.HasExactGradientCollision
        F
        (HC4.Newton.standardJoinPoint
          (u, fun _ : Fin 2 => (0 : K)))
        (HC4.Newton.standardJoinPoint
          (v, fun _ : Fin 2 => (0 : K))) := by
    dsimp [F]
    exact HC4.Newton.planarDoublingPotential_exactCollision_of_planarCollision
      (Gn 0) (Gn 1) hcollisionPair
  have hgrad4 :
      HC4.Newton.mvGradientMap F
          (HC4.Newton.standardJoinPoint
            (u, fun _ : Fin 2 => (0 : K))) =
        HC4.Newton.mvGradientMap F
          (HC4.Newton.standardJoinPoint
            (v, fun _ : Fin 2 => (0 : K))) := by
    funext i
    exact hcoll4 i
  have hpointEq := hHC4 F hF hgrad4
  exact
    HC4.Newton.standardJoinPoint_zeroFibre_ne_of_ne huv hpointEq

end

end HC4