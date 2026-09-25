import HC4.Valuation.AdaptiveAlignedSmithMarkedAxisTerminal
import HC4.Newton.TerminalAssociatedGradedEndpoint
import HC4.PlanarJC2HessianEmbedding
import Mathlib.Tactic

/-!
# Planar Keller collisions lift to certified two-zero terminal collisions

The final-resolution interface accepts an honest
`TerminalAssociatedGradedCollisionData`.  An explicit planar Keller collision
already contains enough information to build one canonically.

First normalise the nonzero constant planar Jacobian to one by scaling the
second target coordinate.  Then form the standard four-variable Hessian
doubling potential

    X₂ A(X₀,X₁) + X₃ C(X₀,X₁).

The planar collision lifts to a distinct exact gradient collision on the zero
fibre.  Every monomial of this potential has exactly one of the positive
weight variables `X₂,X₃`, so the potential is weighted homogeneous of degree
one for the standard two-zero weight `(0,0,1,1)`.  Its Hessian determinant is
one by the existing Hessian/Jacobian-square identity.

Thus every explicit planar Keller collision yields the already-certified
standard two-zero direct-jump endpoint.  No JC2 hypothesis is used.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A polynomial depending only on the standard zero-weight pair is weighted
homogeneous of degree zero for the standard two-zero weight of degree one. -/
theorem dependsOnlyOnStandardZeroPair_isWeightedHomogeneous_zero
    (P : MvPolynomial (Fin 4) K)
    (hP : DependsOnlyOnStandardZeroPair P) :
    MvPolynomial.IsWeightedHomogeneous
      (standardTwoZeroTerminalWeight (1 : ℤ)) P 0 := by
  intro m hm
  rcases hP m hm with ⟨hm2, hm3⟩
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [standardTwoZeroTerminalWeight, Fin.sum_univ_four, hm2, hm3]
  · intro i
    simp

/-- The Hessian doubling of arbitrary planar coordinate polynomials is
weighted homogeneous of degree one for `(0,0,1,1)`. -/
theorem planarDoublingPotential_twoZero_homogeneous
    (A C : MvPolynomial (Fin 2) K) :
    IsIntegralWeightedHomogeneous
      (standardTwoZeroTerminalWeight (1 : ℤ))
      (1 : ℤ)
      (planarDoublingPotential A C) := by
  let w : Fin 4 → ℤ := standardTwoZeroTerminalWeight (1 : ℤ)
  have hA0 :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.rename standardZeroPairEmbedding A) 0 := by
    exact
      dependsOnlyOnStandardZeroPair_isWeightedHomogeneous_zero
        (MvPolynomial.rename standardZeroPairEmbedding A)
        (rename_standardZeroPair_dependsOnly A)
  have hC0 :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.rename standardZeroPairEmbedding C) 0 := by
    exact
      dependsOnlyOnStandardZeroPair_isWeightedHomogeneous_zero
        (MvPolynomial.rename standardZeroPairEmbedding C)
        (rename_standardZeroPair_dependsOnly C)
  have hX2 :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) K) 1 := by
    simpa [w, standardTwoZeroTerminalWeight] using
      (MvPolynomial.isWeightedHomogeneous_X K w (2 : Fin 4))
  have hX3 :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) K) 1 := by
    simpa [w, standardTwoZeroTerminalWeight] using
      (MvPolynomial.isWeightedHomogeneous_X K w (3 : Fin 4))
  have hleft :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.X (2 : Fin 4) *
          MvPolynomial.rename standardZeroPairEmbedding A) 1 := by
    simpa using hX2.mul hA0
  have hright :
      MvPolynomial.IsWeightedHomogeneous w
        (MvPolynomial.X (3 : Fin 4) *
          MvPolynomial.rename standardZeroPairEmbedding C) 1 := by
    simpa using hX3.mul hC0
  apply mathlibWeightedHomogeneous_to_integral
  simpa [planarDoublingPotential, w] using hleft.add hright

end

end HC4.Newton

namespace HC4.Newton

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace PlanarKellerCollisionData

/-- **Planar collision -> permitted final associated-graded collision.**

The target is an honest standard two-zero Hessian potential obtained from the
normalised planar Keller map.  The theorem is proposition-valued, so the
existential Keller scalar may be eliminated directly without crossing Lean's
Prop-to-Type restriction. -/
theorem exists_terminalAssociatedGradedCollisionData
    (T : PlanarKellerCollisionData K) :
    Nonempty (TerminalAssociatedGradedCollisionData K) := by
  rcases T.keller with ⟨c, hc, hJ⟩
  let G : HC4.PlanarPolynomialMap K :=
    HC4.normalizePlanarKellerMap c T.map
  let A : MvPolynomial (Fin 2) K := G 0
  let C : MvPolynomial (Fin 2) K := G 1
  let F : MvPolynomial (Fin 4) K :=
    planarDoublingPotential A C
  let p : Fin 4 → K :=
    standardJoinPoint
      (T.leftPoint, fun _ : Fin 2 => (0 : K))
  let q : Fin 4 → K :=
    standardJoinPoint
      (T.rightPoint, fun _ : Fin 2 => (0 : K))

  have hJG :
      HC4.planarJacobianDetPolynomial G =
        MvPolynomial.C (1 : K) := by
    dsimp [G]
    exact HC4.normalizePlanarKellerMap_jacobian_one hc hJ

  have hpair :
      standardPlanarPairMap A C = G := by
    dsimp [A, C]
    exact HC4.standardPlanarPairMap_components G

  have hcollisionG :
      HC4.planarPolynomialMapEval G T.leftPoint =
        HC4.planarPolynomialMapEval G T.rightPoint := by
    dsimp [G]
    exact HC4.normalizePlanarKellerMap_collision T.collision

  have hcollisionPair :
      HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) T.leftPoint =
        HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C) T.rightPoint := by
    rw [hpair]
    exact hcollisionG

  have hcoll :
      HasExactGradientCollision F p q := by
    dsimp [F, p, q]
    exact
      planarDoublingPotential_exactCollision_of_planarCollision
        A C hcollisionPair

  have hpq : p ≠ q := by
    dsimp [p, q]
    exact standardJoinPoint_zeroFibre_ne_of_ne T.distinct

  have hdet :
      HC4.Polynomial.hessianDeterminant F = 1 := by
    dsimp [F]
    apply planarDoublingPotential_hessianDeterminant_one A C
    rw [hpair]
    exact hJG

  have hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight (1 : ℤ))
        (1 : ℤ) F := by
    dsimp [F]
    exact planarDoublingPotential_twoZero_homogeneous A C

  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := by
    unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
    exact hdet

  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight (1 : ℤ))
        (1 : ℤ)
        (MvPolynomial.rename (Equiv.refl (Fin 4)) F) := by
    simpa using hhom

  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename (Equiv.refl (Fin 4)) F) := by
    simpa using hMA

  have hendpoint :
      CertifiedTerminalEndpoint
        (MvPolynomial.rename (Equiv.refl (Fin 4)) F) :=
    .twoZero (1 : ℤ) (by norm_num) hhomRenamed hMARenamed

  exact ⟨{
    fibre := F
    leftPoint := p
    rightPoint := q
    distinct := hpq
    exactCollision := hcoll
    endpoint := .permuted (Equiv.refl (Fin 4)) hendpoint
  }⟩

/-- Type-valued form used by final-resolution constructors. -/
noncomputable def toTerminalAssociatedGradedCollisionData
    (T : PlanarKellerCollisionData K) :
    TerminalAssociatedGradedCollisionData K :=
  Classical.choice T.exists_terminalAssociatedGradedCollisionData

end PlanarKellerCollisionData

/-- Proposition-level planar Keller collision witnesses also lift directly to
a permitted terminal associated-graded collision.  Keeping the target under
`Nonempty` makes the existential elimination sound and avoids choosing a
planar witness in `Type`. -/
theorem HC4.HasPlanarKellerCollision.exists_terminalAssociatedGradedCollisionData
    (h : HC4.HasPlanarKellerCollision K) :
    Nonempty (TerminalAssociatedGradedCollisionData K) := by
  rcases h with ⟨G, hKeller, u, v, huv, hcoll⟩
  let P : PlanarKellerCollisionData K := {
    map := G
    leftPoint := u
    rightPoint := v
    distinct := huv
    keller := hKeller
    collision := hcoll
  }
  exact P.exists_terminalAssociatedGradedCollisionData

end

end HC4.Newton
