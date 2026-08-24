import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreHesseBridge
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-!
# Exact binary planarisation of the stationary transverse wall core

The zero-jet/Hesse reductions leave a transverse canonical wall face supported
only on the coordinate plane `(0, ell)`, with `ell != 0`, and with vanishing
binary Hessian determinant in those two directions.

This file turns that support statement into an honest polynomial in
`MvPolynomial (Fin 2) K`.  The inclusion sends the two binary variables to
ambient coordinates `0` and `ell`.  Mathlib's
`MvPolynomial.exists_rename_eq_of_vars_subset_range` then gives an exact
planarisation, not merely a moral dependence on two variables.

We also transport the binary Hessian determinant through the inclusion.  Thus
the newly proved binary homogeneous Hesse machinery can be applied directly to
the surviving HC4 wall core without any further four-variable support
bookkeeping.  No JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Inclusion of the canonical transverse base plane into the four ambient
coordinates: binary coordinate `0` is the marked longitudinal axis and binary
coordinate `1` is the surviving transverse axis `ell`. -/
def transverseBaseEmbedding
    (ell : Fin 4)
    (hell : ell ≠ (0 : Fin 4)) : Fin 2 ↪ Fin 4 where
  toFun i := if i = (0 : Fin 2) then (0 : Fin 4) else ell
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hell hij.symm).elim
    · exact (hell hij).elim
    · rfl

@[simp] theorem transverseBaseEmbedding_zero
    (ell : Fin 4)
    (hell : ell ≠ (0 : Fin 4)) :
    transverseBaseEmbedding ell hell (0 : Fin 2) = (0 : Fin 4) := by
  simp [transverseBaseEmbedding]

@[simp] theorem transverseBaseEmbedding_one
    (ell : Fin 4)
    (hell : ell ≠ (0 : Fin 4)) :
    transverseBaseEmbedding ell hell (1 : Fin 2) = ell := by
  simp [transverseBaseEmbedding, hell]

/-- Support on the ambient base plane `(0,ell)` implies every variable of the
polynomial lies in the range of the corresponding binary inclusion. -/
theorem transverseBaseSupport_vars_subset_range
    {ell : Fin 4}
    {F : MvPolynomial (Fin 4) K}
    (hell : ell ≠ (0 : Fin 4))
    (hsupp : IsTransverseBaseSupport ell F) :
    (↑F.vars : Set (Fin 4)) ⊆
      Set.range (transverseBaseEmbedding ell hell) := by
  intro i hi
  change i ∈ F.vars at hi
  rw [MvPolynomial.mem_vars i] at hi
  rcases hi with ⟨m, hm, him⟩
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
  have hmcoeff : MvPolynomial.coeff m F ≠ 0 := by
    simpa [MvPolynomial.coeff] using (Finsupp.mem_support_iff.mp hm)
  have hmsupp : m ∈ F.support := by
    exact Finsupp.mem_support_iff.mpr hmcoeff
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    exact ⟨0, by simp⟩
  · by_cases hiel : i = ell
    · subst i
      exact ⟨1, by simp⟩
    · exact (hmi (hsupp m hmsupp i hi0 hiel)).elim

/-- Every transverse base-plane polynomial is the exact rename of an honest
binary polynomial. -/
theorem transverseBaseSupport_exists_binaryPlanarisation
    {ell : Fin 4}
    {F : MvPolynomial (Fin 4) K}
    (hell : ell ≠ (0 : Fin 4))
    (hsupp : IsTransverseBaseSupport ell F) :
    ∃ Q : MvPolynomial (Fin 2) K,
      MvPolynomial.rename (transverseBaseEmbedding ell hell) Q = F := by
  exact MvPolynomial.exists_rename_eq_of_vars_subset_range
    F
    (transverseBaseEmbedding ell hell)
    (transverseBaseEmbedding ell hell).injective
    (transverseBaseSupport_vars_subset_range hell hsupp)

/-- First partial derivatives commute with the transverse base embedding. -/
theorem pderiv_rename_transverseBaseEmbedding
    (ell : Fin 4)
    (hell : ell ≠ (0 : Fin 4))
    (i : Fin 2)
    (Q : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv (transverseBaseEmbedding ell hell i)
        (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
      MvPolynomial.rename (transverseBaseEmbedding ell hell)
        (MvPolynomial.pderiv i Q) := by
  simpa using
    (MvPolynomial.pderiv_rename
      (transverseBaseEmbedding ell hell).injective i Q)

/-- The binary Hessian determinant is transported exactly by the base-plane
inclusion. -/
theorem binaryDirectionalHessianDet_rename_transverseBaseEmbedding
    (ell : Fin 4)
    (hell : ell ≠ (0 : Fin 4))
    (Q : MvPolynomial (Fin 2) K) :
    binaryDirectionalHessianDet (0 : Fin 4) ell
        (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
      MvPolynomial.rename (transverseBaseEmbedding ell hell)
        (binaryDirectionalHessianDet (0 : Fin 2) 1 Q) := by
  have h00first :
      MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (MvPolynomial.pderiv (0 : Fin 2) Q) := by
    simpa using
      (pderiv_rename_transverseBaseEmbedding ell hell (0 : Fin 2) Q)
  have h00second :
      MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.rename (transverseBaseEmbedding ell hell)
            (MvPolynomial.pderiv (0 : Fin 2) Q)) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (MvPolynomial.pderiv (0 : Fin 2)
            (MvPolynomial.pderiv (0 : Fin 2) Q)) := by
    simpa using
      (pderiv_rename_transverseBaseEmbedding ell hell (0 : Fin 2)
        (MvPolynomial.pderiv (0 : Fin 2) Q))
  have h00 :
      directionalSecondDerivative (0 : Fin 4)
          (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (directionalSecondDerivative (0 : Fin 2) Q) := by
    unfold directionalSecondDerivative
    rw [h00first, h00second]
  have h11first :
      MvPolynomial.pderiv ell
          (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (MvPolynomial.pderiv (1 : Fin 2) Q) := by
    simpa using
      (pderiv_rename_transverseBaseEmbedding ell hell (1 : Fin 2) Q)
  have h11second :
      MvPolynomial.pderiv ell
          (MvPolynomial.rename (transverseBaseEmbedding ell hell)
            (MvPolynomial.pderiv (1 : Fin 2) Q)) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (MvPolynomial.pderiv (1 : Fin 2)
            (MvPolynomial.pderiv (1 : Fin 2) Q)) := by
    simpa using
      (pderiv_rename_transverseBaseEmbedding ell hell (1 : Fin 2)
        (MvPolynomial.pderiv (1 : Fin 2) Q))
  have h11 :
      directionalSecondDerivative ell
          (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (directionalSecondDerivative (1 : Fin 2) Q) := by
    unfold directionalSecondDerivative
    rw [h11first, h11second]
  have h01second :
      MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.rename (transverseBaseEmbedding ell hell)
            (MvPolynomial.pderiv (1 : Fin 2) Q)) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (MvPolynomial.pderiv (0 : Fin 2)
            (MvPolynomial.pderiv (1 : Fin 2) Q)) := by
    simpa using
      (pderiv_rename_transverseBaseEmbedding ell hell (0 : Fin 2)
        (MvPolynomial.pderiv (1 : Fin 2) Q))
  have h01 :
      directionalMixedDerivative (0 : Fin 4) ell
          (MvPolynomial.rename (transverseBaseEmbedding ell hell) Q) =
        MvPolynomial.rename (transverseBaseEmbedding ell hell)
          (directionalMixedDerivative (0 : Fin 2) 1 Q) := by
    unfold directionalMixedDerivative
    rw [h11first, h01second]
  unfold binaryDirectionalHessianDet
  rw [h00, h11, h01]
  simp

/-- Exact binary data carried by a surviving transverse stationary wall core. -/
structure DirectClosingCanonicalSquareBinaryStationaryCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) where
  D : DirectClosingAlignedSquareSourceData C
  hindex : D.index ≠ (0 : Fin 4)
  face : MvPolynomial (Fin 4) K
  binaryFace : MvPolynomial (Fin 2) K
  face_eq_rename :
    MvPolynomial.rename (transverseBaseEmbedding D.index hindex) binaryFace = face
  face_ne_zero : face ≠ 0
  binaryFace_ne_zero : binaryFace ≠ 0
  binary_det_zero :
    binaryDirectionalHessianDet (0 : Fin 2) 1 binaryFace = 0
  source_collision :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber D.family)
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  face_linear_zero :
    ∀ i : Fin 4,
      MvPolynomial.coeff (Finsupp.single i 1) face = 0

/-- Binary-normal-form frontier for the marked stationary wall core.  The
longitudinal branch is already one-dimensional.  The transverse branch carries
an exact honest binary polynomial, so all subsequent Hesse/direction-locking
arguments can be performed in `Fin 2`. -/
inductive DirectClosingCanonicalSquareBinaryStationaryCoreFrontier
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
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
      (data : DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)

/-- Exact binary planarisation of every transverse marked stationary core.
The longitudinal core is retained unchanged as the already one-dimensional
branch. -/
theorem DirectClosingCanonicalSquareMarkedStationaryPlanarCoreData.toBinaryStationaryCoreFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareMarkedStationaryPlanarCoreData C heq) :
    DirectClosingCanonicalSquareBinaryStationaryCoreFrontier C heq := by
  cases L with
  | longitudinal D face face_eq face_ne_zero base_support source_collision face_linear_zero =>
      exact .longitudinal D face face_ne_zero base_support source_collision face_linear_zero
  | transverse D hindex face face_eq face_ne_zero base_support base_det_zero source_collision face_linear_zero =>
      rcases transverseBaseSupport_exists_binaryPlanarisation hindex base_support with
        ⟨Q, hQrename⟩
      have hQne : Q ≠ 0 := by
        intro hQ
        apply face_ne_zero
        rw [← hQrename, hQ]
        simp
      have hdetTransport :=
        binaryDirectionalHessianDet_rename_transverseBaseEmbedding
          D.index hindex Q
      have hrenameDet :
          MvPolynomial.rename (transverseBaseEmbedding D.index hindex)
              (binaryDirectionalHessianDet (0 : Fin 2) 1 Q) = 0 := by
        rw [← hdetTransport, hQrename, base_det_zero]
      have hdetQ :
          binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0 := by
        apply MvPolynomial.rename_injective
          (transverseBaseEmbedding D.index hindex)
          (transverseBaseEmbedding D.index hindex).injective
        simpa using hrenameDet
      exact .transverse {
        D := D
        hindex := hindex
        face := face
        binaryFace := Q
        face_eq_rename := hQrename
        face_ne_zero := face_ne_zero
        binaryFace_ne_zero := hQne
        binary_det_zero := hdetQ
        source_collision := source_collision
        face_linear_zero := face_linear_zero
      }

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
