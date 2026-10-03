import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticMultiplicity
import Mathlib.Tactic

/-!
# G20: midpoint normalization of the quartic final seam

If the final seam has ordinary degree at most four, G17--G19 show that its
maximal degree is exactly four. The represented source carries the exact
collision 0 ~ e0 and has Hessian determinant one.

For the low-degree endgame it is more natural to recenter at the midpoint.
This file develops the small field-valued longitudinal translation API needed
for that step and translates by one half in coordinate 0. The collision then
becomes the antipodal pair minus-half e0 ~ plus-half e0, while the Hessian
determinant remains exactly one.

No low-dimensional Jacobian/Hessian theorem is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

noncomputable def longitudinalScalarShiftHom
    (c : K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases
      (MvPolynomial.X (0 : Fin 4) + MvPolynomial.C c)
      (fun j : Fin 3 => MvPolynomial.X j.succ))

@[simp] theorem longitudinalScalarShiftHom_C
    (c a : K) :
    longitudinalScalarShiftHom (K := K) c (MvPolynomial.C a) =
      MvPolynomial.C a := by
  simp [longitudinalScalarShiftHom]

@[simp] theorem longitudinalScalarShiftHom_X_zero
    (c : K) :
    longitudinalScalarShiftHom (K := K) c
        (MvPolynomial.X (0 : Fin 4)) =
      MvPolynomial.X 0 + MvPolynomial.C c := by
  simp [longitudinalScalarShiftHom]

@[simp] theorem longitudinalScalarShiftHom_X_succ
    (c : K) (j : Fin 3) :
    longitudinalScalarShiftHom (K := K) c
        (MvPolynomial.X j.succ) =
      MvPolynomial.X j.succ := by
  simp [longitudinalScalarShiftHom]

def longitudinalScalarShiftPoint
    (c : K)
    (p : Fin 4 → K) :
    Fin 4 → K :=
  Fin.cases (p 0 + c) (fun j : Fin 3 => p j.succ)

theorem eval_longitudinalScalarShiftHom
    (c : K)
    (p : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval p
        (longitudinalScalarShiftHom (K := K) c F) =
      MvPolynomial.eval (longitudinalScalarShiftPoint c p) F := by
  change
    MvPolynomial.eval p
        (MvPolynomial.eval₂
          MvPolynomial.C
          (Fin.cases
            (MvPolynomial.X (0 : Fin 4) + MvPolynomial.C c)
            (fun j : Fin 3 => MvPolynomial.X j.succ))
          F) =
      MvPolynomial.eval (longitudinalScalarShiftPoint c p) F
  rw [← MvPolynomial.eval_assoc
    (Fin.cases
      (MvPolynomial.X (0 : Fin 4) + MvPolynomial.C c)
      (fun j : Fin 3 => MvPolynomial.X j.succ))
    p F]
  apply congrArg (fun q => MvPolynomial.eval q F)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [longitudinalScalarShiftPoint]
  · simp [longitudinalScalarShiftPoint]

theorem pderiv_longitudinalScalarShiftHom
    (c : K)
    (i : Fin 4)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv i
        (longitudinalScalarShiftHom (K := K) c F) =
      longitudinalScalarShiftHom (K := K) c
        (MvPolynomial.pderiv i F) := by
  apply MvPolynomial.induction_on F
  · intro a
    simp
  · intro P Q hP hQ
    simp [hP, hQ]
  · intro P n hP
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    by_cases hni : n = i
    · subst n
      fin_cases i <;> simp [longitudinalScalarShiftHom]
    · fin_cases n <;> fin_cases i <;>
        simp_all [longitudinalScalarShiftHom]

theorem hessian_longitudinalScalarShiftHom_entry
    (c : K)
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (longitudinalScalarShiftHom (K := K) c F) i j =
      longitudinalScalarShiftHom (K := K) c
        (HC4.Polynomial.hessian F i j) := by
  rw [HC4.Polynomial.hessian_apply]
  rw [pderiv_longitudinalScalarShiftHom]
  rw [pderiv_longitudinalScalarShiftHom]
  rw [HC4.Polynomial.hessian_apply]

theorem hessian_longitudinalScalarShiftHom
    (c : K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian
        (longitudinalScalarShiftHom (K := K) c F) =
      (longitudinalScalarShiftHom (K := K) c).mapMatrix
        (HC4.Polynomial.hessian F) := by
  ext i j
  exact hessian_longitudinalScalarShiftHom_entry c F i j

theorem hessianDeterminant_longitudinalScalarShiftHom
    (c : K)
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant
        (longitudinalScalarShiftHom (K := K) c F) =
      longitudinalScalarShiftHom (K := K) c
        (HC4.Polynomial.hessianDeterminant F) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_longitudinalScalarShiftHom]
  exact
    (RingHom.map_det
      (longitudinalScalarShiftHom (K := K) c)
      (HC4.Polynomial.hessian F)).symm

theorem HasExactGradientCollision.longitudinalScalarShift
    {F : MvPolynomial (Fin 4) K}
    {p q p' q' : Fin 4 → K}
    (c : K)
    (hcoll : HasExactGradientCollision F p q)
    (hp : longitudinalScalarShiftPoint c p' = p)
    (hq : longitudinalScalarShiftPoint c q' = q) :
    HasExactGradientCollision
      (longitudinalScalarShiftHom (K := K) c F) p' q' := by
  intro i
  unfold mvGradientComponentAt
  rw [pderiv_longitudinalScalarShiftHom,
    eval_longitudinalScalarShiftHom,
    eval_longitudinalScalarShiftHom,
    hp, hq]
  exact hcoll i

noncomputable def finalSeamHalf : K := (1 : K) / 2

noncomputable def finalSeamMidpointLeft : Fin 4 → K :=
  Fin.cases (- finalSeamHalf (K := K)) (fun _ : Fin 3 => 0)

noncomputable def finalSeamMidpointRight : Fin 4 → K :=
  Fin.cases (finalSeamHalf (K := K)) (fun _ : Fin 3 => 0)

theorem finalSeamMidpointLeft_shift_eq_zero :
    longitudinalScalarShiftPoint
        (finalSeamHalf (K := K))
        (finalSeamMidpointLeft (K := K)) =
      (fun _ : Fin 4 => (0 : K)) := by
  funext i
  fin_cases i <;>
    simp [longitudinalScalarShiftPoint, finalSeamMidpointLeft,
      finalSeamHalf]

theorem finalSeamMidpointRight_shift_eq_axis :
    longitudinalScalarShiftPoint
        (finalSeamHalf (K := K))
        (finalSeamMidpointRight (K := K)) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  fin_cases i <;>
    simp [longitudinalScalarShiftPoint, finalSeamMidpointRight,
      finalSeamHalf, coordinateAxisPoint] <;>
    field_simp

theorem finalSeamMidpoint_points_distinct :
    finalSeamMidpointLeft (K := K) ≠
      finalSeamMidpointRight (K := K) := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  have htwo : (2 : K) ≠ 0 := by norm_num
  simp [finalSeamMidpointLeft, finalSeamMidpointRight,
    finalSeamHalf] at h0
  field_simp [htwo] at h0

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

noncomputable def finalSeamMidpointFibre
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    MvPolynomial (Fin 4) K :=
  longitudinalScalarShiftHom
    (K := K) (finalSeamHalf (K := K)) T.representedSpecialFiber

theorem finalSeamMidpointFibre_hessianDeterminant_eq_one
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Polynomial.hessianDeterminant T.finalSeamMidpointFibre = 1 := by
  rw [finalSeamMidpointFibre,
    hessianDeterminant_longitudinalScalarShiftHom,
    T.finalSeamData.representedHessianDetOne]
  simp

theorem finalSeamMidpointFibre_exactCollision
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasExactGradientCollision
      T.finalSeamMidpointFibre
      (finalSeamMidpointLeft (K := K))
      (finalSeamMidpointRight (K := K)) := by
  apply HasExactGradientCollision.longitudinalScalarShift
    (c := finalSeamHalf (K := K))
    T.finalSeamData.exactCollision
  · exact finalSeamMidpointLeft_shift_eq_zero (K := K)
  · exact finalSeamMidpointRight_shift_eq_axis (K := K)

structure FinalSeamQuarticMidpointData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  topDegree_eq_four : T.topFace.degree = 4
  fibre : MvPolynomial (Fin 4) K
  fibre_eq : fibre = T.finalSeamMidpointFibre
  hessianDet_one :
    HC4.Polynomial.hessianDeterminant fibre = 1
  leftPoint : Fin 4 → K
  rightPoint : Fin 4 → K
  left_eq : leftPoint = finalSeamMidpointLeft (K := K)
  right_eq : rightPoint = finalSeamMidpointRight (K := K)
  distinct : leftPoint ≠ rightPoint
  antipodal :
    ∀ i : Fin 4, leftPoint i = - rightPoint i
  exactCollision :
    HasExactGradientCollision fibre leftPoint rightPoint

theorem finalSeamQuarticMidpointData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    Nonempty T.FinalSeamQuarticMidpointData := by
  have hD4 := T.finalSeam_degree_eq_four_of_le_four hdeg
  refine ⟨{
    topDegree_eq_four := hD4
    fibre := T.finalSeamMidpointFibre
    fibre_eq := rfl
    hessianDet_one := T.finalSeamMidpointFibre_hessianDeterminant_eq_one
    leftPoint := finalSeamMidpointLeft (K := K)
    rightPoint := finalSeamMidpointRight (K := K)
    left_eq := rfl
    right_eq := rfl
    distinct := finalSeamMidpoint_points_distinct (K := K)
    antipodal := ?_
    exactCollision := T.finalSeamMidpointFibre_exactCollision
  }⟩
  intro i
  fin_cases i <;>
    simp [finalSeamMidpointLeft, finalSeamMidpointRight]

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
