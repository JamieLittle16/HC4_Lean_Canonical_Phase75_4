import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticMidpoint
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# G21: exact homogeneous core of the midpoint-normalized quartic seam

G20 places the quartic final seam at the antipodal collision pair while
preserving Hessian determinant one.  This file now forgets all Smith geometry
and performs only ordinary-degree bookkeeping.

Affine translation cannot increase ordinary source degree.  Since the original
represented source has maximal ordinary degree four, the midpoint fibre also
has no monomial above degree four.  It therefore decomposes exactly into its
ordinary homogeneous components of degrees zero through four.

The degree-zero and degree-one components have zero Hessian.  Consequently the
nonlinear core

    q2 + h3 + h4

has exactly the same Hessian as the full midpoint fibre and hence still has
Hessian determinant one.

No low-dimensional Hessian/Jacobian theorem, terminal cocharacter, or JC2
input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-! ## Affine substitutions preserve an ordinary support ceiling -/

/-- If every input source exponent has ordinary degree at most m and a source
substitution sends each source monomial to total degree no larger than its
original degree, then every output source exponent still has degree at most m.
-/
theorem support_degree_le_of_map_monomial_totalDegree_le
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) S)
    (P : MvPolynomial (Fin 4) R)
    (m : ℕ)
    (hP :
      ∀ n ∈ P.support,
        HC4.Polynomial.ordinaryDegree4 n ≤ m)
    (hmono :
      ∀ (n : Fin 4 →₀ ℕ) (c : R),
        (φ (MvPolynomial.monomial n c)).totalDegree ≤
          HC4.Polynomial.ordinaryDegree4 n) :
    ∀ d ∈ (φ P).support,
      HC4.Polynomial.ordinaryDegree4 d ≤ m := by
  classical
  intro d hd
  have hsum :
      φ P =
        ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
    calc
      φ P = φ (∑ n ∈ P.support,
          MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            exact congrArg φ (MvPolynomial.as_sum P)
      _ = ∑ n ∈ P.support,
          φ (MvPolynomial.monomial n (MvPolynomial.coeff n P)) := by
            simp only [map_sum]
  have hdSum :
      d ∈ (∑ n ∈ P.support,
        φ (MvPolynomial.monomial n (MvPolynomial.coeff n P))).support := by
    rwa [← hsum]
  have hdUnion :
      d ∈ P.support.biUnion
        (fun n =>
          (φ (MvPolynomial.monomial n
            (MvPolynomial.coeff n P))).support) :=
    MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨n, hnP, hdn⟩
  have hdleTotal :
      HC4.Polynomial.ordinaryDegree4 d ≤
        (φ (MvPolynomial.monomial n
          (MvPolynomial.coeff n P))).totalDegree := by
    rw [← finsuppSum_eq_ordinaryDegree4]
    exact MvPolynomial.le_totalDegree hdn
  exact
    (hdleTotal.trans (hmono n (MvPolynomial.coeff n P))).trans
      (hP n hnP)

/-- Longitudinal scalar translation cannot increase ordinary source degree. -/
theorem longitudinalScalarShiftHom_support_degree_le
    (c : K)
    (F : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hF :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ m) :
    ∀ d ∈ (longitudinalScalarShiftHom (K := K) c F).support,
      HC4.Polynomial.ordinaryDegree4 d ≤ m := by
  apply support_degree_le_of_map_monomial_totalDegree_le
    (longitudinalScalarShiftHom (K := K) c) F m hF
  intro n a
  unfold longitudinalScalarShiftHom
  apply totalDegree_eval₂Hom_monomial_le_ordinaryDegree4
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  · simp

/-! ## Finite ordinary-degree decomposition -/

/-- Ordinary initial forms of negative degree vanish because all four ordinary
weights are positive. -/
theorem fourOrdinaryInitialForm_eq_zero_of_neg
    (F : MvPolynomial (Fin 4) K)
    (r : ℤ)
    (hr : r < 0) :
    HC4.Polynomial.initialForm fourOrdinaryIntegerWeight r F = 0 := by
  ext d
  rw [HC4.Polynomial.coeff_initialForm]
  split
  · rename_i hw
    rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4] at hw
    have hnonneg :
        (0 : ℤ) ≤ (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
      positivity
    exfalso
    omega
  · rfl

/-- A polynomial supported in ordinary degrees at most four is exactly the sum
of its five ordinary homogeneous components. -/
theorem eq_sum_fourOrdinaryDegreeComponents_of_degree_le_four
    (F : MvPolynomial (Fin 4) K)
    (hF :
      ∀ d ∈ F.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ 4) :
    F =
      fourOrdinaryDegreeComponent F 0 +
      fourOrdinaryDegreeComponent F 1 +
      fourOrdinaryDegreeComponent F 2 +
      fourOrdinaryDegreeComponent F 3 +
      fourOrdinaryDegreeComponent F 4 := by
  ext d
  by_cases hd0 : MvPolynomial.coeff d F = 0
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm, hd0]
  have hdmem : d ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hd0
  have hdeg := hF d hdmem
  have hcases :
      HC4.Polynomial.ordinaryDegree4 d = 0 ∨
      HC4.Polynomial.ordinaryDegree4 d = 1 ∨
      HC4.Polynomial.ordinaryDegree4 d = 2 ∨
      HC4.Polynomial.ordinaryDegree4 d = 3 ∨
      HC4.Polynomial.ordinaryDegree4 d = 4 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4, h0]
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4, h1]
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4, h2]
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4, h3]
  · simp [fourOrdinaryDegreeComponent,
      HC4.Polynomial.coeff_initialForm,
      fourOrdinaryIntegerWeight_eq_ordinaryDegree4, h4]

/-- Degree-zero and degree-one ordinary homogeneous components have zero
Hessian. -/
theorem hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hD : D ≤ 1) :
    HC4.Polynomial.hessian (fourOrdinaryDegreeComponent F D) = 0 := by
  ext i j
  have h :=
    HC4.Polynomial.hessian_initialForm_entry
      fourOrdinaryIntegerWeight (D : ℤ) F i j
  have hneg :
      (D : ℤ) -
          fourOrdinaryIntegerWeight i -
          fourOrdinaryIntegerWeight j < 0 := by
    simp [fourOrdinaryIntegerWeight]
    omega
  have hz :=
    fourOrdinaryInitialForm_eq_zero_of_neg
      (HC4.Polynomial.hessian F i j)
      ((D : ℤ) -
        fourOrdinaryIntegerWeight i -
        fourOrdinaryIntegerWeight j)
      hneg
  rw [hz] at h
  simpa [fourOrdinaryDegreeComponent] using h

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- Exact degree-D homogeneous component of the midpoint-normalized final seam.
-/
noncomputable def finalSeamMidpointComponent
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : ℕ) :
    MvPolynomial (Fin 4) K :=
  fourOrdinaryDegreeComponent T.finalSeamMidpointFibre D

/-- Affine part of the midpoint-normalized quartic fibre. -/
noncomputable def finalSeamMidpointAffinePart
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    MvPolynomial (Fin 4) K :=
  T.finalSeamMidpointComponent 0 + T.finalSeamMidpointComponent 1

/-- Nonlinear cubic-quartic core, retaining the quadratic component. -/
noncomputable def finalSeamMidpointQuarticCore
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    MvPolynomial (Fin 4) K :=
  T.finalSeamMidpointComponent 2 +
    T.finalSeamMidpointComponent 3 +
    T.finalSeamMidpointComponent 4

/-- Under the quartic upper bound, every midpoint-fibre monomial still has
ordinary degree at most four. -/
theorem finalSeamMidpointFibre_degree_le_four
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    ∀ d ∈ T.finalSeamMidpointFibre.support,
      HC4.Polynomial.ordinaryDegree4 d ≤ 4 := by
  have hD4 := T.finalSeam_degree_eq_four_of_le_four hdeg
  apply longitudinalScalarShiftHom_support_degree_le
    (K := K) (finalSeamHalf (K := K))
    T.representedSpecialFiber 4
  intro d hd
  have hmax := T.topFace.maximal d hd
  simpa [hD4] using hmax

/-- Exact affine-plus-nonlinear decomposition of the midpoint fibre. -/
theorem finalSeamMidpointFibre_eq_affine_add_quarticCore
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    T.finalSeamMidpointFibre =
      T.finalSeamMidpointAffinePart +
        T.finalSeamMidpointQuarticCore := by
  have hsum :=
    eq_sum_fourOrdinaryDegreeComponents_of_degree_le_four
      T.finalSeamMidpointFibre
      (T.finalSeamMidpointFibre_degree_le_four hdeg)
  simpa [finalSeamMidpointAffinePart,
    finalSeamMidpointQuarticCore,
    finalSeamMidpointComponent, add_assoc] using hsum

/-- The affine part contributes no Hessian. -/
theorem finalSeamMidpointAffinePart_hessian_eq_zero
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Polynomial.hessian T.finalSeamMidpointAffinePart = 0 := by
  have h0 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.finalSeamMidpointFibre 0 (by omega)
  have h1 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.finalSeamMidpointFibre 1 (by omega)
  ext i j
  have h0ij := congrArg (fun M => M i j) h0
  have h1ij := congrArg (fun M => M i j) h1
  simpa [finalSeamMidpointAffinePart,
    finalSeamMidpointComponent,
    HC4.Polynomial.hessian_apply] using
      add_eq_zero_iff_eq_neg.mpr (by simp [h0ij, h1ij])

/-- The nonlinear quartic core has exactly the same Hessian as the full
midpoint fibre. -/
theorem finalSeamMidpointQuarticCore_hessian_eq_fibre
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    HC4.Polynomial.hessian T.finalSeamMidpointQuarticCore =
      HC4.Polynomial.hessian T.finalSeamMidpointFibre := by
  have hdecomp :=
    T.finalSeamMidpointFibre_eq_affine_add_quarticCore hdeg
  have haff := T.finalSeamMidpointAffinePart_hessian_eq_zero
  ext i j
  have h :=
    congrArg
      (fun P : MvPolynomial (Fin 4) K =>
        HC4.Polynomial.hessian P i j)
      hdecomp
  have ha := congrArg (fun M => M i j) haff
  simp only [HC4.Polynomial.hessian_apply, map_add] at h
  simpa using (show
    HC4.Polynomial.hessian T.finalSeamMidpointQuarticCore i j =
      HC4.Polynomial.hessian T.finalSeamMidpointFibre i j by
        linear_combination h)

/-- The nonlinear homogeneous core remains determinant one. -/
theorem finalSeamMidpointQuarticCore_hessianDeterminant_eq_one
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    HC4.Polynomial.hessianDeterminant
      T.finalSeamMidpointQuarticCore = 1 := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [T.finalSeamMidpointQuarticCore_hessian_eq_fibre hdeg]
  exact T.finalSeamMidpointFibre_hessianDeterminant_eq_one

/-- G21 cubic-quartic homogeneous core packet. -/
structure FinalSeamQuarticHomogeneousCoreData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  topDegree_eq_four : T.topFace.degree = 4
  q2 : MvPolynomial (Fin 4) K
  h3 : MvPolynomial (Fin 4) K
  h4 : MvPolynomial (Fin 4) K
  q2_eq : q2 = T.finalSeamMidpointComponent 2
  h3_eq : h3 = T.finalSeamMidpointComponent 3
  h4_eq : h4 = T.finalSeamMidpointComponent 4
  q2_homogeneous : q2.IsHomogeneous 2
  h3_homogeneous : h3.IsHomogeneous 3
  h4_homogeneous : h4.IsHomogeneous 4
  core_eq :
    T.finalSeamMidpointQuarticCore = q2 + h3 + h4
  hessianDet_one :
    HC4.Polynomial.hessianDeterminant (q2 + h3 + h4) = 1
  midpointCollision :
    HasExactGradientCollision
      T.finalSeamMidpointFibre
      (finalSeamMidpointLeft (K := K))
      (finalSeamMidpointRight (K := K))

/-- Assemble the exact q2+h3+h4 quartic core. -/
theorem finalSeamQuarticHomogeneousCoreData
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hdeg : T.topFace.degree ≤ 4) :
    Nonempty T.FinalSeamQuarticHomogeneousCoreData := by
  let q2 := T.finalSeamMidpointComponent 2
  let h3 := T.finalSeamMidpointComponent 3
  let h4 := T.finalSeamMidpointComponent 4
  have hcore :
      T.finalSeamMidpointQuarticCore = q2 + h3 + h4 := by
    rfl
  refine ⟨{
    topDegree_eq_four := T.finalSeam_degree_eq_four_of_le_four hdeg
    q2 := q2
    h3 := h3
    h4 := h4
    q2_eq := rfl
    h3_eq := rfl
    h4_eq := rfl
    q2_homogeneous := by
      dsimp [q2, finalSeamMidpointComponent]
      exact fourOrdinaryDegreeComponent_isHomogeneous
        T.finalSeamMidpointFibre 2
    h3_homogeneous := by
      dsimp [h3, finalSeamMidpointComponent]
      exact fourOrdinaryDegreeComponent_isHomogeneous
        T.finalSeamMidpointFibre 3
    h4_homogeneous := by
      dsimp [h4, finalSeamMidpointComponent]
      exact fourOrdinaryDegreeComponent_isHomogeneous
        T.finalSeamMidpointFibre 4
    core_eq := hcore
    hessianDet_one := by
      rw [← hcore]
      exact T.finalSeamMidpointQuarticCore_hessianDeterminant_eq_one hdeg
    midpointCollision := T.finalSeamMidpointFibre_exactCollision
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
