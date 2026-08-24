import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTopLayerPeeling
import HC4.Polynomial.DerivativeBounds
import Mathlib.Tactic

/-!
# Cross-degree Hessian equation for the stationary binary core

Let `Q = H + R`, where `H` is the maximal ordinary-homogeneous layer of
binary degree `D` and `R` has maximal active degree `E < D`.  The full binary
core satisfies

    det Hess Q = 0.

The degree `D + E - 4` part of this determinant cannot receive a contribution
from `det Hess R`, whose degree is at most `2E - 4`.  It is therefore exactly
the bilinear polarisation of the binary Hessian determinant between the top
layer `H` and the next layer `G = in_E(R)`.

This file proves that statement with exact weighted initial forms.  In the
nonlinear branch `H = a L^D`, so the resulting equation is the precise input
for the next direction-lock theorem: it says that the second derivative of
`G` transverse to `L` vanishes.  No JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Bilinear polarisation of the binary Hessian determinant.  The symmetric
four-term form avoids introducing a scalar `2`, which keeps the weighted
support bookkeeping completely formal. -/
def binaryHessianDetCross
    (P Q : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  directionalSecondDerivative (0 : Fin 2) P *
      directionalSecondDerivative (1 : Fin 2) Q +
    directionalSecondDerivative (0 : Fin 2) Q *
      directionalSecondDerivative (1 : Fin 2) P -
    directionalMixedDerivative (0 : Fin 2) 1 P *
      directionalMixedDerivative (0 : Fin 2) 1 Q -
    directionalMixedDerivative (0 : Fin 2) 1 Q *
      directionalMixedDerivative (0 : Fin 2) 1 P

/-- Exact polarisation identity for the binary Hessian determinant. -/
theorem binaryDirectionalHessianDet_add_cross
    (P Q : MvPolynomial (Fin 2) K) :
    binaryDirectionalHessianDet (0 : Fin 2) 1 (P + Q) =
      binaryDirectionalHessianDet (0 : Fin 2) 1 P +
        binaryHessianDetCross P Q +
          binaryDirectionalHessianDet (0 : Fin 2) 1 Q := by
  unfold binaryDirectionalHessianDet binaryHessianDetCross
    directionalSecondDerivative directionalMixedDerivative
  simp only [map_add]
  ring

/-- A homogeneous left factor can be pulled out of the exact top component of
its product with a weakly bounded right factor. -/
theorem initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous
    {σ : Type*} [DecidableEq σ]
    {w : σ → ℤ} {a b : ℤ}
    {P Q : MvPolynomial σ K}
    (hP : MvPolynomial.IsWeightedHomogeneous w P a)
    (hQ : IsWeightLE w b Q) :
    initialForm w (a + b) (P * Q) =
      P * initialForm w b Q := by
  let Q0 : MvPolynomial σ K := initialForm w b Q
  have hQ0hom : MvPolynomial.IsWeightedHomogeneous w Q0 b := by
    exact initialForm_isWeightedHomogeneous w b Q
  have hQdiff : IsWeightLT w b (Q - Q0) := by
    simpa [Q0] using sub_initialForm_isWeightLT hQ
  have hPLE : IsWeightLE w a P :=
    isWeightLE_of_isWeightedHomogeneous hP
  have hlow : IsWeightLT w (a + b) (P * (Q - Q0)) :=
    hPLE.mul_lt hQdiff
  have hlowZero : initialForm w (a + b) (P * (Q - Q0)) = 0 :=
    initialForm_eq_zero_of_isWeightLT hlow (le_refl _)
  have htopHom :
      MvPolynomial.IsWeightedHomogeneous w (P * Q0) (a + b) :=
    MvPolynomial.IsWeightedHomogeneous.mul hP hQ0hom
  have htop : initialForm w (a + b) (P * Q0) = P * Q0 :=
    initialForm_eq_self_of_isWeightedHomogeneous htopHom
  have hdecomp : P * Q = P * Q0 + P * (Q - Q0) := by ring
  rw [hdecomp, initialForm_add, htop, hlowZero, add_zero]

/-- Ordinary-weight homogeneity of a binary Hessian entry of a homogeneous
polynomial. -/
theorem binaryHessianEntry_isWeightedHomogeneous
    (H : MvPolynomial (Fin 2) K)
    (D : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (i j : Fin 2) :
    MvPolynomial.IsWeightedHomogeneous binaryOrdinaryIntegerWeight
      (HC4.Polynomial.hessian H i j) ((D : ℤ) - 2) := by
  have h := HC4.Polynomial.hessian_entry_isWeightedHomogeneous hH i j
  have hshift :
      (D : ℤ) - binaryOrdinaryIntegerWeight i - binaryOrdinaryIntegerWeight j =
        (D : ℤ) - 2 := by
    change (D : ℤ) - 1 - 1 = (D : ℤ) - 2
    ring
  rw [hshift] at h
  exact h

/-- Ordinary-weight upper bound for a binary Hessian entry. -/
theorem binaryHessianEntry_isWeightLE
    (Q : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hQ : IsWeightLE binaryOrdinaryIntegerWeight E Q)
    (i j : Fin 2) :
    IsWeightLE binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
      (HC4.Polynomial.hessian Q i j) := by
  have h := hQ.hessian_entry i j
  have hshift :
      (E : ℤ) - binaryOrdinaryIntegerWeight i - binaryOrdinaryIntegerWeight j =
        (E : ℤ) - 2 := by
    change (E : ℤ) - 1 - 1 = (E : ℤ) - 2
    ring
  rw [hshift] at h
  exact h

/-- The binary Hessian determinant of a polynomial of ordinary degree at most
`E` has ordinary weight at most `(E-2)+(E-2)`.  This formulation works without
special cases when `E < 2`: the derivative bounds simply force the relevant
entries to vanish. -/
theorem binaryDirectionalHessianDet_isWeightLE
    (Q : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (hQ : IsWeightLE binaryOrdinaryIntegerWeight E Q) :
    IsWeightLE binaryOrdinaryIntegerWeight
      (((E : ℤ) - 2) + ((E : ℤ) - 2))
      (binaryDirectionalHessianDet (0 : Fin 2) 1 Q) := by
  have h00 : IsWeightLE binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
      (directionalSecondDerivative (0 : Fin 2) Q) := by
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE Q E hQ (0 : Fin 2) 0)
  have h11 : IsWeightLE binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
      (directionalSecondDerivative (1 : Fin 2) Q) := by
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE Q E hQ (1 : Fin 2) 1)
  have h01 : IsWeightLE binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
      (directionalMixedDerivative (0 : Fin 2) 1 Q) := by
    simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE Q E hQ (1 : Fin 2) 0)
  have hprod := h00.mul h11
  have hsq := h01.mul h01
  simpa [binaryDirectionalHessianDet, pow_two] using hprod.sub hsq

/-- The exact ordinary degree-`E-2` component of every Hessian entry of `R`
is the corresponding Hessian entry of its degree-`E` component. -/
theorem initialForm_binaryHessianEntry_eq_componentHessian
    (R : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (i j : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
        (HC4.Polynomial.hessian R i j) =
      HC4.Polynomial.hessian (binaryOrdinaryDegreeComponent R E) i j := by
  have h := HC4.Polynomial.hessian_initialForm_entry
    binaryOrdinaryIntegerWeight (E : ℤ) R i j
  have hshift :
      (E : ℤ) - binaryOrdinaryIntegerWeight i - binaryOrdinaryIntegerWeight j =
        (E : ℤ) - 2 := by
    change (E : ℤ) - 1 - 1 = (E : ℤ) - 2
    ring
  rw [hshift] at h
  simpa [binaryOrdinaryDegreeComponent] using h.symm

/-- Directional pure second derivatives commute with extraction of an exact
ordinary homogeneous component. -/
theorem initialForm_directionalSecondDerivative_eq_component
    (R : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (i : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
        (directionalSecondDerivative i R) =
      directionalSecondDerivative i (binaryOrdinaryDegreeComponent R E) := by
  simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
    (initialForm_binaryHessianEntry_eq_componentHessian R E i i)

/-- Directional mixed second derivatives commute with extraction of an exact
ordinary homogeneous component. -/
theorem initialForm_directionalMixedDerivative_eq_component
    (R : MvPolynomial (Fin 2) K)
    (E : ℕ)
    (i j : Fin 2) :
    initialForm binaryOrdinaryIntegerWeight ((E : ℤ) - 2)
        (directionalMixedDerivative i j R) =
      directionalMixedDerivative i j (binaryOrdinaryDegreeComponent R E) := by
  simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
    (initialForm_binaryHessianEntry_eq_componentHessian R E j i)

/-- **Exact cross-layer extraction.**

If `H` is homogeneous of degree `D` and `R` has ordinary degree at most `E`,
then the degree `(D-2)+(E-2)` component of their Hessian polarisation uses
exactly the degree-`E` component of `R`. -/
theorem initialForm_binaryHessianDetCross_eq_nextComponent
    (H R : MvPolynomial (Fin 2) K)
    (D E : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hR : IsWeightLE binaryOrdinaryIntegerWeight E R) :
    initialForm binaryOrdinaryIntegerWeight
        (((D : ℤ) - 2) + ((E : ℤ) - 2))
        (binaryHessianDetCross H R) =
      binaryHessianDetCross H (binaryOrdinaryDegreeComponent R E) := by
  let w := binaryOrdinaryIntegerWeight
  let Hd00 := directionalSecondDerivative (0 : Fin 2) H
  let Hd11 := directionalSecondDerivative (1 : Fin 2) H
  let Hd01 := directionalMixedDerivative (0 : Fin 2) 1 H
  let Rd00 := directionalSecondDerivative (0 : Fin 2) R
  let Rd11 := directionalSecondDerivative (1 : Fin 2) R
  let Rd01 := directionalMixedDerivative (0 : Fin 2) 1 R
  let G := binaryOrdinaryDegreeComponent R E
  have hH00 : MvPolynomial.IsWeightedHomogeneous w Hd00 ((D : ℤ) - 2) := by
    dsimp [w, Hd00]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (0 : Fin 2) 0)
  have hH11 : MvPolynomial.IsWeightedHomogeneous w Hd11 ((D : ℤ) - 2) := by
    dsimp [w, Hd11]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (1 : Fin 2) 1)
  have hH01 : MvPolynomial.IsWeightedHomogeneous w Hd01 ((D : ℤ) - 2) := by
    dsimp [w, Hd01]
    simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightedHomogeneous H D hH (1 : Fin 2) 0)
  have hR00 : IsWeightLE w ((E : ℤ) - 2) Rd00 := by
    dsimp [w, Rd00]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE R E hR (0 : Fin 2) 0)
  have hR11 : IsWeightLE w ((E : ℤ) - 2) Rd11 := by
    dsimp [w, Rd11]
    simpa [directionalSecondDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE R E hR (1 : Fin 2) 1)
  have hR01 : IsWeightLE w ((E : ℤ) - 2) Rd01 := by
    dsimp [w, Rd01]
    simpa [directionalMixedDerivative, HC4.Polynomial.hessian_apply] using
      (binaryHessianEntry_isWeightLE R E hR (1 : Fin 2) 0)
  have htop00_11 :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Hd00 * Rd11) =
        Hd00 * directionalSecondDerivative (1 : Fin 2) G := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hH00 hR11]
    dsimp [w, Rd11, G]
    rw [initialForm_directionalSecondDerivative_eq_component R E (1 : Fin 2)]
  have htop11_00 :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Rd00 * Hd11) =
        directionalSecondDerivative (0 : Fin 2) G * Hd11 := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hH11 hR00]
    dsimp [w, Rd00, G]
    rw [initialForm_directionalSecondDerivative_eq_component R E (0 : Fin 2)]
    ring
  have htop01_a :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Hd01 * Rd01) =
        Hd01 * directionalMixedDerivative (0 : Fin 2) 1 G := by
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hH01 hR01]
    dsimp [w, Rd01, G]
    rw [initialForm_directionalMixedDerivative_eq_component R E (0 : Fin 2) 1]
  have htop01_b :
      initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2)) (Rd01 * Hd01) =
        directionalMixedDerivative (0 : Fin 2) 1 G * Hd01 := by
    rw [mul_comm]
    rw [initialForm_mul_eq_left_mul_initialForm_of_leftHomogeneous hH01 hR01]
    dsimp [w, Rd01, G]
    rw [initialForm_directionalMixedDerivative_eq_component R E (0 : Fin 2) 1]
    ring
  unfold binaryHessianDetCross
  change initialForm w (((D : ℤ) - 2) + ((E : ℤ) - 2))
      (Hd00 * Rd11 + Rd00 * Hd11 - Hd01 * Rd01 - Rd01 * Hd01) = _
  simp only [map_sub, initialForm_add]
  rw [htop00_11, htop11_00, htop01_a, htop01_b]

/-- **First nontrivial mixed-degree consequence of `det Hess Q = 0`.**

If `Q = H + R`, `H` is homogeneous of degree `D`, `R` has maximal degree
`E < D`, and the Hessian determinants of `Q` and `H` vanish, then the Hessian
polarisation between `H` and the maximal degree-`E` layer of `R` vanishes.
-/
theorem binaryHessianDetCross_nextComponent_eq_zero
    (Q H R : MvPolynomial (Fin 2) K)
    (D E : ℕ)
    (hdecomp : Q = H + R)
    (hH : MvPolynomial.IsWeightedHomogeneous
      binaryOrdinaryIntegerWeight H D)
    (hR : IsWeightLE binaryOrdinaryIntegerWeight E R)
    (hED : E < D)
    (hQdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0)
    (hHdet : binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0) :
    binaryHessianDetCross H (binaryOrdinaryDegreeComponent R E) = 0 := by
  let n : ℤ := ((D : ℤ) - 2) + ((E : ℤ) - 2)
  have hRdetLE := binaryDirectionalHessianDet_isWeightLE R E hR
  have hboundlt :
      (((E : ℤ) - 2) + ((E : ℤ) - 2)) < n := by
    dsimp [n]
    have hcast : (E : ℤ) < (D : ℤ) := by exact_mod_cast hED
    omega
  have hRdetTop :
      initialForm binaryOrdinaryIntegerWeight n
        (binaryDirectionalHessianDet (0 : Fin 2) 1 R) = 0 :=
    initialForm_eq_zero_of_isWeightLE hRdetLE hboundlt
  have hQsum :
      binaryHessianDetCross H R +
          binaryDirectionalHessianDet (0 : Fin 2) 1 R = 0 := by
    have hexpand := binaryDirectionalHessianDet_add_cross H R
    have hsum :
        binaryHessianDetCross H R +
            binaryDirectionalHessianDet (0 : Fin 2) 1 R =
          binaryDirectionalHessianDet (0 : Fin 2) 1 (H + R) -
            binaryDirectionalHessianDet (0 : Fin 2) 1 H := by
      rw [hexpand]
      ring
    rw [hsum, ← hdecomp, hQdet, hHdet]
    ring
  have hcomponent := congrArg
    (fun P : MvPolynomial (Fin 2) K =>
      initialForm binaryOrdinaryIntegerWeight n P) hQsum
  have hcrossTop := initialForm_binaryHessianDetCross_eq_nextComponent
    H R D E hH hR
  dsimp [n] at hcomponent hRdetTop
  rw [initialForm_add, hcrossTop, hRdetTop, add_zero, initialForm_zero]
    at hcomponent
  exact hcomponent

/-- Assembly-facing frontier after the first exact mixed-degree Hessian
calculation.  The nonlinear branch either collapses to its top linear power or
retains a strictly lower maximal layer together with the exact vanishing
cross-Hessian equation. -/
inductive BinarySingularHessianTopLayerCrossFrontier
    (Q : MvPolynomial (Fin 2) K) : Type (u + 1)
  | lowDegree
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
  | nonlinearCollapsed
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (Q_eq_H : Q = H)
  | nonlinearNextLayer
      (D : ℕ)
      (H : MvPolynomial (Fin 2) K)
      (hD : 2 ≤ D)
      (H_eq : H = binaryOrdinaryDegreeComponent Q D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
      (a : K)
      (c : Fin 2 → K)
      (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
      (R : MvPolynomial (Fin 2) K)
      (R_eq : R = Q - H)
      (R_ne_zero : R ≠ 0)
      (E : ℕ)
      (G : MvPolynomial (Fin 2) K)
      (E_lt_D : E < D)
      (G_eq : G = binaryOrdinaryDegreeComponent R E)
      (G_ne_zero : G ≠ 0)
      (remainder_maximal : ∀ d ∈ R.support, d.degree ≤ E)
      (G_homogeneous : G.IsHomogeneous E)
      (cross_zero : binaryHessianDetCross H G = 0)

/-- Every nonzero singular-Hessian binary polynomial reaches the exact
cross-degree frontier. -/
theorem binarySingularHessian_topLayerCrossFrontier
    (Q : MvPolynomial (Fin 2) K)
    (hQ : Q ≠ 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    Nonempty (BinarySingularHessianTopLayerCrossFrontier Q) := by
  rcases binarySingularHessian_maximalLayerFrontier Q hQ hdet with ⟨M⟩
  cases M with
  | lowDegree D H hD H_eq H_ne_zero maximal =>
      exact ⟨.lowDegree D H hD H_eq H_ne_zero maximal⟩
  | nonlinearLinearPower D H hD H_eq H_ne_zero maximal a c normalForm =>
      rcases binaryMaximalLayer_residualFrontier Q D H H_eq maximal with ⟨P⟩
      cases P with
      | collapsed Q_eq_H =>
          exact ⟨.nonlinearCollapsed D H hD H_eq H_ne_zero maximal
            a c normalForm Q_eq_H⟩
      | nextLayer R R_eq R_ne_zero E G E_lt_D G_eq G_ne_zero
          remainder_maximal G_homogeneous =>
          have hHhom : MvPolynomial.IsWeightedHomogeneous
              binaryOrdinaryIntegerWeight H D := by
            rw [H_eq]
            simpa [binaryOrdinaryDegreeComponent] using
              (initialForm_isWeightedHomogeneous
                binaryOrdinaryIntegerWeight D Q)
          have hRLE : IsWeightLE binaryOrdinaryIntegerWeight E R :=
            isWeightLE_binaryOrdinary_of_degree_le R E remainder_maximal
          have hdecomp : Q = H + R := by
            rw [R_eq]
            ring
          have hHdet :
              binaryDirectionalHessianDet (0 : Fin 2) 1 H = 0 := by
            rw [H_eq]
            exact binaryOrdinaryDegreeComponent_det_zero_of_maximal
              Q D maximal hdet
          have hcross0 := binaryHessianDetCross_nextComponent_eq_zero
            Q H R D E hdecomp hHhom hRLE E_lt_D hdet hHdet
          have hcross : binaryHessianDetCross H G = 0 := by
            rw [G_eq]
            exact hcross0
          exact ⟨.nonlinearNextLayer D H hD H_eq H_ne_zero maximal
            a c normalForm R R_eq R_ne_zero E G E_lt_D G_eq G_ne_zero
            remainder_maximal G_homogeneous hcross⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The actual HC4 transverse stationary binary core reaches the same exact
cross-degree frontier without losing any source-level provenance stored in
`D.binaryData`. -/
theorem DirectClosingCanonicalSquareBinaryMaximalLayerData.topLayerCrossFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (D : DirectClosingCanonicalSquareBinaryMaximalLayerData C heq) :
    Nonempty (BinarySingularHessianTopLayerCrossFrontier
      D.binaryData.binaryFace) :=
  binarySingularHessian_topLayerCrossFrontier
    D.binaryData.binaryFace D.binaryData.binaryFace_ne_zero
      D.binaryData.binary_det_zero

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
