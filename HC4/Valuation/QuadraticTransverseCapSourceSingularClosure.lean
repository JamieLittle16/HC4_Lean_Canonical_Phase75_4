import HC4.Valuation.QuadraticTransverseCapSourceSchurProfile
import Mathlib.Tactic

/-!
# Actual represented-source singular quadratic transverse closure

For the SAME four-variable determinant-one source F with transverse
degree at most two, the polynomial transverse Hessian C(x)
has a nonzero 2x2 minor, via the origin reverse-Rees witness.

In the singular branch det C=0, that minor is a genuine principal
pivot, with no source shear. Its exact marked-gradient collision
gives b_i(1)=b_i(0).

The real four-variable Hessian determinant on the marked axis
and on each of the six constant sections y=±e_j has unit Schur
core. The whole-source cap-two differentiated identities prove
that the three mixed entries at those sections are precisely
b'(x)±C'(x)e_j.

Thus the existing seven-section polynomial kernel-drift endpoint
yields False. No arbitrary final-resolution producer, repaired
potential, rank-two chart promotion, or graded-fibre determinant
assumption is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **Source-honest closure of the singular transverse-rank-two
quadratic-cap case.**

The only assumptions are the real source transverse cap, the real
source Hessian determinant one, the genuinely singular *source-axis*
transverse 3x3 block, and the actual transverse-linear marked
collision. Every Schur section equation is derived internally. -/
theorem quadraticTransverseCap_two_singularSource_impossible
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hsingular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore = 0)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K)
        (quadraticTransverseCapSourceLinearCoefficients F i) =
      Polynomial.eval (0 : K)
        (quadraticTransverseCapSourceLinearCoefficients F i)) :
    False := by
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let H₀ := quadraticTransverseCapSourceAxisFourBlock F
  let ep : Fin 3 → Fin 3 → K :=
    fun j k => if k = j then 1 else 0
  let em : Fin 3 → Fin 3 → K :=
    fun j k => if k = j then -1 else 0
  let Hp : Fin 3 → GeneralFourBlock (Polynomial K) :=
    fun j => quadraticTransverseSourceSectionFourBlock F (ep j)
  let Hm : Fin 3 → GeneralFourBlock (Polynomial K) :=
    fun j => quadraticTransverseSourceSectionFourBlock F (em j)
  let up : Fin 3 → Polynomial K := fun j => (Hp j).a
  let um : Fin 3 → Polynomial K := fun j => (Hm j).a
  have hpivot :
      C.d * C.f - C.e * C.e ≠ 0 ∨
      C.a * C.f - C.c * C.c ≠ 0 ∨
      C.a * C.d - C.b * C.b ≠ 0 :=
    quadraticTransverseCapSource_singular_principalPivot
      F hbound hdet hsing
  have haxis :
      quadraticAxisFourBlockCore H₀.a
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1 :=
    quadraticTransverseCapSource_axisSchur_unit F hdet
  have hplusRow (i j : Fin 3) :
      quadraticTransverseCapFourBlock_mixedRow (Hp j) i =
        Polynomial.derivative (b i) +
          Polynomial.derivative (C.matrix i j) := by
    simpa [Hp, ep] using
      (quadraticTransverseCap_two_sectionMixedRow_affine
        F hbound i j (1 : K))
  have hminusRow (i j : Fin 3) :
      quadraticTransverseCapFourBlock_mixedRow (Hm j) i =
        Polynomial.derivative (b i) -
          Polynomial.derivative (C.matrix i j) := by
    simpa [Hm, em] using
      (quadraticTransverseCap_two_sectionMixedRow_affine
        F hbound i j (-1 : K))
  have hplus (j : Fin 3) :
      quadraticAxisFourBlockCore (up j)
        (Polynomial.derivative (b 0) +
          Polynomial.derivative (C.matrix 0 j))
        (Polynomial.derivative (b 1) +
          Polynomial.derivative (C.matrix 1 j))
        (Polynomial.derivative (b 2) +
          Polynomial.derivative (C.matrix 2 j))
        C.a C.b C.c C.d C.e C.f = 1 := by
    have hunit :
        quadraticAxisFourBlockCore (Hp j).a
          (Hp j).b (Hp j).p (Hp j).q
          C.a C.b C.c C.d C.e C.f = 1 :=
      quadraticTransverseCap_two_actualSectionSchur_unit
        F hbound hdet (ep j)
    have hb : (Hp j).b = Polynomial.derivative (b 0) +
        Polynomial.derivative (C.matrix 0 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hplusRow (0 : Fin 3) j
    have hp : (Hp j).p = Polynomial.derivative (b 1) +
        Polynomial.derivative (C.matrix 1 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hplusRow (1 : Fin 3) j
    have hq : (Hp j).q = Polynomial.derivative (b 2) +
        Polynomial.derivative (C.matrix 2 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hplusRow (2 : Fin 3) j
    change quadraticAxisFourBlockCore (Hp j).a
      (Polynomial.derivative (b 0) + Polynomial.derivative (C.matrix 0 j))
      (Polynomial.derivative (b 1) + Polynomial.derivative (C.matrix 1 j))
      (Polynomial.derivative (b 2) + Polynomial.derivative (C.matrix 2 j))
      C.a C.b C.c C.d C.e C.f = 1
    rw [← hb, ← hp, ← hq]
    exact hunit
  have hminus (j : Fin 3) :
      quadraticAxisFourBlockCore (um j)
        (Polynomial.derivative (b 0) -
          Polynomial.derivative (C.matrix 0 j))
        (Polynomial.derivative (b 1) -
          Polynomial.derivative (C.matrix 1 j))
        (Polynomial.derivative (b 2) -
          Polynomial.derivative (C.matrix 2 j))
        C.a C.b C.c C.d C.e C.f = 1 := by
    have hunit :
        quadraticAxisFourBlockCore (Hm j).a
          (Hm j).b (Hm j).p (Hm j).q
          C.a C.b C.c C.d C.e C.f = 1 :=
      quadraticTransverseCap_two_actualSectionSchur_unit
        F hbound hdet (em j)
    have hb : (Hm j).b = Polynomial.derivative (b 0) -
        Polynomial.derivative (C.matrix 0 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hminusRow (0 : Fin 3) j
    have hp : (Hm j).p = Polynomial.derivative (b 1) -
        Polynomial.derivative (C.matrix 1 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hminusRow (1 : Fin 3) j
    have hq : (Hm j).q = Polynomial.derivative (b 2) -
        Polynomial.derivative (C.matrix 2 j) := by
      simpa [quadraticTransverseCapFourBlock_mixedRow] using
        hminusRow (2 : Fin 3) j
    change quadraticAxisFourBlockCore (Hm j).a
      (Polynomial.derivative (b 0) - Polynomial.derivative (C.matrix 0 j))
      (Polynomial.derivative (b 1) - Polynomial.derivative (C.matrix 1 j))
      (Polynomial.derivative (b 2) - Polynomial.derivative (C.matrix 2 j))
      C.a C.b C.c C.d C.e C.f = 1
    rw [← hb, ← hp, ← hq]
    exact hunit
  exact quadraticTransverseCap_rankTwo_sevenSchurSections_impossible
    C b H₀.a up um hsingular hpivot haxis hplus hminus hcoll

end

end HC4.Valuation
