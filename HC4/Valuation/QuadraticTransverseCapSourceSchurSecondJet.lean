import HC4.Valuation.QuadraticTransverseCapSchurSecondDerivative
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# The actual quadratic source's twice-transverse Schur coefficient

This file applies the general Schur derivative theorem to the
ORIGINAL four-variable determinant-one Hessian, not a model source.
Every transverse coordinate partial derivative is an actual
`MvPolynomial.pderiv`, which mathlib already represents as a
K-linear `Derivation`.

The whole-source transverse-degree-two cap gives:
  * every transverse derivative of the lower-right 3x3 Hessian
    block is zero;
  * every SECOND transverse derivative of the mixed H₀i entries
    is zero, including the off-diagonal combinations.

Two transverse derivatives of the actual global determinant-one
Schur equation therefore give an exact source-level quadratic
coefficient in the original polynomial ring:

  det(C) · ∂ᵧⱼ∂ᵧᵢ H₀₀ =
    2 (∂ᵧᵢ H₀*)ᵀ adj(C) (∂ᵧⱼ H₀*).

The source-axis specialization, using the separately proved exact
Hessian-jet theorem, will turn this into the polynomial Riccati
equation for C(x) without inventing any source normal form.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The genuine lower-right transverse block in the GLOBAL
original-source Hessian, before restricting to the x₀-axis. -/
noncomputable def quadraticTransverseCapSourceGlobalThreeBlock
    (F : MvPolynomial (Fin 4) K) :
    GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  { a := H.d
    b := H.r
    c := H.s
    d := H.x
    e := H.y
    f := H.z }

/-- Every transverse derivative of the genuine global source
transverse Hessian block vanishes under the whole-source
quadratic transverse cap. -/
theorem quadraticTransverseCap_two_globalThreeBlock_pderiv_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (j : Fin 3) :
    let C := quadraticTransverseCapSourceGlobalThreeBlock F
    MvPolynomial.pderiv j.succ C.a = 0 ∧
    MvPolynomial.pderiv j.succ C.b = 0 ∧
    MvPolynomial.pderiv j.succ C.c = 0 ∧
    MvPolynomial.pderiv j.succ C.d = 0 ∧
    MvPolynomial.pderiv j.succ C.e = 0 ∧
    MvPolynomial.pderiv j.succ C.f = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (0 : Fin 3) (0 : Fin 3) j)
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (0 : Fin 3) (1 : Fin 3) j)
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (0 : Fin 3) (2 : Fin 3) j)
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (1 : Fin 3) (1 : Fin 3) j)
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (1 : Fin 3) (2 : Fin 3) j)
  · simpa [quadraticTransverseCapSourceGlobalThreeBlock,
      quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
        (quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound (2 : Fin 3) (2 : Fin 3) j)

/-- Under the original source's quadratic transverse cap, the
genuine mixed Hessian H₀m has ZERO double transverse derivative
in ANY two directions j,k, not just on the diagonal. -/
theorem quadraticTransverseCap_two_mixedHessian_crossTransverse_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (m j k : Fin 3) :
    MvPolynomial.pderiv k.succ
      (MvPolynomial.pderiv j.succ
        (HC4.Polynomial.hessian F 0 m.succ)) = 0 := by
  have htriple :=
    quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hbound m j k
  change
    MvPolynomial.pderiv k.succ
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv m.succ
          (MvPolynomial.pderiv (0 : Fin 4) F))) = 0
  calc
    MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv m.succ
            (MvPolynomial.pderiv (0 : Fin 4) F))) =
      MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv m.succ F))) := by
              rw [pderiv_comm_commRing m.succ (0 : Fin 4) F]
    _ = MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv m.succ F))) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                (MvPolynomial.pderiv m.succ F)]
    _ = MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv m.succ F))) := by
              rw [pderiv_comm_commRing k.succ (0 : Fin 4)
                (MvPolynomial.pderiv j.succ
                  (MvPolynomial.pderiv m.succ F))]
    _ = 0 := by rw [htriple]; simp

/-- **Actual SOURCE polynomial Schur quadratic coefficient.**

For every two transverse source-coordinate indices i,j, this is
the precise denominator-free, un-specialised Riccati coefficient
forced by det Hess(F)=1. Every hypothesis is a real property
of the source; in particular NO Riccati identity is assumed.

The next exact source-axis restriction identifies ∂ⱼ∂ᵢ H₀₀
with Cᵢⱼ'' and ∂ᵢ H₀* with the corresponding C' column. -/
theorem quadraticTransverseCap_two_sourceGlobalSchur_secondJet
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (i j : Fin 3) :
    let H := quadraticTransverseCapSourceGlobalFourBlock F
    let C := quadraticTransverseCapSourceGlobalThreeBlock F
    (MvPolynomial.pderiv j.succ
      (MvPolynomial.pderiv i.succ H.a)) * C.determinantCore =
        2 * (
          MvPolynomial.pderiv i.succ H.b *
            quadraticTransverseAdjugateVector0 C
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q) +
          MvPolynomial.pderiv i.succ H.p *
            quadraticTransverseAdjugateVector1 C
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q) +
          MvPolynomial.pderiv i.succ H.q *
            quadraticTransverseAdjugateVector2 C
              (MvPolynomial.pderiv j.succ H.b)
              (MvPolynomial.pderiv j.succ H.p)
              (MvPolynomial.pderiv j.succ H.q)) := by
  dsimp only
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let C := quadraticTransverseCapSourceGlobalThreeBlock F
  let D : Derivation K (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K) := MvPolynomial.pderiv i.succ
  let E : Derivation K (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K) := MvPolynomial.pderiv j.succ
  have hD :
      D C.a = 0 ∧ D C.b = 0 ∧ D C.c = 0 ∧
      D C.d = 0 ∧ D C.e = 0 ∧ D C.f = 0 :=
    quadraticTransverseCap_two_globalThreeBlock_pderiv_zero
      F hbound i
  have hE :
      E C.a = 0 ∧ E C.b = 0 ∧ E C.c = 0 ∧
      E C.d = 0 ∧ E C.e = 0 ∧ E C.f = 0 :=
    quadraticTransverseCap_two_globalThreeBlock_pderiv_zero
      F hbound j
  have hv₀ : E (D H.b) = 0 := by
    simpa [D, E, H, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCap_two_mixedHessian_crossTransverse_zero
        F hbound (0 : Fin 3) i j)
  have hv₁ : E (D H.p) = 0 := by
    simpa [D, E, H, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCap_two_mixedHessian_crossTransverse_zero
        F hbound (1 : Fin 3) i j)
  have hv₂ : E (D H.q) = 0 := by
    simpa [D, E, H, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCap_two_mixedHessian_crossTransverse_zero
        F hbound (2 : Fin 3) i j)
  have hcore :
      quadraticAxisFourBlockCore H.a H.b H.p H.q
        C.a C.b C.c C.d C.e C.f = 1 := by
    exact quadraticTransverseCapSourceGlobalSchur_unit F hdet
  have hzero :
      E (D (quadraticAxisFourBlockCore H.a H.b H.p H.q
        C.a C.b C.c C.d C.e C.f)) = 0 := by
    rw [hcore]
    simp
  have hsecond :=
    quadraticTransverse_schur_secondDerivative
      D E H.a H.b H.p H.q C
      hD hE hv₀ hv₁ hv₂
  rw [hsecond] at hzero
  change E (D H.a) * C.determinantCore =
    2 * (D H.b * quadraticTransverseAdjugateVector0 C
      (E H.b) (E H.p) (E H.q) +
    D H.p * quadraticTransverseAdjugateVector1 C
      (E H.b) (E H.p) (E H.q) +
    D H.q * quadraticTransverseAdjugateVector2 C
      (E H.b) (E H.p) (E H.q))
  linear_combination hzero

end

end HC4.Valuation
