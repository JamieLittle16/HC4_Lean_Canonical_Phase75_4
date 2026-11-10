import HC4.Valuation.QuadraticTransverseCapSourceRiccatiCleared
import Mathlib.Tactic

/-!
# The genuine transverse-linear Schur coefficient for the original source

For F(x,y)=a(x)+b(x)·y+(1/2)yᵀC(x)y, the y-linear coefficient of
det Hess F=1 is the polynomial identity

    det C * b'' = 2 C' adj(C) b'.

We do NOT assume the displayed normal form. Instead the whole-source
transverse degree cap gives ∂ᵧ C=0. Differentiating the original
global Hessian Schur identity once and restricting to the actual
marked x-axis gives the identity directly, for all three entries
of b(x). This is the second concrete polynomial coefficient needed
to close the generic-rank-three quadratic branch.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The exact original source axis restriction of one transverse
derivative of H₀₀ is bⱼ''(x), with b the ORIGINAL transverse-linear
longitudinal coefficient polynomial. -/
theorem quadraticTransverseCapSource_axisLongitudinal_firstTransverseJet
    (F : MvPolynomial (Fin 4) K)
    (j : Fin 3) :
    longitudinalAxisRestrictionRingHom (K := K)
      (MvPolynomial.pderiv j.succ
        (HC4.Polynomial.hessian F 0 0)) =
      Polynomial.derivative
        (Polynomial.derivative
          (quadraticTransverseCapSourceLinearCoefficients F j)) := by
  have hcomm :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4) F)) =
      MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ F)) := by
    calc
      MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv (0 : Fin 4) F)) =
        MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv (0 : Fin 4) F)) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                (MvPolynomial.pderiv (0 : Fin 4) F)]
      _ = MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv j.succ F)) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4) F]
  change
    longitudinalAxisRestriction
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4) F))) =
    Polynomial.derivative
      (Polynomial.derivative
        (longitudinalCoefficientPolynomialAt
          (Finsupp.single j 1) F))
  rw [hcomm, longitudinalAxisRestriction_pderiv_zero,
    longitudinalAxisRestriction_pderiv_zero,
    longitudinalCoefficient_single_eq_axisRestriction_pderiv]

/-- The first transverse derivative of the exact GLOBAL source
Schur core yields the real un-specialised linear coefficient
equation, with no new Riccati or source-normal-form assumption. -/
theorem quadraticTransverseCap_two_sourceGlobalSchur_firstJet
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (j : Fin 3) :
    let H := quadraticTransverseCapSourceGlobalFourBlock F
    let G := quadraticTransverseCapSourceGlobalThreeBlock F
    MvPolynomial.pderiv j.succ H.a * G.determinantCore =
      2 * (
        MvPolynomial.pderiv j.succ H.b *
          quadraticTransverseAdjugateVector0 G H.b H.p H.q +
        MvPolynomial.pderiv j.succ H.p *
          quadraticTransverseAdjugateVector1 G H.b H.p H.q +
        MvPolynomial.pderiv j.succ H.q *
          quadraticTransverseAdjugateVector2 G H.b H.p H.q) := by
  dsimp only
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let G := quadraticTransverseCapSourceGlobalThreeBlock F
  let D : Derivation K (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K) := MvPolynomial.pderiv j.succ
  have hC :
      D G.a = 0 ∧ D G.b = 0 ∧ D G.c = 0 ∧
      D G.d = 0 ∧ D G.e = 0 ∧ D G.f = 0 :=
    quadraticTransverseCap_two_globalThreeBlock_pderiv_zero
      F hbound j
  have hunit :
      quadraticAxisFourBlockCore H.a H.b H.p H.q
        G.a G.b G.c G.d G.e G.f = 1 :=
    quadraticTransverseCapSourceGlobalSchur_unit F hdet
  have hz :
      D (quadraticAxisFourBlockCore H.a H.b H.p H.q
        G.a G.b G.c G.d G.e G.f) = 0 := by
    rw [hunit]
    simp
  have hder :=
    quadraticTransverse_schur_firstDerivative
      D H.a H.b H.p H.q G hC
  rw [hder] at hz
  change D H.a * G.determinantCore =
    2 * (
      D H.b * quadraticTransverseAdjugateVector0 G H.b H.p H.q +
      D H.p * quadraticTransverseAdjugateVector1 G H.b H.p H.q +
      D H.q * quadraticTransverseAdjugateVector2 G H.b H.p H.q)
  linear_combination hz

/-- **Actual source transverse-linear coefficient in K[x].**

The precise denominator-cleared equation for each bⱼ'' is a
theorem of the represented source's true quadratic cap and
Hessian determinant, without assuming generic invertibility. -/
theorem quadraticTransverseCap_two_sourceRiccati_linearCleared
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (j : Fin 3) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    let b := quadraticTransverseCapSourceLinearCoefficients F
    C.determinantCore *
      Polynomial.derivative (Polynomial.derivative (b j)) =
      2 * (
        Polynomial.derivative (C.matrix 0 j) *
          quadraticTransverseAdjugateVector0 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative (C.matrix 1 j) *
          quadraticTransverseAdjugateVector1 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2)) +
        Polynomial.derivative (C.matrix 2 j) *
          quadraticTransverseAdjugateVector2 C
            (Polynomial.derivative (b 0))
            (Polynomial.derivative (b 1))
            (Polynomial.derivative (b 2))) := by
  dsimp only
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let G := quadraticTransverseCapSourceGlobalThreeBlock F
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let φ : MvPolynomial (Fin 4) K →+* Polynomial K :=
    longitudinalAxisRestrictionRingHom (K := K)
  obtain ⟨ha, hb, hc, hd, he, hf⟩ :=
    quadraticTransverseCapSource_globalThreeBlock_axisEntries F
  have hdetmap : φ G.determinantCore = C.determinantCore := by
    simp [GeneralThreeBlock.determinantCore,
      ha, hb, hc, hd, he, hf]
  have hmix₀ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.b) =
        Polynomial.derivative (C.matrix 0 k) := by
    simpa [φ, H, C, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (0 : Fin 3) k)
  have hmix₁ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.p) =
        Polynomial.derivative (C.matrix 1 k) := by
    simpa [φ, H, C, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (1 : Fin 3) k)
  have hmix₂ (k : Fin 3) :
      φ (MvPolynomial.pderiv k.succ H.q) =
        Polynomial.derivative (C.matrix 2 k) := by
    simpa [φ, H, C, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_globalMixedDerivative_axis
        F (2 : Fin 3) k)
  have hv₀ : φ H.b = Polynomial.derivative (b 0) := by
    simpa [φ, H, b, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      quadraticTransverseCapSourceLinearCoefficients] using
      longitudinalAxisRestriction_hessian_zero_succ (0 : Fin 3) F
  have hv₁ : φ H.p = Polynomial.derivative (b 1) := by
    simpa [φ, H, b, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      quadraticTransverseCapSourceLinearCoefficients] using
      longitudinalAxisRestriction_hessian_zero_succ (1 : Fin 3) F
  have hv₂ : φ H.q = Polynomial.derivative (b 2) := by
    simpa [φ, H, b, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      quadraticTransverseCapSourceLinearCoefficients] using
      longitudinalAxisRestriction_hessian_zero_succ (2 : Fin 3) F
  have hjet :
      φ (MvPolynomial.pderiv j.succ H.a) =
        Polynomial.derivative (Polynomial.derivative (b j)) := by
    simpa [φ, H, b, quadraticTransverseCapSourceGlobalFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      quadraticTransverseCapSource_axisLongitudinal_firstTransverseJet F j
  have hadj₀ :
      φ (quadraticTransverseAdjugateVector0 G H.b H.p H.q) =
        quadraticTransverseAdjugateVector0 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    simp [quadraticTransverseAdjugateVector0,
      ha, hb, hc, hd, he, hf, hv₀, hv₁, hv₂]
  have hadj₁ :
      φ (quadraticTransverseAdjugateVector1 G H.b H.p H.q) =
        quadraticTransverseAdjugateVector1 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    simp [quadraticTransverseAdjugateVector1,
      ha, hb, hc, hd, he, hf, hv₀, hv₁, hv₂]
  have hadj₂ :
      φ (quadraticTransverseAdjugateVector2 G H.b H.p H.q) =
        quadraticTransverseAdjugateVector2 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    simp [quadraticTransverseAdjugateVector2,
      ha, hb, hc, hd, he, hf, hv₀, hv₁, hv₂]
  have hsource :=
    quadraticTransverseCap_two_sourceGlobalSchur_firstJet
      F hbound hdet j
  have hmapped := congrArg φ hsource
  dsimp only at hmapped
  simp only [map_mul, map_add, map_sub, map_ofNat] at hmapped
  rw [hjet, hdetmap, hmix₀ j, hmix₁ j, hmix₂ j,
      hadj₀, hadj₁, hadj₂] at hmapped
  linear_combination hmapped

end

end HC4.Valuation
