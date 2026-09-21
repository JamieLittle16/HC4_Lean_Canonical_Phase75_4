
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamTransverseQuadraticPivot
import Mathlib.Tactic

/-!
# G13: literal transverse square on the zero-clock special fibre

G12 gives an honest zero-clock family after an axis-preserving determinant-one
source transvection and a transverse diagonal origin-Hessian entry which is
nonzero at parameter layer zero.

At layer zero the family is exactly its field-valued special fibre.  The
generic origin-Hessian coefficient formula therefore converts that matrix
entry into a literal nonzero quadratic source coefficient.  Since the entry
is diagonal, the exponent is the pure square `X_ell^2`, with `ell != 0`.

The same special fibre still has Hessian determinant one and the exact marked
collision `0 ~ -e_0`.  Thus the remaining Newton extraction can be phrased
entirely on one field-valued polynomial carrying a distinguished transverse
square.

No progress, terminal weight, or JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Field-valued zero-clock packet with an actual transverse square source
monomial. -/
structure FinalSeamTransverseSquareData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop where
  familyPacket : T.FinalSeamTransverseQuadraticPivotFamily
  fibre : MvPolynomial (Fin 4) K
  fibre_eq :
    fibre = polynomialFamilySpecialFiber familyPacket.family
  ell_ne_zero : familyPacket.ell ≠ (0 : Fin 4)
  squareCoeff_ne_zero :
    MvPolynomial.coeff
      (HC4.Newton.quadraticExponent familyPacket.ell familyPacket.ell)
      fibre ≠ 0
  square_mem_support :
    HC4.Newton.quadraticExponent familyPacket.ell familyPacket.ell ∈
      fibre.support
  hessianDeterminant_one :
    HC4.Polynomial.hessianDeterminant fibre = 1
  exactCollision :
    HasExactGradientCollision
      fibre
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  collisionPoints_ne :
    (fun _ : Fin 4 => (0 : K)) ≠
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)

/-- The transverse diagonal G12 entry yields a literal nonzero square
coefficient on the special fibre. -/
theorem FinalSeamTransverseQuadraticPivotFamily.specialFiber_squareCoeff_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (P : T.FinalSeamTransverseQuadraticPivotFamily) :
    MvPolynomial.coeff
      (HC4.Newton.quadraticExponent P.ell P.ell)
      (polynomialFamilySpecialFiber P.family) ≠ 0 := by
  have hentry :
      quadraticFamilyHessianMatrix
        (polynomialFamilySpecialFiber P.family) P.ell P.ell ≠ 0 := by
    rw [← familyParameterLayer_zero_eq_polynomialFamilySpecialFiber]
    rw [← quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    exact P.transverseDiagonal_ne_zero

  have hformula :=
    quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient
      (polynomialFamilySpecialFiber P.family) P.ell P.ell

  intro hcoeff
  apply hentry
  rw [hformula]
  have hquad :
      Finsupp.single P.ell 1 + Finsupp.single P.ell 1 =
        HC4.Newton.quadraticExponent P.ell P.ell := by
    rfl
  rw [hquad, hcoeff]
  simp

/-- Zero family Hessian clock specializes to determinant one. -/
theorem FinalSeamTransverseQuadraticPivotFamily.specialFiber_hessianDeterminant_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (P : T.FinalSeamTransverseQuadraticPivotFamily) :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber P.family) = 1 := by
  have hspecial :=
    hessianDeterminant_polynomialFamilySpecialFiber P.family
  have hdef := P.hessianDefect_zero
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef] at hspecial
  simpa using hspecial

/-- The G12 family collision specializes to the same marked collision on its
field-valued special fibre. -/
theorem FinalSeamTransverseQuadraticPivotFamily.specialFiber_exactCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (P : T.FinalSeamTransverseQuadraticPivotFamily) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber P.family)
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  have h :=
    polynomialFamilyExactGradientCollision_specialFiber
      P.family
      (zeroPolynomialSection (K := K))
      P.rightSection
      P.exactCollision
  have hleft :
      polynomialSectionSpecialPoint
        (zeroPolynomialSection (K := K)) =
      (fun _ : Fin 4 => (0 : K)) := by
    funext i
    simp [polynomialSectionSpecialPoint, zeroPolynomialSection]
  rw [hleft, P.rightSpecialPoint] at h
  exact h

/-- **G13 transverse square special-fibre packet.** -/
theorem finalSeamTransverseSquareData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.FinalSeamTransverseSquareData := by
  rcases T.finalSeamTransverseQuadraticPivotFamily with ⟨P⟩
  let F := polynomialFamilySpecialFiber P.family
  have hsquare :
      MvPolynomial.coeff
        (HC4.Newton.quadraticExponent P.ell P.ell) F ≠ 0 := by
    simpa [F] using P.specialFiber_squareCoeff_ne_zero
  have hmem :
      HC4.Newton.quadraticExponent P.ell P.ell ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hsquare
  refine ⟨{
    familyPacket := P
    fibre := F
    fibre_eq := rfl
    ell_ne_zero := P.ell_ne_zero
    squareCoeff_ne_zero := hsquare
    square_mem_support := hmem
    hessianDeterminant_one := by
      simpa [F] using P.specialFiber_hessianDeterminant_one
    exactCollision := by
      simpa [F] using P.specialFiber_exactCollision
    collisionPoints_ne := T.rightRecenteredSpecialFiber_collisionPoints_ne
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
