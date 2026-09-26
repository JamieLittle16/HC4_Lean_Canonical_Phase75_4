import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamSimpleAxisPivot
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingOriginPencil
import Mathlib.Tactic

/-!
# G12: axis-preserving transverse quadratic pivot at zero clock

The final seam is already a determinant-one static polynomial with a distinct
marked collision from the origin to `-e₀`.  Embed that polynomial as a family
constant in a dummy parameter.  Its Hessian clock is therefore exactly zero.

The source-origin Hessian is invertible, hence nonzero.  The existing
axis-preserving quadratic normalization theorem applies at parameter layer
zero: one honest determinant-one source transvection, whose added direction is
transverse, makes a transverse diagonal origin-Hessian coefficient nonzero.

Because the added direction is transverse, the inverse transvection fixes the
marked special point `-e₀`.  Exact gradient collision and Hessian defect are
preserved by the already-green covariance theorems.

This produces a genuine family-level transverse quadratic pivot at zero clock.
No positive-clock carrier, progress theorem, repair transition, terminal
cocharacter, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The special fibre of a constant polynomial family is the original
field-valued polynomial. -/
theorem polynomialFamilySpecialFiber_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K) :
    polynomialFamilySpecialFiber (constantPolynomialFamily F) = F := by
  apply MvPolynomial.ext
  intro d
  simp [polynomialFamilySpecialFiber, constantPolynomialFamily]

/-- A determinant-one static polynomial becomes a polynomial family with
exact zero Hessian clock. -/
theorem constantPolynomialFamily_hasHessianDefect_zero
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    HasPolynomialFamilyHessianDefect
      (K := K) (constantPolynomialFamily F) 0 := by
  unfold HasPolynomialFamilyHessianDefect
  rw [hessianDeterminant_constantPolynomialFamily, hdet]
  simp [constantPolynomialFamily]

/-- A static exact gradient collision lifts to the same collision between
constant polynomial sections of the constant family. -/
theorem constantPolynomialFamily_exactGradientCollision
    (F : MvPolynomial (Fin 4) K)
    (p q : Fin 4 → K)
    (hcoll : HasExactGradientCollision F p q) :
    HasPolynomialFamilyExactGradientCollision
      (constantPolynomialFamily F)
      (polynomialConstantSection p)
      (polynomialConstantSection q) := by
  intro i
  change
    MvPolynomial.eval (fun j => Polynomial.C (p j))
        (MvPolynomial.pderiv i (MvPolynomial.map Polynomial.C F)) =
      MvPolynomial.eval (fun j => Polynomial.C (q j))
        (MvPolynomial.pderiv i (MvPolynomial.map Polynomial.C F))
  simp only [MvPolynomial.pderiv_map]
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  exact congrArg Polynomial.C (hcoll i)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Honest zero-clock family packet after one marked-axis-preserving source
transvection has exposed a transverse quadratic pivot. -/
structure FinalSeamTransverseQuadraticPivotFamily
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) where
  k : Fin 4
  ell : Fin 4
  a : K
  k_ne_ell : k ≠ ell
  ell_ne_zero : ell ≠ (0 : Fin 4)
  family : MvPolynomial (Fin 4) (Polynomial K)
  rightSection : Fin 4 → Polynomial K
  family_eq :
    family =
      transverseSourceShearHom
        (K := K) k ell (Polynomial.C a)
        (constantPolynomialFamily T.rightRecenteredSpecialFiber)
  rightSection_eq :
    rightSection =
      transverseSourceUnshearSection
        k ell (Polynomial.C a)
        (polynomialConstantSection
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
  transverseDiagonal_ne_zero :
    (quadraticFamilyHessianMatrix family ell ell).coeff 0 ≠ 0
  hessianDefect_zero :
    HasPolynomialFamilyHessianDefect (K := K) family 0
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family
      (zeroPolynomialSection (K := K))
      rightSection
  rightSpecialPoint :
    polynomialSectionSpecialPoint rightSection =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)

/-- The origin Hessian of the right-recentered seam is nonzero.  In fact its
determinant is one; the nonzero formulation is the exact input expected by
the quadratic normalization theorem. -/
theorem rightRecentered_originHessian_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    quadraticFamilyHessianMatrix T.rightRecenteredSpecialFiber ≠ 0 := by
  have hdet :
      (quadraticFamilyHessianMatrix T.rightRecenteredSpecialFiber).det = 1 := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [T.rightRecenteredSpecialFiber_hessianDeterminant_eq_one]
    simp
  intro hzero
  rw [hzero] at hdet
  simp at hdet

/-- **G12 zero-clock transverse quadratic normalization.**

Every final seam admits an honest determinant-one source transvection that
preserves the marked collision and exposes a nonzero transverse diagonal
origin-Hessian coefficient at parameter layer zero. -/
theorem finalSeamTransverseQuadraticPivotFamily
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.FinalSeamTransverseQuadraticPivotFamily := by
  let F := T.rightRecenteredSpecialFiber
  let P := constantPolynomialFamily F

  have hspecial :
      polynomialFamilySpecialFiber P = F := by
    simpa [P] using polynomialFamilySpecialFiber_constantPolynomialFamily F

  have hH :
      quadraticFamilyHessianMatrix (familyParameterLayer P 0) ≠ 0 := by
    rw [familyParameterLayer_zero_eq_polynomialFamilySpecialFiber, hspecial]
    exact T.rightRecentered_originHessian_ne_zero

  rcases exists_axisPreservingShear_layerTransverseDiagonal_ne_zero
      (K := K) P 0 hH with
    ⟨k, ell, a, hkl, hell0, hdiag⟩

  let P' :=
    transverseSourceShearHom
      (K := K) k ell (Polynomial.C a) P
  let b :=
    polynomialConstantSection
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  let b' :=
    transverseSourceUnshearSection
      k ell (Polynomial.C a) b

  have hbaseDef :
      HasPolynomialFamilyHessianDefect (K := K) P 0 := by
    simpa [P, F] using
      constantPolynomialFamily_hasHessianDefect_zero
        F T.rightRecenteredSpecialFiber_hessianDeterminant_eq_one

  have hdef :
      HasPolynomialFamilyHessianDefect (K := K) P' 0 := by
    dsimp [P']
    exact transverseSourceShearHom_preservesHessianDefect
      (K := K) k ell hkl (Polynomial.C a) P hbaseDef

  have hbaseColl :
      HasPolynomialFamilyExactGradientCollision
        P
        (zeroPolynomialSection (K := K))
        b := by
    have h :=
      constantPolynomialFamily_exactGradientCollision
        F
        (fun _ : Fin 4 => (0 : K))
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
        T.rightRecenteredSpecialFiber_exactAxisCollision
    simpa [P, F, b, zeroPolynomialSection,
      polynomialConstantSection] using h

  have hcoll :
      HasPolynomialFamilyExactGradientCollision
        P'
        (zeroPolynomialSection (K := K))
        b' := by
    have h :=
      polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) k ell hkl (Polynomial.C a) P
        (zeroPolynomialSection (K := K)) b hbaseColl
    rw [transverseSourceUnshearSection_zero] at h
    simpa [P', b'] using h

  have hspecialPoint :
      polynomialSectionSpecialPoint b' =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    dsimp [b']
    apply polynomialSectionSpecialPoint_transverseUnshear_negAxis
      (K := K) k ell hell0 a b
    simp [b, polynomialSectionSpecialPoint,
      polynomialConstantSection]

  refine ⟨{
    k := k
    ell := ell
    a := a
    k_ne_ell := hkl
    ell_ne_zero := hell0
    family := P'
    rightSection := b'
    family_eq := rfl
    rightSection_eq := rfl
    transverseDiagonal_ne_zero := ?_
    hessianDefect_zero := hdef
    exactCollision := hcoll
    rightSpecialPoint := hspecialPoint
  }⟩
  simpa [P'] using hdiag

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
