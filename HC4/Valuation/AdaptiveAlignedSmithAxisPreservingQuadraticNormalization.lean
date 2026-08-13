import HC4.Valuation.AdaptiveAlignedSmithTransverseSourceShearQuadraticLayer
import Mathlib.Tactic

/-!
# Axis-preserving quadratic normalisation at direct closing

The first actual direct-closing layer is already known to have nonzero
source-origin Hessian.  A priori that curvature may sit entirely in the
marked row/column, so it is not legitimate to assume a nonzero transverse
`3 x 3` block.

The elementary source transvection

    X_k \mapsto X_k + a X_ell

has a better feature: to preserve the marked special point `-e_0`, it is
enough that the *added direction* `ell` be transverse.  The sheared coordinate
`k` itself may be the marked coordinate `0`.

This file proves that every nonzero quadratic parameter layer can therefore
be normalised, by an honest determinant-one source transvection preserving the
marked collision special point, to a nonzero square coefficient on some
transverse coordinate `ell ≠ 0`.  It then packages this for the direct-closing
case `firstActualLayerOrder = defect`, retaining the exact Hessian clock and
exact moving collision.

This is deliberately only a normalisation theorem.  It does not yet claim
that the resulting square is a fresh first-contact monomial, nor that the
canonical Smith support data is invariant under the shear.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- If the added direction of a source transvection has zero special
coordinate, inverse-shearing a moving section does not change its special
point.  The sheared coordinate itself may be arbitrary. -/
theorem polynomialSectionSpecialPoint_transverseUnshear_of_addedCoord_zero
    (k ell : Fin 4)
    (a : K)
    (s : Fin 4 -> Polynomial K)
    (hell : polynomialSectionSpecialPoint s ell = 0) :
    polynomialSectionSpecialPoint
        (transverseSourceUnshearSection k ell (Polynomial.C a) s) =
      polynomialSectionSpecialPoint s := by
  funext i
  by_cases hik : i = k
  · subst i
    have hell0 : (s ell).coeff 0 = 0 := by
      simpa [Polynomial.constantCoeff, polynomialSectionSpecialPoint] using hell
    simp [polynomialSectionSpecialPoint, transverseSourceUnshearSection,
      hell0]
  · simp [polynomialSectionSpecialPoint, transverseSourceUnshearSection, hik]

/-- In particular, a parameter-constant transvection whose added direction is
transverse preserves the marked special point `-e_0` exactly. -/
theorem polynomialSectionSpecialPoint_transverseUnshear_negAxis
    (k ell : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (a : K)
    (s : Fin 4 -> Polynomial K)
    (hspecial :
      polynomialSectionSpecialPoint s =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)) :
    polynomialSectionSpecialPoint
        (transverseSourceUnshearSection k ell (Polynomial.C a) s) =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  have hell : polynomialSectionSpecialPoint s ell = 0 := by
    rw [hspecial]
    simp [coordinateAxisPoint, hell0]
  rw [polynomialSectionSpecialPoint_transverseUnshear_of_addedCoord_zero
    k ell a s hell]
  exact hspecial

/-- Every nonzero source-origin Hessian parameter layer admits an honest
constant source transvection which makes a diagonal coefficient nonzero on a
*transverse* coordinate.

No assumption that the original nonzero entry lies in the transverse block is
needed.  If the only visible curvature is `H_{00}`, use the pair `(0, ell)`;
if it is a marked/transverse mixed entry, use that pair directly. -/
theorem exists_axisPreservingShear_layerTransverseDiagonal_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : Nat)
    (hH :
      quadraticFamilyHessianMatrix (familyParameterLayer P n) ≠ 0) :
    ∃ k ell : Fin 4, ∃ a : K,
      k ≠ ell ∧
      ell ≠ (0 : Fin 4) ∧
      (quadraticFamilyHessianMatrix
          (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
          ell ell).coeff n ≠ 0 := by
  have hexists :
      ∃ i r : Fin 4,
        quadraticFamilyHessianMatrix (familyParameterLayer P n) i r ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    apply hH
    apply Matrix.ext
    intro i r
    exact hnot i r
  rcases hexists with ⟨i, r, hir⟩
  have hirCoeff :
      (quadraticFamilyHessianMatrix P i r).coeff n ≠ 0 := by
    rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
    exact hir
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    by_cases hr0 : r = (0 : Fin 4)
    · subst r
      let ell : Fin 4 := 1
      have hell0 : ell ≠ (0 : Fin 4) := by
        simp [ell]
      have hkl : (0 : Fin 4) ≠ ell := Ne.symm hell0
      have hnz :
          (quadraticFamilyHessianMatrix P ell ell).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 ell).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 0).coeff n ≠ 0 := by
        exact Or.inr (Or.inr hirCoeff)
      rcases exists_constantTransverseShear_layerDiagonal_ne_zero
          (K := K) (0 : Fin 4) ell hkl P n hnz with ⟨a, ha⟩
      exact ⟨0, ell, a, hkl, hell0, ha⟩
    · have hkl : (0 : Fin 4) ≠ r := Ne.symm hr0
      have hnz :
          (quadraticFamilyHessianMatrix P r r).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 r).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 0).coeff n ≠ 0 := by
        exact Or.inr (Or.inl hirCoeff)
      rcases exists_constantTransverseShear_layerDiagonal_ne_zero
          (K := K) (0 : Fin 4) r hkl P n hnz with ⟨a, ha⟩
      exact ⟨0, r, a, hkl, hr0, ha⟩
  · by_cases hirEq : i = r
    · subst r
      have hkl : (0 : Fin 4) ≠ i := Ne.symm hi0
      have hnz :
          (quadraticFamilyHessianMatrix P i i).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 i).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P 0 0).coeff n ≠ 0 := by
        exact Or.inl hirCoeff
      rcases exists_constantTransverseShear_layerDiagonal_ne_zero
          (K := K) (0 : Fin 4) i hkl P n hnz with ⟨a, ha⟩
      exact ⟨0, i, a, hkl, hi0, ha⟩
    · have hkl : r ≠ i := Ne.symm hirEq
      have hriCoeff :
          (quadraticFamilyHessianMatrix P r i).coeff n ≠ 0 := by
        intro hzero
        apply hirCoeff
        rw [quadraticFamilyHessianMatrix_coeff_symmetric P n i r]
        exact hzero
      have hnz :
          (quadraticFamilyHessianMatrix P i i).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P r i).coeff n ≠ 0 ∨
          (quadraticFamilyHessianMatrix P r r).coeff n ≠ 0 := by
        exact Or.inr (Or.inl hriCoeff)
      rcases exists_constantTransverseShear_layerDiagonal_ne_zero
          (K := K) r i hkl P n hnz with ⟨a, ha⟩
      exact ⟨r, i, a, hkl, hi0, ha⟩

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : Nat}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- **Axis-preserving direct-closing quadratic normalisation.**

If the first actual layer closes exactly at the Hessian defect, then after an
honest parameter-constant determinant-one source transvection there is a
nonzero square Hessian coefficient at that same order on a transverse source
coordinate.  The transformed family retains the exact Hessian defect, the
exact moving gradient collision, and the marked special point `-e_0`.

This is the strongest coordinate-normalisation statement justified at this
stage; freshness of the square contact is a separate remaining issue. -/
theorem directClosing_exists_axisPreservingTransverseSquare
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    ∃ k ell : Fin 4, ∃ a : K,
      k ≠ ell ∧
      ell ≠ (0 : Fin 4) ∧
      (quadraticFamilyHessianMatrix
          (transverseSourceShearHom
            (K := K) k ell (Polynomial.C a) C.family)
          ell ell).coeff C.firstActualLayerOrder ≠ 0 ∧
      HasPolynomialFamilyHessianDefect (K := K)
        (transverseSourceShearHom
          (K := K) k ell (Polynomial.C a) C.family)
        B.aligned.endpoint.defect ∧
      HasPolynomialFamilyExactGradientCollision
        (transverseSourceShearHom
          (K := K) k ell (Polynomial.C a) C.family)
        (zeroPolynomialSection (K := K))
        (transverseSourceUnshearSection
          k ell (Polynomial.C a)
          B.aligned.endpoint.rightRecenteredRightSection) ∧
      polynomialSectionSpecialPoint
        (transverseSourceUnshearSection
          k ell (Polynomial.C a)
          B.aligned.endpoint.rightRecenteredRightSection) =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  have hH := C.firstActualLayer_originHessian_ne_zero_of_eq_defect heq
  rcases exists_axisPreservingShear_layerTransverseDiagonal_ne_zero
      (K := K) C.family C.firstActualLayerOrder hH with
    ⟨k, ell, a, hkl, hell0, hdiag⟩
  refine ⟨k, ell, a, hkl, hell0, hdiag, ?_, ?_, ?_⟩
  · exact transverseSourceShearHom_preservesHessianDefect
      (K := K) k ell hkl (Polynomial.C a) C.family C.family_hessianDefect
  · have hcoll :=
      polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) k ell hkl (Polynomial.C a) C.family
        (zeroPolynomialSection (K := K))
        B.aligned.endpoint.rightRecenteredRightSection
        C.family_exactCollision
    simpa [transverseSourceUnshearSection_zero] using hcoll
  · exact polynomialSectionSpecialPoint_transverseUnshear_negAxis
      (K := K) k ell hell0 a
      B.aligned.endpoint.rightRecenteredRightSection
      B.aligned.endpoint.rightRecenteredRightSection_specialPoint

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
