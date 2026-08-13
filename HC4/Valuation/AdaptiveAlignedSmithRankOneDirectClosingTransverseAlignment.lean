import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingKernelAxisFrontier
import HC4.Valuation.AdaptiveAlignedSmithAxisPreservingQuadraticNormalization
import Mathlib.Tactic

/-!
# Transverse kernel alignment at direct rank-one closing

The green kernel-axis frontier leaves one genuinely transverse case at
`j = Delta`: a nonzero vector `v` with a transverse coordinate `v ell != 0`,

    H_0 v = 0,
    v^T H_j v != 0.

Because `ell != 0`, the normalized vector `v / v_ell` can be obtained from
`e_ell` by three determinant-one source transvections, all using the same
*added* direction `ell`.  Such transvections preserve the marked point
`-e_0`, even when one of the sheared coordinates is `0`.

This file packages that alignment at the honest polynomial-family level.
The resulting family retains

* the exact Hessian defect;
* the exact moving gradient collision;
* the marked special point `-e_0`;
* a transverse square coefficient whose constant term vanishes, whose
  coefficient at the direct-closing order is nonzero, and whose exact
  parameter order is therefore precisely `j`.

Thus the remaining equality branch has an honest coordinate fresh square
on a source-equivalent closing family.  The next interface is purely the
transport/exposure step into the first-contact lattice.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Two missing one-shear Hessian entry formulas -/

/-- Away from the added direction `ell`, the mixed `i,ell` Hessian entry
acquires the expected `i,k` term under `X_k -> X_k + c X_ell`. -/
theorem quadraticFamilyHessianMatrix_transverseSourceShear_iell
    (k ell i : Fin 4)
    (hkl : k ≠ ell)
    (hil : i ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell c P) i ell =
      quadraticFamilyHessianMatrix P i ell +
        c * quadraticFamilyHessianMatrix P i k := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv ell
          (MvPolynomial.pderiv i
            (transverseSourceShearHom (K := K) k ell c P))) = _
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c i hil P]
  rw [pderiv_source_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv i P)]
  simp only [map_add, map_mul]
  rw [constantCoeff_transverseSourceShearHom
      k ell hkl c (MvPolynomial.pderiv ell (MvPolynomial.pderiv i P))]
  rw [constantCoeff_transverseSourceShearHom
      k ell hkl c (MvPolynomial.pderiv k (MvPolynomial.pderiv i P))]
  simp

/-- If both Hessian indices avoid the added direction, the source-origin
entry is unchanged by the transvection. -/
theorem quadraticFamilyHessianMatrix_transverseSourceShear_ij_of_ne_added
    (k ell i r : Fin 4)
    (hkl : k ≠ ell)
    (hil : i ≠ ell)
    (hrl : r ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell c P) i r =
      quadraticFamilyHessianMatrix P i r := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv r
          (MvPolynomial.pderiv i
            (transverseSourceShearHom (K := K) k ell c P))) = _
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c i hil P]
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c r hrl (MvPolynomial.pderiv i P)]
  exact constantCoeff_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv r (MvPolynomial.pderiv i P))

/-- Parameter-layer form of the generic mixed-entry identity. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    (k ell i : Fin 4)
    (hkl : k ≠ ell)
    (hil : i ≠ ell)
    (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        i ell).coeff n =
      (quadraticFamilyHessianMatrix P i ell).coeff n +
        a * (quadraticFamilyHessianMatrix P i k).coeff n := by
  rw [quadraticFamilyHessianMatrix_transverseSourceShear_iell
    k ell i hkl hil (Polynomial.C a) P]
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- Parameter-layer form of the away-from-`ell` invariance. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
    (k ell i r : Fin 4)
    (hkl : k ≠ ell)
    (hil : i ≠ ell)
    (hrl : r ≠ ell)
    (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        i r).coeff n =
      (quadraticFamilyHessianMatrix P i r).coeff n := by
  rw [quadraticFamilyHessianMatrix_transverseSourceShear_ij_of_ne_added
    k ell i r hkl hil hrl (Polynomial.C a) P]

/-! ## Canonical three-transvection alignment -/

/-- Three constant source transvections with common added direction `ell`.
The order is fixed only to make the Lean term canonical. -/
def tripleTransverseSourceShearFamily
    (k₁ k₂ k₃ ell : Fin 4)
    (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  transverseSourceShearHom (K := K) k₃ ell (Polynomial.C a₃)
    (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
      (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P))

/-- Sequential inverse action of the same three transvections on a moving
section. -/
def tripleTransverseSourceUnshearSection
    (k₁ k₂ k₃ ell : Fin 4)
    (a₁ a₂ a₃ : K)
    (s : Fin 4 → Polynomial K) : Fin 4 → Polynomial K :=
  transverseSourceUnshearSection k₃ ell (Polynomial.C a₃)
    (transverseSourceUnshearSection k₂ ell (Polynomial.C a₂)
      (transverseSourceUnshearSection k₁ ell (Polynomial.C a₁) s))

@[simp] theorem tripleTransverseSourceUnshearSection_zero
    (k₁ k₂ k₃ ell : Fin 4)
    (a₁ a₂ a₃ : K) :
    tripleTransverseSourceUnshearSection
        k₁ k₂ k₃ ell a₁ a₂ a₃ (zeroPolynomialSection (K := K)) =
      zeroPolynomialSection (K := K) := by
  simp [tripleTransverseSourceUnshearSection,
    transverseSourceUnshearSection_zero]

/-- The three-transvection alignment preserves the exact Hessian defect. -/
theorem tripleTransverseSourceShearFamily_preservesHessianDefect
    (k₁ k₂ k₃ ell : Fin 4)
    (hk₁ : k₁ ≠ ell)
    (hk₂ : k₂ ≠ ell)
    (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ P) Delta := by
  have h1 := transverseSourceShearHom_preservesHessianDefect
    (K := K) k₁ ell hk₁ (Polynomial.C a₁) P hdef
  have h2 := transverseSourceShearHom_preservesHessianDefect
    (K := K) k₂ ell hk₂ (Polynomial.C a₂)
      (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P) h1
  have h3 := transverseSourceShearHom_preservesHessianDefect
    (K := K) k₃ ell hk₃ (Polynomial.C a₃)
      (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
        (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P)) h2
  simpa [tripleTransverseSourceShearFamily] using h3

/-- The three-transvection alignment preserves an exact zero-left moving
collision. -/
theorem polynomialFamilyExactGradientCollision_tripleTransverseSourceShear
    (k₁ k₂ k₃ ell : Fin 4)
    (hk₁ : k₁ ≠ ell)
    (hk₂ : k₂ ≠ ell)
    (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hcoll : HasPolynomialFamilyExactGradientCollision
      P (zeroPolynomialSection (K := K)) b) :
    HasPolynomialFamilyExactGradientCollision
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ P)
      (zeroPolynomialSection (K := K))
      (tripleTransverseSourceUnshearSection
        k₁ k₂ k₃ ell a₁ a₂ a₃ b) := by
  have h1 := polynomialFamilyExactGradientCollision_transverseSourceShear
    (K := K) k₁ ell hk₁ (Polynomial.C a₁)
      P (zeroPolynomialSection (K := K)) b hcoll
  rw [transverseSourceUnshearSection_zero] at h1
  have h2 := polynomialFamilyExactGradientCollision_transverseSourceShear
    (K := K) k₂ ell hk₂ (Polynomial.C a₂)
      (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P)
      (zeroPolynomialSection (K := K))
      (transverseSourceUnshearSection k₁ ell (Polynomial.C a₁) b) h1
  rw [transverseSourceUnshearSection_zero] at h2
  have h3 := polynomialFamilyExactGradientCollision_transverseSourceShear
    (K := K) k₃ ell hk₃ (Polynomial.C a₃)
      (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
        (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P))
      (zeroPolynomialSection (K := K))
      (transverseSourceUnshearSection k₂ ell (Polynomial.C a₂)
        (transverseSourceUnshearSection k₁ ell (Polynomial.C a₁) b)) h2
  rw [transverseSourceUnshearSection_zero] at h3
  simpa [tripleTransverseSourceShearFamily,
    tripleTransverseSourceUnshearSection] using h3

/-- If the common added direction is transverse, all three inverse
transvections preserve the marked point `-e₀`. -/
theorem polynomialSectionSpecialPoint_tripleTransverseUnshear_negAxis
    (k₁ k₂ k₃ ell : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (a₁ a₂ a₃ : K)
    (s : Fin 4 → Polynomial K)
    (hspecial :
      polynomialSectionSpecialPoint s =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)) :
    polynomialSectionSpecialPoint
        (tripleTransverseSourceUnshearSection
          k₁ k₂ k₃ ell a₁ a₂ a₃ s) =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  have h1 := polynomialSectionSpecialPoint_transverseUnshear_negAxis
    (K := K) k₁ ell hell0 a₁ s hspecial
  have h2 := polynomialSectionSpecialPoint_transverseUnshear_negAxis
    (K := K) k₂ ell hell0 a₂
      (transverseSourceUnshearSection k₁ ell (Polynomial.C a₁) s) h1
  have h3 := polynomialSectionSpecialPoint_transverseUnshear_negAxis
    (K := K) k₃ ell hell0 a₃
      (transverseSourceUnshearSection k₂ ell (Polynomial.C a₂)
        (transverseSourceUnshearSection k₁ ell (Polynomial.C a₁) s)) h2
  simpa [tripleTransverseSourceUnshearSection] using h3

/-! ## Exact diagonal formula for the triple alignment -/

/-- Exact parameter-layer diagonal after three shears with common added
coordinate.  This is the quadratic form on
`e_ell + a₁ e_k₁ + a₂ e_k₂ + a₃ e_k₃`, written entrywise. -/
theorem quadraticFamilyHessianMatrix_coeff_tripleTransverseSourceShear_ellell
    (k₁ k₂ k₃ ell : Fin 4)
    (hk₁ : k₁ ≠ ell)
    (hk₂ : k₂ ≠ ell)
    (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (tripleTransverseSourceShearFamily
          k₁ k₂ k₃ ell a₁ a₂ a₃ P)
        ell ell).coeff n =
      (quadraticFamilyHessianMatrix P ell ell).coeff n +
      a₁ * (quadraticFamilyHessianMatrix P k₁ ell).coeff n +
      a₁ * (quadraticFamilyHessianMatrix P ell k₁).coeff n +
      a₁ * a₁ * (quadraticFamilyHessianMatrix P k₁ k₁).coeff n +
      a₂ * (quadraticFamilyHessianMatrix P k₂ ell).coeff n +
      a₂ * (quadraticFamilyHessianMatrix P ell k₂).coeff n +
      a₂ * a₂ * (quadraticFamilyHessianMatrix P k₂ k₂).coeff n +
      a₃ * (quadraticFamilyHessianMatrix P k₃ ell).coeff n +
      a₃ * (quadraticFamilyHessianMatrix P ell k₃).coeff n +
      a₃ * a₃ * (quadraticFamilyHessianMatrix P k₃ k₃).coeff n +
      a₁ * a₂ * (quadraticFamilyHessianMatrix P k₁ k₂).coeff n +
      a₂ * a₁ * (quadraticFamilyHessianMatrix P k₂ k₁).coeff n +
      a₁ * a₃ * (quadraticFamilyHessianMatrix P k₁ k₃).coeff n +
      a₃ * a₁ * (quadraticFamilyHessianMatrix P k₃ k₁).coeff n +
      a₂ * a₃ * (quadraticFamilyHessianMatrix P k₂ k₃).coeff n +
      a₃ * a₂ * (quadraticFamilyHessianMatrix P k₃ k₂).coeff n := by
  let P₁ := transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁) P
  let P₂ := transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂) P₁
  change
    (quadraticFamilyHessianMatrix
      (transverseSourceShearHom (K := K) k₃ ell (Polynomial.C a₃) P₂)
      ell ell).coeff n = _
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
    k₃ ell hk₃ a₃ P₂ n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
    k₂ ell hk₂ a₂ P₁ n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    k₂ ell k₃ hk₂ hk₃ a₂ P₁ n]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P₂ n ell k₃]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    k₂ ell k₃ hk₂ hk₃ a₂ P₁ n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
    k₂ ell k₃ k₃ hk₂ hk₃ hk₃ a₂ P₁ n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
    k₁ ell hk₁ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    k₁ ell k₂ hk₁ hk₂ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P₁ n ell k₂]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    k₁ ell k₂ hk₁ hk₂ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
    k₁ ell k₂ k₂ hk₁ hk₂ hk₂ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_iell
    k₁ ell k₃ hk₁ hk₃ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
    k₁ ell k₃ k₂ hk₁ hk₃ hk₂ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ij_of_ne_added
    k₁ ell k₃ k₃ hk₁ hk₃ hk₃ a₁ P n]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n ell k₁]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n ell k₂]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n ell k₃]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n k₁ k₂]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n k₁ k₃]
  rw [quadraticFamilyHessianMatrix_coeff_symmetric P n k₂ k₃]
  ring

/-- Generic diagonal Hessian/square-coefficient relation, now for an arbitrary
polynomial family rather than only the canonical closing carrier. -/
theorem sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff_generic
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (i : Fin 4) :
    sourceOriginHessianLayer P n i i =
      2 * (MvPolynomial.coeff
        (AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i i) P).coeff n := by
  rw [sourceOriginHessianLayer_apply]
  rw [quadraticFamilyHessianMatrix_coeff_familyParameterLayer]
  rw [quadraticFamilyHessianMatrix_entry_eq_quadraticCoefficient]
  rw [familyParameterLayer_coeff]
  simp [AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent]
  ring

/-! ## Packaged transverse aligned closing source -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Data of an honest transverse alignment of the direct-closing kernel.
The aligned family is definitionally a three-transvection source-equivalent
copy of the original closing family. -/
structure DirectClosingTransverseAlignedSquareData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  ell : Fin 4
  ell_ne_zero : ell ≠ (0 : Fin 4)
  k₁ : Fin 4
  k₂ : Fin 4
  k₃ : Fin 4
  k₁_ne_ell : k₁ ≠ ell
  k₂_ne_ell : k₂ ≠ ell
  k₃_ne_ell : k₃ ≠ ell
  a₁ : K
  a₂ : K
  a₃ : K
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)
      B.aligned.endpoint.defect
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)
      (zeroPolynomialSection (K := K))
      (tripleTransverseSourceUnshearSection
        k₁ k₂ k₃ ell a₁ a₂ a₃
        B.aligned.endpoint.rightRecenteredRightSection)
  rightSpecialPoint :
    polynomialSectionSpecialPoint
      (tripleTransverseSourceUnshearSection
        k₁ k₂ k₃ ell a₁ a₂ a₃
        B.aligned.endpoint.rightRecenteredRightSection) =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  squareCoeff_zero :
    (MvPolynomial.coeff (directClosingQuadraticExponent ell ell)
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)).coeff 0 = 0
  squareCoeff_first_ne :
    (MvPolynomial.coeff (directClosingQuadraticExponent ell ell)
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)).coeff
          C.firstActualLayerOrder ≠ 0
  squareCoeff_lower_zero :
    ∀ n : ℕ, 0 < n → n < C.firstActualLayerOrder →
      (MvPolynomial.coeff (directClosingQuadraticExponent ell ell)
        (tripleTransverseSourceShearFamily
          k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)).coeff n = 0
  squareOrder :
    smithFamilyCoefficientOrder
      (tripleTransverseSourceShearFamily
        k₁ k₂ k₃ ell a₁ a₂ a₃ C.family)
      (directClosingQuadraticExponent ell ell) =
        C.firstActualLayerOrder

namespace DirectClosingTransverseAlignedSquareData

/-- The aligned source family. -/
noncomputable def family
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingTransverseAlignedSquareData C) :=
  tripleTransverseSourceShearFamily
    D.k₁ D.k₂ D.k₃ D.ell D.a₁ D.a₂ D.a₃ C.family

/-- The inverse-transformed right moving section. -/
noncomputable def rightSection
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingTransverseAlignedSquareData C) :=
  tripleTransverseSourceUnshearSection
    D.k₁ D.k₂ D.k₃ D.ell D.a₁ D.a₂ D.a₃
    B.aligned.endpoint.rightRecenteredRightSection

end DirectClosingTransverseAlignedSquareData

/-- Exact order extraction from a fresh square coefficient with all positive
coefficients below `j` zero. -/
private theorem smithFamilyCoefficientOrder_eq_of_fresh_coeff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (j : ℕ)
    (h0 : (MvPolynomial.coeff d P).coeff 0 = 0)
    (hj : (MvPolynomial.coeff d P).coeff j ≠ 0)
    (hlower : ∀ n : ℕ, 0 < n → n < j →
      (MvPolynomial.coeff d P).coeff n = 0) :
    smithFamilyCoefficientOrder P d = j := by
  have hc : MvPolynomial.coeff d P ≠ 0 := by
    intro hz
    rw [hz] at hj
    simp at hj
  have hd : d ∈ P.support := MvPolynomial.mem_support_iff.mpr hc
  rw [smithFamilyCoefficientOrder_eq P hd]
  unfold smithFamilyCoefficientParameterOrder
  let hc' : MvPolynomial.coeff d P ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := polynomialParameterOrder (MvPolynomial.coeff d P) hc'
  have hqle : q ≤ j := by
    exact polynomialParameterOrder_le_of_coeff_ne_zero
      (MvPolynomial.coeff d P) hc' hj
  have hqcoeff : (MvPolynomial.coeff d P).coeff q ≠ 0 := by
    exact polynomialParameterOrder_coeff_ne_zero (MvPolynomial.coeff d P) hc'
  have hjle : j ≤ q := by
    by_contra hnot
    have hqj : q < j := Nat.lt_of_not_ge hnot
    by_cases hq0 : q = 0
    · rw [hq0] at hqcoeff
      exact hqcoeff h0
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      exact hqcoeff (hlower q hqpos hqj)
  exact Nat.le_antisymm hqle hjle

/-- A transverse fresh kernel vector can be aligned by three marked-axis
preserving transvections to an honest transverse square whose exact parameter
order is `j`. -/
theorem exists_transverseAlignedSquare_of_kernelFresh
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (v : Fin 4 → K)
    (ell : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (hvell : v ell ≠ 0)
    (hker : (sourceOriginHessianLayer C.family 0).mulVec v = 0)
    (hfresh : dotProduct v
      ((sourceOriginHessianLayer C.family C.firstActualLayerOrder).mulVec v) ≠ 0) :
    Nonempty (DirectClosingTransverseAlignedSquareData C) := by
  have hq0 :
      dotProduct v ((sourceOriginHessianLayer C.family 0).mulVec v) = 0 := by
    rw [hker]
    simp [dotProduct]

  have build
      (k₁ k₂ k₃ : Fin 4)
      (hk₁ : k₁ ≠ ell)
      (hk₂ : k₂ ≠ ell)
      (hk₃ : k₃ ≠ ell)
      (hcover :
        ∀ n : ℕ,
          v ell * v ell *
              (quadraticFamilyHessianMatrix
                (tripleTransverseSourceShearFamily
                  k₁ k₂ k₃ ell
                    (v k₁ / v ell) (v k₂ / v ell) (v k₃ / v ell)
                    C.family)
                ell ell).coeff n =
            dotProduct v ((sourceOriginHessianLayer C.family n).mulVec v)) :
      Nonempty (DirectClosingTransverseAlignedSquareData C) := by
    let a₁ := v k₁ / v ell
    let a₂ := v k₂ / v ell
    let a₃ := v k₃ / v ell
    let Q := tripleTransverseSourceShearFamily
      k₁ k₂ k₃ ell a₁ a₂ a₃ C.family
    let b := tripleTransverseSourceUnshearSection
      k₁ k₂ k₃ ell a₁ a₂ a₃
      B.aligned.endpoint.rightRecenteredRightSection
    let d := directClosingQuadraticExponent ell ell

    have hvell2 : v ell * v ell ≠ 0 := mul_ne_zero hvell hvell
    have hdiag0 : (quadraticFamilyHessianMatrix Q ell ell).coeff 0 = 0 := by
      have hs := hcover 0
      change v ell * v ell *
          (quadraticFamilyHessianMatrix Q ell ell).coeff 0 = _ at hs
      rw [hq0] at hs
      exact (mul_eq_zero.mp hs).resolve_left hvell2
    have hdiagj :
        (quadraticFamilyHessianMatrix Q ell ell).coeff
            C.firstActualLayerOrder ≠ 0 := by
      intro hz
      apply hfresh
      have hs := hcover C.firstActualLayerOrder
      change v ell * v ell *
          (quadraticFamilyHessianMatrix Q ell ell).coeff
            C.firstActualLayerOrder = _ at hs
      rw [hz] at hs
      simpa using hs.symm
    have hdiagLower : ∀ n : ℕ, 0 < n → n < C.firstActualLayerOrder →
        (quadraticFamilyHessianMatrix Q ell ell).coeff n = 0 := by
      intro n hnpos hnlt
      have hHn := C.sourceOriginHessianLayer_eq_zero_of_pos_lt_firstActual
        hnpos hnlt
      have hq :
          dotProduct v ((sourceOriginHessianLayer C.family n).mulVec v) = 0 := by
        rw [hHn]
        simp [dotProduct, Matrix.mulVec]
      have hs := hcover n
      change v ell * v ell *
          (quadraticFamilyHessianMatrix Q ell ell).coeff n = _ at hs
      rw [hq] at hs
      exact (mul_eq_zero.mp hs).resolve_left hvell2

    have hcoeff0 : (MvPolynomial.coeff d Q).coeff 0 = 0 := by
      have h := sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff_generic
        (K := K) Q 0 ell
      rw [sourceOriginHessianLayer_apply] at h
      change
        (quadraticFamilyHessianMatrix Q ell ell).coeff 0 =
          2 * (MvPolynomial.coeff d Q).coeff 0 at h
      rw [hdiag0] at h
      have htwo : (2 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h.symm).resolve_left htwo
    have hcoeffj :
        (MvPolynomial.coeff d Q).coeff C.firstActualLayerOrder ≠ 0 := by
      intro hz
      apply hdiagj
      have h := sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff_generic
        (K := K) Q C.firstActualLayerOrder ell
      rw [sourceOriginHessianLayer_apply] at h
      change
        (quadraticFamilyHessianMatrix Q ell ell).coeff C.firstActualLayerOrder =
          2 * (MvPolynomial.coeff d Q).coeff C.firstActualLayerOrder at h
      rw [hz] at h
      simpa using h
    have hcoeffLower : ∀ n : ℕ, 0 < n → n < C.firstActualLayerOrder →
        (MvPolynomial.coeff d Q).coeff n = 0 := by
      intro n hnpos hnlt
      have h := sourceOriginHessianLayer_diag_eq_two_mul_squareCoeff_generic
        (K := K) Q n ell
      rw [sourceOriginHessianLayer_apply] at h
      change
        (quadraticFamilyHessianMatrix Q ell ell).coeff n =
          2 * (MvPolynomial.coeff d Q).coeff n at h
      rw [hdiagLower n hnpos hnlt] at h
      have htwo : (2 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h.symm).resolve_left htwo
    have horder : smithFamilyCoefficientOrder Q d = C.firstActualLayerOrder := by
      exact smithFamilyCoefficientOrder_eq_of_fresh_coeff
        Q d C.firstActualLayerOrder hcoeff0 hcoeffj hcoeffLower

    refine ⟨{
      ell := ell
      ell_ne_zero := hell0
      k₁ := k₁
      k₂ := k₂
      k₃ := k₃
      k₁_ne_ell := hk₁
      k₂_ne_ell := hk₂
      k₃_ne_ell := hk₃
      a₁ := a₁
      a₂ := a₂
      a₃ := a₃
      hessianDefect := ?_
      exactCollision := ?_
      rightSpecialPoint := ?_
      squareCoeff_zero := ?_
      squareCoeff_first_ne := ?_
      squareCoeff_lower_zero := ?_
      squareOrder := ?_
    }⟩
    · exact tripleTransverseSourceShearFamily_preservesHessianDefect
        (K := K) k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
        C.family C.family_hessianDefect
    · exact polynomialFamilyExactGradientCollision_tripleTransverseSourceShear
        (K := K) k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
        C.family B.aligned.endpoint.rightRecenteredRightSection
        C.family_exactCollision
    · exact polynomialSectionSpecialPoint_tripleTransverseUnshear_negAxis
        (K := K) k₁ k₂ k₃ ell hell0 a₁ a₂ a₃
        B.aligned.endpoint.rightRecenteredRightSection
        B.aligned.endpoint.rightRecenteredRightSection_specialPoint
    · simpa [Q, d] using hcoeff0
    · simpa [Q, d] using hcoeffj
    · intro n hnpos hnlt
      simpa [Q, d] using hcoeffLower n hnpos hnlt
    · simpa [Q, d] using horder

  fin_cases ell
  · exact False.elim (hell0 rfl)
  · apply build (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide)
    intro n
    change
      v (1 : Fin 4) * v (1 : Fin 4) *
          (quadraticFamilyHessianMatrix
            (tripleTransverseSourceShearFamily
              (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
              (v 0 / v 1) (v 2 / v 1) (v 3 / v 1) C.family)
            (1 : Fin 4) (1 : Fin 4)).coeff n =
        dotProduct v ((sourceOriginHessianLayer C.family n).mulVec v)
    rw [quadraticFamilyHessianMatrix_coeff_tripleTransverseSourceShear_ellell
      (K := K) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
      (by decide) (by decide) (by decide)
      (v 0 / v 1) (v 2 / v 1) (v 3 / v 1) C.family n]
    simp [sourceOriginHessianLayer_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    have hv1 : v (1 : Fin 4) ≠ 0 := by
      simpa using hvell
    field_simp [hv1] <;> ring
  · apply build (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide)
    intro n
    change
      v (2 : Fin 4) * v (2 : Fin 4) *
          (quadraticFamilyHessianMatrix
            (tripleTransverseSourceShearFamily
              (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
              (v 0 / v 2) (v 1 / v 2) (v 3 / v 2) C.family)
            (2 : Fin 4) (2 : Fin 4)).coeff n =
        dotProduct v ((sourceOriginHessianLayer C.family n).mulVec v)
    rw [quadraticFamilyHessianMatrix_coeff_tripleTransverseSourceShear_ellell
      (K := K) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide)
      (v 0 / v 2) (v 1 / v 2) (v 3 / v 2) C.family n]
    simp [sourceOriginHessianLayer_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    have hv2 : v (2 : Fin 4) ≠ 0 := by
      simpa using hvell
    field_simp [hv2] <;> ring
  · apply build (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (by decide) (by decide) (by decide)
    intro n
    change
      v (3 : Fin 4) * v (3 : Fin 4) *
          (quadraticFamilyHessianMatrix
            (tripleTransverseSourceShearFamily
              (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
              (v 0 / v 3) (v 1 / v 3) (v 2 / v 3) C.family)
            (3 : Fin 4) (3 : Fin 4)).coeff n =
        dotProduct v ((sourceOriginHessianLayer C.family n).mulVec v)
    rw [quadraticFamilyHessianMatrix_coeff_tripleTransverseSourceShear_ellell
      (K := K) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide)
      (v 0 / v 3) (v 1 / v 3) (v 2 / v 3) C.family n]
    simp [sourceOriginHessianLayer_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    have hv3 : v (3 : Fin 4) ≠ 0 := by
      simpa using hvell
    field_simp [hv3] <;> ring

/-- **Direct-closing transverse alignment frontier.**

At equality `j = Delta`, either the original coordinates already contain a
fresh longitudinal square, or there is an honest marked-axis-preserving
source-equivalent family carrying a transverse square of exact parameter
order `j`. -/
theorem directClosing_freshLongitudinalSquare_or_transverseAlignedSquare
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.HasFreshDirectClosingSquareAt (0 : Fin 4) ∨
      Nonempty (DirectClosingTransverseAlignedSquareData C) := by
  rcases C.directClosing_freshLongitudinalSquare_or_transverseKernelFresh heq with
    hlong | htrans
  · exact Or.inl hlong
  · rcases htrans with ⟨v, ell, _hvne, hell0, hvell, hker, hfresh⟩
    exact Or.inr
      (C.exists_transverseAlignedSquare_of_kernelFresh
        v ell hell0 hvell hker hfresh)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
