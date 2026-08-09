import HC4.Toric.SparseEigenSupport

/-!
# Coefficient extension and support descent

The final step of the symmetric-gradings argument extends scalars to an
algebraic closure, classifies the monomial support there, and then descends the
support statement to the original field.  This module isolates the exact
finite-support fact needed for that step: an injective coefficient map neither
creates nor removes supported exponent vectors.
-/

namespace HC4.Toric

/-- Apply a zero-preserving map to every coefficient of a sparse polynomial. -/
noncomputable def mapCoeffs
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (f : SparsePolynomial K) : SparsePolynomial L :=
  f.mapRange φ hφ0

@[simp] theorem mapCoeffs_apply
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (f : SparsePolynomial K) (u : Exponent) :
    mapCoeffs φ hφ0 f u = φ (f u) := by
  simp [mapCoeffs]

/-- An injective coefficient map preserves support exactly. -/
theorem support_mapCoeffs_eq
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (f : SparsePolynomial K) :
    (mapCoeffs φ hφ0 f).support = f.support := by
  exact Finsupp.support_mapRange_of_injective hφ0 f hφ

/-- Balanced support is unchanged by injective scalar extension. -/
theorem hasBalancedSupport_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (a b : ℕ) (f : SparsePolynomial K) :
    HasBalancedSupport a b (mapCoeffs φ hφ0 f) ↔
      HasBalancedSupport a b f := by
  unfold HasBalancedSupport
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

/-- Constant-character support is unchanged by injective scalar extension. -/
theorem hasSupportCharacter_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (c : ℤ) (f : SparsePolynomial K) :
    HasSupportCharacter c (mapCoeffs φ hφ0 f) ↔
      HasSupportCharacter c f := by
  unfold HasSupportCharacter
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

/-- Fixed `r`-level support descends and ascends through an injective coefficient map. -/
theorem sparseOnRLevel_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (a b k : ℕ) (f : SparsePolynomial K) :
    SparseOnRLevel a b k (mapCoeffs φ hφ0 f) ↔
      SparseOnRLevel a b k f := by
  unfold SparseOnRLevel
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

/-- Fixed `s`-level support descends and ascends through an injective coefficient map. -/
theorem sparseOnSLevel_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (a b k : ℕ) (f : SparsePolynomial K) :
    SparseOnSLevel a b k (mapCoeffs φ hφ0 f) ↔
      SparseOnSLevel a b k f := by
  unfold SparseOnSLevel
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

/-- Support in the `p,q` cone descends and ascends through scalar extension. -/
theorem sparseOnPQCone_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (f : SparsePolynomial K) :
    SparseOnPQCone (mapCoeffs φ hφ0 f) ↔ SparseOnPQCone f := by
  unfold SparseOnPQCone
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

end HC4.Toric
