import HC4.Toric.ClassifiedSupport

/-!
# Descent of the classified support alternatives

This module proves the final scalar-descent step in a coefficient-level form.
For an injective ring homomorphism, a normalised sparse potential belongs to
the `r` family (or the `s` family) after extending coefficients if and only if
it already belongs to that family over the original ring.
-/

namespace HC4.Toric

section RingHom

variable {K L : Type*} [CommRing K] [CommRing L]

/-- Coefficient extension associated with a ring homomorphism. -/
noncomputable def extendCoeffs (φ : K →+* L) (f : SparsePolynomial K) : SparsePolynomial L :=
  mapCoeffs φ φ.map_zero f

@[simp] theorem extendCoeffs_apply
    (φ : K →+* L) (f : SparsePolynomial K) (u : Exponent) :
    extendCoeffs φ f u = φ (f u) := by
  simp [extendCoeffs]

@[simp] theorem extendCoeffs_zero (φ : K →+* L) :
    extendCoeffs φ (0 : SparsePolynomial K) = 0 := by
  ext u
  simp [extendCoeffs]

@[simp] theorem extendCoeffs_add
    (φ : K →+* L) (f g : SparsePolynomial K) :
    extendCoeffs φ (f + g) = extendCoeffs φ f + extendCoeffs φ g := by
  ext u
  simp [extendCoeffs, mapCoeffs]

@[simp] theorem extendCoeffs_neg
    (φ : K →+* L) (f : SparsePolynomial K) :
    extendCoeffs φ (-f) = -extendCoeffs φ f := by
  ext u
  simp [extendCoeffs, mapCoeffs]

@[simp] theorem extendCoeffs_sub
    (φ : K →+* L) (f g : SparsePolynomial K) :
    extendCoeffs φ (f - g) = extendCoeffs φ f - extendCoeffs φ g := by
  ext u
  simp [extendCoeffs, mapCoeffs]

@[simp] theorem extendCoeffs_basePotential (φ : K →+* L) :
    extendCoeffs φ (basePotential : SparsePolynomial K) =
      (basePotential : SparsePolynomial L) := by
  classical
  ext u
  simp only [extendCoeffs_apply, basePotential, Finsupp.add_apply,
    Finsupp.single_apply]
  split_ifs <;> simp_all [pExponent, qExponent]

/-- Exact support preservation for an injective ring homomorphism. -/
theorem support_extendCoeffs_eq
    (φ : K →+* L) (hφ : Function.Injective φ) (f : SparsePolynomial K) :
    (extendCoeffs φ f).support = f.support := by
  exact support_mapCoeffs_eq φ φ.map_zero hφ f

/-- The normalised `r` classification descends through an injective scalar extension. -/
theorem normalisedRClassified_extendCoeffs_iff
    (φ : K →+* L) (hφ : Function.Injective φ)
    (a b : ℕ) (ψ : SparsePolynomial K) :
    IsNormalisedRClassified a b (extendCoeffs φ ψ) ↔
      IsNormalisedRClassified a b ψ := by
  constructor
  · rintro ⟨g, hg, hψ⟩
    let f : SparsePolynomial K := ψ - basePotential
    have hmap : extendCoeffs φ f = g := by
      dsimp [f]
      rw [extendCoeffs_sub, extendCoeffs_basePotential, hψ]
      abel
    refine ⟨f, ?_, ?_⟩
    · apply (isPureRCorrection_mapCoeffs_iff φ φ.map_zero hφ a b f).mp
      change IsPureRCorrection a b (extendCoeffs φ f)
      rw [hmap]
      exact hg
    · dsimp [f]
      abel
  · rintro ⟨f, hf, hψ⟩
    refine ⟨extendCoeffs φ f, ?_, ?_⟩
    · apply (isPureRCorrection_mapCoeffs_iff φ φ.map_zero hφ a b f).mpr
      exact hf
    · rw [hψ, extendCoeffs_add, extendCoeffs_basePotential]

/-- The normalised `s` classification descends through an injective scalar extension. -/
theorem normalisedSClassified_extendCoeffs_iff
    (φ : K →+* L) (hφ : Function.Injective φ)
    (a b : ℕ) (ψ : SparsePolynomial K) :
    IsNormalisedSClassified a b (extendCoeffs φ ψ) ↔
      IsNormalisedSClassified a b ψ := by
  constructor
  · rintro ⟨g, hg, hψ⟩
    let f : SparsePolynomial K := ψ - basePotential
    have hmap : extendCoeffs φ f = g := by
      dsimp [f]
      rw [extendCoeffs_sub, extendCoeffs_basePotential, hψ]
      abel
    refine ⟨f, ?_, ?_⟩
    · apply (isPureSCorrection_mapCoeffs_iff φ φ.map_zero hφ a b f).mp
      change IsPureSCorrection a b (extendCoeffs φ f)
      rw [hmap]
      exact hg
    · dsimp [f]
      abel
  · rintro ⟨f, hf, hψ⟩
    refine ⟨extendCoeffs φ f, ?_, ?_⟩
    · apply (isPureSCorrection_mapCoeffs_iff φ φ.map_zero hφ a b f).mpr
      exact hf
    · rw [hψ, extendCoeffs_add, extendCoeffs_basePotential]

/-- The disjunction of the two classified outcomes descends exactly. -/
theorem normalisedClassified_extendCoeffs_iff
    (φ : K →+* L) (hφ : Function.Injective φ)
    (a b : ℕ) (ψ : SparsePolynomial K) :
    (IsNormalisedRClassified a b (extendCoeffs φ ψ) ∨
      IsNormalisedSClassified a b (extendCoeffs φ ψ)) ↔
    (IsNormalisedRClassified a b ψ ∨ IsNormalisedSClassified a b ψ) := by
  rw [normalisedRClassified_extendCoeffs_iff φ hφ,
    normalisedSClassified_extendCoeffs_iff φ hφ]

end RingHom

end HC4.Toric
