import HC4.Toric.CoefficientDescent
import HC4.Toric.SupportIntersection

/-!
# Sparse support of the two classified families

The two final families have nonlinear support on positive pure powers of `r`
or positive pure powers of `s`.  This module packages those support conditions,
proves that the two correction spaces meet only at zero, and gives the exact
support-level form of the statement that the two alternatives overlap only at
the quadratic base.
-/

namespace HC4.Toric

/-- The zero exponent, corresponding to an additive constant. -/
def zeroExponent : Exponent := ⟨0, 0, 0, 0⟩

/-- A sparse correction supported on positive pure powers of `r`. -/
def IsPureRCorrection
    {K : Type*} [Zero K] (a b : ℕ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, ∃ k : ℕ, 0 < k ∧ u = rBranch a b 0 0 k

/-- A sparse correction supported on positive pure powers of `s`. -/
def IsPureSCorrection
    {K : Type*} [Zero K] (a b : ℕ) (f : SparsePolynomial K) : Prop :=
  ∀ u ∈ f.support, ∃ k : ℕ, 0 < k ∧ u = sBranch a b 0 0 k

/-- The normalised quadratic base `p + q`. -/
noncomputable def basePotential
    {K : Type*} [Semiring K] : SparsePolynomial K :=
  Finsupp.single pExponent 1 + Finsupp.single qExponent 1

/-- A normalised sparse potential in the classified `r` family. -/
def IsNormalisedRClassified
    {K : Type*} [CommRing K] (a b : ℕ) (ψ : SparsePolynomial K) : Prop :=
  ∃ f : SparsePolynomial K,
    IsPureRCorrection a b f ∧ ψ = basePotential + f

/-- A normalised sparse potential in the classified `s` family. -/
def IsNormalisedSClassified
    {K : Type*} [CommRing K] (a b : ℕ) (ψ : SparsePolynomial K) : Prop :=
  ∃ f : SparsePolynomial K,
    IsPureSCorrection a b f ∧ ψ = basePotential + f

/-- No nonzero sparse correction can be supported on both positive pure branches. -/
theorem pure_r_s_correction_eq_zero
    {K : Type*} [Zero K]
    {a b : ℕ} (hb : 0 < b) {f : SparsePolynomial K}
    (hR : IsPureRCorrection a b f) (hS : IsPureSCorrection a b f) :
    f = 0 := by
  ext u
  by_contra hne
  have hu : u ∈ f.support := by
    simpa [Finsupp.mem_support_iff] using hne
  rcases hR u hu with ⟨k, hk, huR⟩
  rcases hS u hu with ⟨l, hl, huS⟩
  have hEq : rBranch a b 0 0 k = sBranch a b 0 0 l := huR.symm.trans huS
  exact (rBranch_ne_positive_sBranch hb hl) hEq

/-- The two normalised classified alternatives overlap only at `p + q`. -/
theorem normalised_classified_overlap
    {K : Type*} [CommRing K]
    {a b : ℕ} (hb : 0 < b) {ψ : SparsePolynomial K}
    (hR : IsNormalisedRClassified a b ψ)
    (hS : IsNormalisedSClassified a b ψ) :
    ψ = basePotential := by
  rcases hR with ⟨f, hfR, hψR⟩
  rcases hS with ⟨g, hgS, hψS⟩
  have hfg : f = g := by
    exact add_left_cancel (hψR.symm.trans hψS)
  subst g
  have hf0 : f = 0 := pure_r_s_correction_eq_zero hb hfR hgS
  simpa [hf0] using hψR

/-- Pure `r`-correction support is preserved by injective coefficient extension. -/
theorem isPureRCorrection_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (a b : ℕ) (f : SparsePolynomial K) :
    IsPureRCorrection a b (mapCoeffs φ hφ0 f) ↔
      IsPureRCorrection a b f := by
  unfold IsPureRCorrection
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

/-- Pure `s`-correction support is preserved by injective coefficient extension. -/
theorem isPureSCorrection_mapCoeffs_iff
    {K L : Type*} [Zero K] [Zero L]
    (φ : K → L) (hφ0 : φ 0 = 0) (hφ : Function.Injective φ)
    (a b : ℕ) (f : SparsePolynomial K) :
    IsPureSCorrection a b (mapCoeffs φ hφ0 f) ↔
      IsPureSCorrection a b f := by
  unfold IsPureSCorrection
  rw [support_mapCoeffs_eq φ hφ0 hφ f]

end HC4.Toric
