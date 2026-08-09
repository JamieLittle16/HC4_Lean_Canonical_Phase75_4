import Mathlib

/-!
# Rank-one quasi-translations

A large part of the exceptional HC4 analysis leads to maps whose nonlinear
part is constrained to one fixed direction.  This module isolates the general
algebraic mechanism.

Let `ell : M →ₗ[K] K`, let `v : M`, and suppose `ell v = 0`.  For an arbitrary
scalar function `f : K → K`, set

    H(x) = f(ell x) • v,
    F(x) = x + H(x).

Then `ell` is constant along the displacement direction, hence `H(F x) = H x`.
Consequently `F` is a quasi-translation with inverse `x ↦ x - H(x)`.
No differentiability assumption is needed.
-/

namespace HC4.QuasiTranslation

section RankOne

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The nonlinear displacement in a fixed direction `v`. -/
def displacement (ell : M →ₗ[K] K) (v : M) (f : K → K) (x : M) : M :=
  f (ell x) • v

/-- The rank-one shear/quasi-translation `x ↦ x + f(ell x) • v`. -/
def shearMap (ell : M →ₗ[K] K) (v : M) (f : K → K) (x : M) : M :=
  x + displacement ell v f x

/-- The candidate inverse `x ↦ x - f(ell x) • v`. -/
def shearInverse (ell : M →ₗ[K] K) (v : M) (f : K → K) (x : M) : M :=
  x - displacement ell v f x

/-- The displacement is killed by `ell` when the direction lies in its kernel. -/
@[simp] theorem ell_displacement
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    ell (displacement ell v f x) = 0 := by
  simp [displacement, horth]

/-- The linear functional is invariant under the forward shear. -/
@[simp] theorem ell_shearMap
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    ell (shearMap ell v f x) = ell x := by
  simp [shearMap, displacement, horth]

/-- The linear functional is invariant under the inverse shear. -/
@[simp] theorem ell_shearInverse
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    ell (shearInverse ell v f x) = ell x := by
  simp [shearInverse, displacement, horth]

/-- The nonlinear displacement is unchanged after applying the shear. -/
@[simp] theorem displacement_shearMap
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    displacement ell v f (shearMap ell v f x) = displacement ell v f x := by
  simp [displacement, ell_shearMap ell v f horth x]

/-- The nonlinear displacement is also unchanged after applying the inverse. -/
@[simp] theorem displacement_shearInverse
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    displacement ell v f (shearInverse ell v f x) = displacement ell v f x := by
  simp [displacement, ell_shearInverse ell v f horth x]

/-- The displacement satisfies the quasi-translation identity `H(x + H(x)) = H(x)`. -/
theorem quasi_translation_identity
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    displacement ell v f (x + displacement ell v f x) =
      displacement ell v f x := by
  exact displacement_shearMap ell v f horth x

/-- The displayed inverse is a left inverse. -/
theorem shearInverse_comp_map
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) :
    Function.LeftInverse (shearInverse ell v f) (shearMap ell v f) := by
  intro x
  change shearMap ell v f x -
    displacement ell v f (shearMap ell v f x) = x
  rw [displacement_shearMap ell v f horth]
  simp [shearMap]

/-- The displayed inverse is a right inverse. -/
theorem shearMap_comp_inverse
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) :
    Function.RightInverse (shearInverse ell v f) (shearMap ell v f) := by
  intro x
  change shearInverse ell v f x +
    displacement ell v f (shearInverse ell v f x) = x
  rw [displacement_shearInverse ell v f horth]
  simp [shearInverse]

/-- Every rank-one shear in a kernel direction is bijective. -/
theorem shearMap_bijective
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) :
    Function.Bijective (shearMap ell v f) := by
  refine ⟨(shearInverse_comp_map ell v f horth).injective, ?_⟩
  exact (shearMap_comp_inverse ell v f horth).surjective

/-- The one-parameter shear flow obtained by scaling the displacement. -/
def shearFlow (t : K) (ell : M →ₗ[K] K) (v : M) (f : K → K) (x : M) : M :=
  shearMap ell v (fun z => t * f z) x

/-- The functional `ell` is constant along every member of the shear flow. -/
@[simp] theorem ell_shearFlow
    (t : K) (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    ell (shearFlow t ell v f x) = ell x := by
  exact ell_shearMap ell v (fun z => t * f z) horth x

/-- Time zero is the identity map. -/
@[simp] theorem shearFlow_zero
    (ell : M →ₗ[K] K) (v : M) (f : K → K) (x : M) :
    shearFlow 0 ell v f x = x := by
  simp [shearFlow, shearMap, displacement]

/-- The rank-one shears form an additive one-parameter action. -/
theorem shearFlow_add
    (s t : K) (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    shearFlow s ell v f (shearFlow t ell v f x) =
      shearFlow (t + s) ell v f x := by
  simp [shearFlow, shearMap, displacement, horth, add_mul, add_smul, add_assoc]

/-- Flow at the negative parameter is the inverse flow. -/
theorem shearFlow_neg_comp
    (t : K) (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) (x : M) :
    shearFlow (-t) ell v f (shearFlow t ell v f x) = x := by
  rw [shearFlow_add (-t) t ell v f horth x]
  simp

/-- A rank-one shear is injective. -/
theorem shearMap_injective
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) :
    Function.Injective (shearMap ell v f) :=
  (shearMap_bijective ell v f horth).1

/-- A rank-one shear is surjective. -/
theorem shearMap_surjective
    (ell : M →ₗ[K] K) (v : M) (f : K → K)
    (horth : ell v = 0) :
    Function.Surjective (shearMap ell v f) :=
  (shearMap_bijective ell v f horth).2

end RankOne

end HC4.QuasiTranslation
