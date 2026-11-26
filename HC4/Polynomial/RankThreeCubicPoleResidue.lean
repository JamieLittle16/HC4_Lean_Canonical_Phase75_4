module

public import HC4.Polynomial.RankThreeCubicFibrePencils

/-!
# Residue of a characteristic direction with a pole

This is the homogeneous quadratic calculation used to detect a common
singular point of the moving cubic. The coefficient ring is intended
to be a local ring at the pole and the second homomorphism its
residue map. The proof only needs the stated ring maps.
-/

@[expose] public section

namespace HC4.Polynomial.RankThreeCubic

open scoped BigOperators
open _root_.Polynomial

variable {ι A F E : Type*} [Fintype ι]
  [CommRing A] [CommRing F] [CommRing E]

/-- A quadratic family evaluated on polynomial coordinates. -/
noncomputable def quadraticFamilyEval (Q : ι → ι → Polynomial A) (z : ι → Polynomial A) : Polynomial A :=
  ∑ i, ∑ j, Q i j * z i * z j

theorem quadraticFamilyEval_scale (Q : ι → ι → Polynomial A) (z : ι → Polynomial A)
    (p : Polynomial A) :
    quadraticFamilyEval Q (fun i => p * z i) = p ^ 2 * quadraticFamilyEval Q z := by
  unfold quadraticFamilyEval
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticFamilyEval_map (f : A →+* F) (Q : ι → ι → Polynomial A)
    (z : ι → Polynomial A) :
    (quadraticFamilyEval Q z).map f =
      quadraticFamilyEval (fun i j => (Q i j).map f) (fun i => (z i).map f) := by
  change mapRingHom f (quadraticFamilyEval Q z) = _
  simp only [quadraticFamilyEval, map_sum, map_mul]
  rfl

/-- A quadratic family constant on the characteristic vanishes at the
residue of the scaled characteristic velocity. A nonzero residue
vector is thus a common zero of the family. -/
theorem quadraticFamilyEval_eq_zero_at_poleResidue [IsDomain E]
    (embed : A →+* F) (hembed : Function.Injective embed)
    (res : A →+* E) (s b : A) (hs : res s = 0)
    (Q : ι → ι → Polynomial A) (y S : ι → A) (W : ι → F)
    (hscale : ∀ i, embed (S i) = embed s * W i)
    (htransport : quadraticFamilyEval (fun i j => (Q i j).map embed)
        (fun i => C (embed (y i)) + X * C (W i)) = C (embed b)) :
    quadraticFamilyEval (fun i j => (Q i j).map res) (fun i => C (res (S i))) = 0 := by
  have hscaled : quadraticFamilyEval Q (fun i => C (s * y i) + X * C (S i)) =
      (C s) ^ 2 * C b := by
    apply Polynomial.map_injective embed hembed
    rw [quadraticFamilyEval_map]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_X, Polynomial.map_pow]
    have he (i : ι) :
        C (embed (s * y i)) + X * C (embed (S i)) =
          C (embed s) * (C (embed (y i)) + X * C (W i)) := by
      rw [hscale]
      simp only [map_mul]
      ring
    simp_rw [he, quadraticFamilyEval_scale, htransport]
  have hres := congrArg (fun p : Polynomial A => p.map res) hscaled
  simp only [quadraticFamilyEval_map, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
    Polynomial.map_pow, res.map_mul, hs, zero_mul, map_zero, zero_add, zero_pow (by decide : 2 ≠ 0)] at hres
  rw [quadraticFamilyEval_scale] at hres
  exact (mul_eq_zero.mp hres).resolve_left (pow_ne_zero _ X_ne_zero)

end HC4.Polynomial.RankThreeCubic
