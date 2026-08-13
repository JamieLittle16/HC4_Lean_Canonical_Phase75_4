import HC4.Valuation.AdaptiveAlignedSmithTransverseSourceShear
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingQuadraticSupport
import Mathlib.Tactic

/-!
# Transverse source shears on the quadratic parameter layer

The arbitrary determinant-one source transvection is now available on the
honest polynomial family.  This file extracts the finite quadratic formulas
needed by the direct-closing calculation.

For

    X_k ↦ X_k + c X_ell

with `k ≠ ell`, the source origin is fixed.  Hence source-origin Hessian
entries transform by the ordinary congruence formulas.  In particular

    H'_{kk}       = H_{kk},
    H'_{k,ell}    = H_{k,ell} + c H_{kk},
    H'_{ell,ell}  = H_{ell,ell} + c H_{k,ell}
                     + c H_{ell,k} + c^2 H_{kk}.

When `c` is parameter-constant, taking an exact parameter coefficient simply
gives the same formulas over `K`.  Thus the first actual quadratic layer can
be normalised by an honest source transvection without changing parameter
orders by spurious convolution with the shear coefficient.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- An arbitrary source transvection fixes the source origin, so taking the
source constant coefficient commutes with the source shear. -/
theorem constantCoeff_transverseSourceShearHom
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.constantCoeff
        (transverseSourceShearHom (K := K) k ell c P) =
      MvPolynomial.constantCoeff P := by
  have h :=
    eval_transverseSourceShearHom_unshear
      (K := K) k ell hkl c P (zeroPolynomialSection (K := K))
  rw [transverseSourceUnshearSection_zero] at h
  change
    MvPolynomial.eval (fun _ : Fin 4 => (0 : Polynomial K))
        (transverseSourceShearHom (K := K) k ell c P) =
      MvPolynomial.eval (fun _ : Fin 4 => (0 : Polynomial K)) P at h
  simpa only [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] using h

/-- The `kk` source-origin Hessian entry is unchanged by
`X_k ↦ X_k + c X_ell`. -/
theorem quadraticFamilyHessianMatrix_transverseSourceShear_kk
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell c P) k k =
      quadraticFamilyHessianMatrix P k k := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv k
          (MvPolynomial.pderiv k
            (transverseSourceShearHom (K := K) k ell c P))) = _
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c k hkl P]
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c k hkl (MvPolynomial.pderiv k P)]
  exact constantCoeff_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv k (MvPolynomial.pderiv k P))

/-- The mixed `k,ell` source-origin Hessian entry acquires one copy of the
`kk` entry. -/
theorem quadraticFamilyHessianMatrix_transverseSourceShear_kell
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell c P) k ell =
      quadraticFamilyHessianMatrix P k ell +
        c * quadraticFamilyHessianMatrix P k k := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv ell
          (MvPolynomial.pderiv k
            (transverseSourceShearHom (K := K) k ell c P))) = _
  rw [pderiv_transverseSourceShearHom_of_ne_source
    k ell hkl c k hkl P]
  rw [pderiv_source_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv k P)]
  simp only [map_add, map_mul]
  rw [constantCoeff_transverseSourceShearHom
      k ell hkl c (MvPolynomial.pderiv ell (MvPolynomial.pderiv k P))]
  rw [constantCoeff_transverseSourceShearHom
      k ell hkl c (MvPolynomial.pderiv k (MvPolynomial.pderiv k P))]
  simp

/-- Exact diagonal congruence formula at the source origin. -/
theorem quadraticFamilyHessianMatrix_transverseSourceShear_ellell
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell c P) ell ell =
      quadraticFamilyHessianMatrix P ell ell +
        c * quadraticFamilyHessianMatrix P k ell +
        c * quadraticFamilyHessianMatrix P ell k +
        c * c * quadraticFamilyHessianMatrix P k k := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv ell
          (MvPolynomial.pderiv ell
            (transverseSourceShearHom (K := K) k ell c P))) = _
  rw [pderiv_source_transverseSourceShearHom k ell hkl c P]
  rw [map_add, MvPolynomial.pderiv_C_mul]
  rw [pderiv_source_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv ell P)]
  rw [pderiv_source_transverseSourceShearHom
    k ell hkl c (MvPolynomial.pderiv k P)]
  simp only [map_add, map_mul]
  repeat' rw [constantCoeff_transverseSourceShearHom k ell hkl c]
  simp
  ring

/-- Parameter-coefficient form of the exact diagonal congruence when the
source shear coefficient is constant in the family parameter. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        ell ell).coeff n =
      (quadraticFamilyHessianMatrix P ell ell).coeff n +
        a * (quadraticFamilyHessianMatrix P k ell).coeff n +
        a * (quadraticFamilyHessianMatrix P ell k).coeff n +
        a * a * (quadraticFamilyHessianMatrix P k k).coeff n := by
  rw [quadraticFamilyHessianMatrix_transverseSourceShear_ellell
    k ell hkl (Polynomial.C a) P]
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc]

/-- Likewise for the mixed entry under a parameter-constant source shear. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_kell
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        k ell).coeff n =
      (quadraticFamilyHessianMatrix P k ell).coeff n +
        a * (quadraticFamilyHessianMatrix P k k).coeff n := by
  rw [quadraticFamilyHessianMatrix_transverseSourceShear_kell
    k ell hkl (Polynomial.C a) P]
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- Likewise the `kk` parameter-layer Hessian coefficient is unchanged. -/
theorem quadraticFamilyHessianMatrix_coeff_transverseSourceShear_kk
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (a : K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    (quadraticFamilyHessianMatrix
        (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
        k k).coeff n =
      (quadraticFamilyHessianMatrix P k k).coeff n := by
  rw [quadraticFamilyHessianMatrix_transverseSourceShear_kk
    k ell hkl (Polynomial.C a) P]


/-- The source-origin family Hessian is symmetric. -/
theorem quadraticFamilyHessianMatrix_symmetric
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i k : Fin 4) :
    quadraticFamilyHessianMatrix P i k =
      quadraticFamilyHessianMatrix P k i := by
  unfold quadraticFamilyHessianMatrix
  change
    MvPolynomial.constantCoeff
        (MvPolynomial.pderiv k (MvPolynomial.pderiv i P)) =
      MvPolynomial.constantCoeff
        (MvPolynomial.pderiv i (MvPolynomial.pderiv k P))
  exact congrArg
    (fun Q : MvPolynomial (Fin 4) (Polynomial K) =>
      MvPolynomial.constantCoeff Q)
    (pderiv_comm_commRing i k P).symm

/-- Symmetry persists after extracting any exact parameter coefficient. -/
theorem quadraticFamilyHessianMatrix_coeff_symmetric
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (i k : Fin 4) :
    (quadraticFamilyHessianMatrix P i k).coeff n =
      (quadraticFamilyHessianMatrix P k i).coeff n := by
  exact congrArg (fun p : Polynomial K => p.coeff n)
    (quadraticFamilyHessianMatrix_symmetric P i k)

variable [CharZero K]

/-- Elementary field algebra behind quadratic source normalisation.  A
nonzero symmetric binary quadratic coefficient can be made visible on a
diagonal by one of the constant shears `t = 0, 1, -1`. -/
theorem exists_scalarShear_diagonal_ne_zero
    (A B C : K)
    (hnz : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ t : K,
      A + t * B + t * B + t * t * C ≠ 0 := by
  by_cases hA : A = 0
  · by_cases hC : C = 0
    · have hB : B ≠ 0 := by
        rcases hnz with hA' | hB' | hC'
        · exact False.elim (hA' hA)
        · exact hB'
        · exact False.elim (hC' hC)
      refine ⟨1, ?_⟩
      simpa [hA, hC, two_mul] using
        (mul_ne_zero (show (2 : K) ≠ 0 by norm_num) hB)
    · by_cases hplus : B + B + C ≠ 0
      · refine ⟨1, ?_⟩
        simpa [hA] using hplus
      · have hp : B + B + C = 0 := not_ne_iff.mp hplus
        refine ⟨-1, ?_⟩
        intro hm
        have hm' : -B - B + C = 0 := by
          simpa [hA, sub_eq_add_neg] using hm
        have hCC : C + C = 0 := by
          calc
            C + C = (B + B + C) + (-B - B + C) := by ring
            _ = 0 := by rw [hp, hm']; simp
        have h2C : (2 : K) * C = 0 := by
          simpa [two_mul] using hCC
        exact hC ((mul_eq_zero.mp h2C).resolve_left
          (show (2 : K) ≠ 0 by norm_num))
  · exact ⟨0, by simpa using hA⟩

/-- **Honest diagonalisation of one quadratic parameter layer.**

If the `k,ell` binary part of one source-origin Hessian parameter layer is
nonzero, a parameter-constant determinant-one source transvection makes the
`ell,ell` coefficient of that same layer nonzero.  Because the shear
coefficient is constant in the family parameter, no lower or higher
parameter orders are mixed into this statement. -/
theorem exists_constantTransverseShear_layerDiagonal_ne_zero
    (k ell : Fin 4)
    (hkl : k ≠ ell)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ)
    (hnz :
      (quadraticFamilyHessianMatrix P ell ell).coeff n ≠ 0 ∨
      (quadraticFamilyHessianMatrix P k ell).coeff n ≠ 0 ∨
      (quadraticFamilyHessianMatrix P k k).coeff n ≠ 0) :
    ∃ a : K,
      (quadraticFamilyHessianMatrix
          (transverseSourceShearHom (K := K) k ell (Polynomial.C a) P)
          ell ell).coeff n ≠ 0 := by
  let A := (quadraticFamilyHessianMatrix P ell ell).coeff n
  let B := (quadraticFamilyHessianMatrix P k ell).coeff n
  let C := (quadraticFamilyHessianMatrix P k k).coeff n
  have hsym :
      (quadraticFamilyHessianMatrix P ell k).coeff n = B := by
    simpa [B] using
      quadraticFamilyHessianMatrix_coeff_symmetric P n ell k
  have habc : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 := by
    simpa [A, B, C] using hnz
  rcases exists_scalarShear_diagonal_ne_zero A B C habc with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [quadraticFamilyHessianMatrix_coeff_transverseSourceShear_ellell
    k ell hkl a P n]
  rw [hsym]
  simpa [A, B, C] using ha

end

end HC4.Valuation
