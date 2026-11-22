import HC4.Polynomial.RankThreeCubicSourceCoordinateRankOneClosure
import Mathlib.Tactic

/-!
# Specialising a polynomial Hessian with cofactor divisibility

If every adjugate entry of a polynomial matrix is divisible by p,
then the evaluated matrix has zero adjugate at any zero of p.

This generic specialised lemma avoids forcing Lean to elaborate
matrix adjugate functoriality inside the much larger cubic
source-plane proof.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

/-- Divisibility of every source Hessian cofactor yields rank at most
one at each point of the candidate pole hyperplane. -/
theorem polynomialMatrix_adjugate_zero_at_root
    {K : Type*} [Field K]
    (H : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K))
    (p : MvPolynomial (Fin 3) K)
    (hcof : ∀ i j : Fin 3, p ∣ H.adjugate i j)
    (v : Fin 3 → K)
    (hv : MvPolynomial.aeval v p = 0) :
    (H.map (MvPolynomial.aeval v).toRingHom).adjugate = 0 := by
  classical
  let φ : MvPolynomial (Fin 3) K →ₐ[K] K := MvPolynomial.aeval v
  have hmap : (H.map φ.toRingHom).adjugate =
      H.adjugate.map φ.toRingHom :=
    (φ.toRingHom.map_adjugate H).symm
  rw [hmap]
  ext i j
  change φ (H.adjugate i j) = 0
  obtain ⟨u, hu⟩ := hcof i j
  rw [hu, map_mul]
  change (MvPolynomial.aeval v p) * (MvPolynomial.aeval v u) = 0
  rw [hv, zero_mul]

end
end HC4.Polynomial.RankThreeCubic
