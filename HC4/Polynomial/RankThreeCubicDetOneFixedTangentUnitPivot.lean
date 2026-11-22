import HC4.Polynomial.RankThreeCubicDetOneLongitudinalUnitEscape
import Mathlib.Tactic

/-!
# Constant tangent vectors have a unit coordinate at the pole

A source-derived fixed tangent direction is a nonzero vector in K^3
transported by an invertible K-matrix. After reduction modulo
an irreducible prime of K[y], at least one of its three coordinate
functions is the image of a NONZERO scalar in K, hence a unit.

This is stronger than the mere nonzero fixed tangent quotient
vector and is precisely what the determinant-one longitudinal
unit lemma requires.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- At least one pivot of an invertibly framed nonzero constant
tangent direction is a unit after passage to a prime quotient. -/
theorem fixedTangent_has_unitPivot_in_irreducibleQuotient
    (p : B3 K) (hp : Irreducible p)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (r t : K) (hrt : r ≠ 0 ∨ t ≠ 0) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    ∃ k : Fin 3,
      IsUnit (q (MvPolynomial.C
        ((M.mulVec ![(0 : K), r, t]) k))) := by
  classical
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R :=
    Ideal.Quotient.mk (Ideal.span {p})
  let ψ : K →+* R := q.comp MvPolynomial.C
  let v : Fin 3 → K := ![(0 : K), r, t]
  have hWne : (fun i : Fin 3 => ψ ((M *ᵥ v) i)) ≠ 0 :=
    fixedTangent_nonzero_in_irreducibleQuotient
      p hp M hM r t hrt
  have hSome : ∃ k : Fin 3, ψ ((M *ᵥ v) k) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hWne
    funext i
    exact hc i
  obtain ⟨k, hk⟩ := hSome
  have hbase : (M *ᵥ v) k ≠ 0 := by
    intro hz
    apply hk
    rw [hz, map_zero]
  have hunit : IsUnit ((M *ᵥ v) k) :=
    isUnit_iff_ne_zero.mpr hbase
  refine ⟨k, ?_⟩
  exact hunit.map ψ

end
end HC4.Polynomial.RankThreeCubic
