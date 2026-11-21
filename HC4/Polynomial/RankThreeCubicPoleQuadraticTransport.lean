import HC4.Polynomial.RankThreeCubicPoleTransportTrichotomy
import HC4.Polynomial.RankThreeCubicSourceQuadraticEuler
import HC4.Polynomial.RankThreeCubicPoleResidue
import Mathlib.Tactic

/-!
# Cubic source gradient transport as an exact quadratic family

Apply the verified double transverse Euler formula to the *full*
gradient transport identity of the actual cubic source. This produces
a quadratic-family equation along its rational characteristic with
no independent polynomial-velocity assumption.

The third-derivative family is initially expressed in the fraction
field; its source provenance is nevertheless exact, since the family
is constructed by applying the same line-evaluation homomorphism to
third derivatives of the original cubic initial form. Showing these coefficients descend to source polynomial
time families at the chosen pole is the next, separate obligation.
Until then this theorem is not a pole-residue contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev PB (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev PF (K : Type*) [Field K] :=
  FractionRing (PB K)
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The quadratic third-derivative family reconstructs the
transverse gradient along its full straight characteristic.

The coefficients of the quadratic family are the line evaluations
of *actual source third derivatives*. Both sides are equal in
the characteristic time polynomial ring over the fraction field. -/
theorem sourceCubic_transportedGradient_quadraticFamily
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → PF K)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (i : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let z := transverseGenericPoint a
    let E := lineEval z V
    quadraticFamilyEval
        (fun j k : Fin 3 =>
          E (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))))
        (fun j : Fin 3 => E (X (.inr j))) =
      (2 : _root_.Polynomial (PF K)) *
        _root_.Polynomial.C (MvPolynomial.aeval z (pderiv (.inr i) L)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let z := transverseGenericPoint a
  let E : SB K →ₐ[K] _root_.Polynomial (PF K) := lineEval z V
  let P : SB K := pderiv (.inr i) L
  have heuler : (2 : SB K) * P =
      ∑ j : Fin 3, ∑ k : Fin 3,
        (X (.inr j) : SB K) * X (.inr k) *
          pderiv (.inr k) (pderiv (.inr j) P) :=
    sourceCubic_transverseGradient_quadraticIdentity F i
  have hmap :
      (2 : _root_.Polynomial (PF K)) * E P =
        ∑ j : Fin 3, ∑ k : Fin 3,
          E (X (.inr j)) * E (X (.inr k)) *
            E (pderiv (.inr k) (pderiv (.inr j) P)) := by
    have hh := congrArg E heuler
    simpa only [map_mul, map_sum, map_ofNat] using hh
  have hsum :
      quadraticFamilyEval
          (fun j k : Fin 3 =>
            E (pderiv (.inr k) (pderiv (.inr j) P)))
          (fun j : Fin 3 => E (X (.inr j))) =
        ∑ j : Fin 3, ∑ k : Fin 3,
          E (X (.inr j)) * E (X (.inr k)) *
            E (pderiv (.inr k) (pderiv (.inr j) P)) := by
    unfold quadraticFamilyEval
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hg : E P =
      _root_.Polynomial.C (MvPolynomial.aeval z P) :=
    hgrad (.inr i)
  calc
    quadraticFamilyEval
        (fun j k : Fin 3 =>
          E (pderiv (.inr k) (pderiv (.inr j) P)))
        (fun j : Fin 3 => E (X (.inr j))) =
      ∑ j : Fin 3, ∑ k : Fin 3,
        E (X (.inr j)) * E (X (.inr k)) *
          E (pderiv (.inr k) (pderiv (.inr j) P)) := hsum
    _ = (2 : _root_.Polynomial (PF K)) * E P := hmap.symm
    _ = (2 : _root_.Polynomial (PF K)) *
        _root_.Polynomial.C (MvPolynomial.aeval z P) := by rw [hg]

end
end HC4.Polynomial.RankThreeCubic
