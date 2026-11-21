import HC4.Polynomial.RankThreeCubicThirdDerivativeLongitudinal
import HC4.Polynomial.RankThreeCubicLongitudinalPolynomialMap
import Mathlib.Tactic

/-!
# Source cubic third-derivative time coefficients have no poles

The three transverse derivatives of the actual cubic initial source
come from one-variable polynomials in the longitudinal coordinate.
After longitudinal line substitution x0 = a + t and the normalized
characteristic condition V0 = 1, the resulting time-polynomial is
the scalar extension of an honest ground-field polynomial in K[t].

This is the precise coefficient-descent theorem needed for reducing
the source cubic quadratic gradient transport at an irreducible
determinant factor. It does not assert the pole residue contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K
private abbrev PB (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev PF (K : Type*) [Field K] :=
  FractionRing (PB K)

/-- The actual cubic third-transverse-derivative coefficient evaluated
along any normalized characteristic lies in the embedded subring K[t],
even when its transverse velocity coordinates have genuine poles. -/
theorem sourceCubic_thirdTransverse_lineEval_polynomialTime
    (F : SB K) (a : K) (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1) (i j k : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let Q := pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
    ∃ T : _root_.Polynomial K,
      lineEval (transverseGenericPoint a) V Q =
        (_root_.Polynomial.mapRingHom
          (algebraMap K (PF K))) T := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let Q : SB K :=
    pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
  obtain ⟨T, hT⟩ :=
    exists_sourceCubic_thirdTransverse_longitudinal F i j k
  let q : _root_.Polynomial K :=
    MvPolynomial.aeval
      (fun _ : Unit =>
        _root_.Polynomial.C a + _root_.Polynomial.X) T
  refine ⟨q, ?_⟩
  have hr :
      lineEval (transverseGenericPoint a) V
        (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) =
      MvPolynomial.aeval
        (fun _ : Unit =>
          _root_.Polynomial.C (algebraMap K (PF K) a) +
            _root_.Polynomial.X) T := by
    change (MvPolynomial.aeval
      (fun x : Unit ⊕ Fin 3 =>
        _root_.Polynomial.C (transverseGenericPoint a x) +
          _root_.Polynomial.C (V x) * _root_.Polynomial.X))
      (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) = _
    rw [MvPolynomial.aeval_rename]
    congr 1
    funext u
    cases u
    change _root_.Polynomial.C
      (transverseGenericPoint a (.inl ())) +
        _root_.Polynomial.C (V (.inl ())) *
          _root_.Polynomial.X = _
    rw [hV]
    simp [transverseGenericPoint]
  calc
    lineEval (transverseGenericPoint a) V Q =
      lineEval (transverseGenericPoint a) V
        (MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T) := by
          rw [hT]
    _ = MvPolynomial.aeval
      (fun _ : Unit =>
        _root_.Polynomial.C (algebraMap K (PF K) a) +
          _root_.Polynomial.X) T := hr
    _ = (_root_.Polynomial.mapRingHom (algebraMap K (PF K))) q :=
      (longitudinalPolynomial_eval_map a T).symm

end
end HC4.Polynomial.RankThreeCubic
