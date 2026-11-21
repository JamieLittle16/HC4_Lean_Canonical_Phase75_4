import HC4.Polynomial.RankThreeCubicThirdDerivativeBasePolynomialTime
import HC4.Polynomial.RankThreeCubicCramerQuadraticResidue
import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
import Mathlib.Tactic

/-!
# Quadratic Cramer residue from the actual source cubic

This module composes the source-honest triple-derivative coefficient
descent, exact quadratic full-gradient transport, and Cramer's
numerator identity.

For any domain-valued residue map annihilating the source transverse
Hessian determinant, the residue of the *actual* Cramer numerator
satisfies the cubic's third-derivative quadratic equation.

The equation holds without squarefreeness, but its residue vector
may be zero at a repeated determinant factor. Proving nonzero
residue and excluding the singular-direction geometry are separate.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual transported transverse gradient is a quadratic family
with polynomial coefficients in K[y][t], not merely in its fraction
field. The witness is the image of the *source third derivatives*. -/
theorem exists_sourceCubic_baseQuadraticTransport
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (i : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let E := lineEval (transverseGenericPoint a) V
    ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
      (∀ j k : Fin 3,
        (Q j k).map (algebraMap (B3 K) (F3 K)) =
          E (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) ∧
      quadraticFamilyEval
        (fun j k : Fin 3 =>
          (Q j k).map (algebraMap (B3 K) (F3 K)))
        (fun j : Fin 3 =>
          _root_.Polynomial.C
            (algebraMap (B3 K) (F3 K) (MvPolynomial.X j)) +
          _root_.Polynomial.X * _root_.Polynomial.C (V (.inr j))) =
        _root_.Polynomial.C
          (algebraMap (B3 K) (F3 K)
            (2 * referenceSlice a (pderiv (.inr i) L))) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let E : SB K →ₐ[K] _root_.Polynomial (F3 K) :=
    lineEval (transverseGenericPoint a) V
  let g : B3 K →+* F3 K := algebraMap (B3 K) (F3 K)
  obtain ⟨Qall, hq⟩ :=
    exists_sourceCubic_thirdTransverse_basePolynomialFamily F a V hV
  let Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K) :=
    fun j k => Qall i j k
  have hQ (j k : Fin 3) :
      (Q j k).map g =
        E (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) :=
    (hq i j k).symm
  have hcoord (j : Fin 3) :
      E (MvPolynomial.X (.inr j)) =
        _root_.Polynomial.C (g (MvPolynomial.X j)) +
          _root_.Polynomial.X *
            _root_.Polynomial.C (V (.inr j)) := by
    change
      (MvPolynomial.aeval
        (fun x : Unit ⊕ Fin 3 =>
          _root_.Polynomial.C (transverseGenericPoint a x) +
            _root_.Polynomial.C (V x) * _root_.Polynomial.X))
        (MvPolynomial.X (.inr j)) = _
    rw [MvPolynomial.aeval_X]
    change
      _root_.Polynomial.C (g (MvPolynomial.X j)) +
        _root_.Polynomial.C (V (.inr j)) * _root_.Polynomial.X =
      _root_.Polynomial.C (g (MvPolynomial.X j)) +
        _root_.Polynomial.X * _root_.Polynomial.C (V (.inr j))
    ring
  have htransport :=
    sourceCubic_transportedGradient_quadraticFamily
      F a V hgrad i
  have hQfun :
      (fun j k : Fin 3 => (Q j k).map g) =
      (fun j k : Fin 3 =>
        E (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) := by
    funext j k
    exact hQ j k
  have hZfun :
      (fun j : Fin 3 =>
        _root_.Polynomial.C (g (MvPolynomial.X j)) +
          _root_.Polynomial.X * _root_.Polynomial.C (V (.inr j))) =
      (fun j : Fin 3 => E (MvPolynomial.X (.inr j))) := by
    funext j
    exact (hcoord j).symm
  have hbase :
      (2 : _root_.Polynomial (F3 K)) *
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv (.inr i) L)) =
      _root_.Polynomial.C
        (g (2 * referenceSlice a (pderiv (.inr i) L))) := by
    rw [← referenceSlice_fractionEvaluation]
    have hg2 : g (2 : B3 K) = (2 : F3 K) := by
      calc
        g (2 : B3 K) = g (1 + 1) := by norm_num
        _ = g 1 + g 1 := map_add g 1 1
        _ = 1 + 1 := by simp only [map_one]
        _ = 2 := by norm_num
    have hC2 : _root_.Polynomial.C (2 : F3 K) =
        (2 : _root_.Polynomial (F3 K)) := by
      calc
        _root_.Polynomial.C (2 : F3 K) =
          _root_.Polynomial.C (1 + 1) := by norm_num
        _ = _root_.Polynomial.C (1 : F3 K) +
            _root_.Polynomial.C (1 : F3 K) := map_add _ _ _
        _ = (1 : _root_.Polynomial (F3 K)) + 1 := by simp only [map_one]
        _ = 2 := by norm_num
    calc
      (2 : _root_.Polynomial (F3 K)) *
          _root_.Polynomial.C (g (referenceSlice a (pderiv (.inr i) L))) =
        _root_.Polynomial.C
          ((2 : F3 K) * g (referenceSlice a (pderiv (.inr i) L))) := by
            rw [← hC2, ← _root_.Polynomial.C_mul]
      _ = _root_.Polynomial.C
          (g (2 * referenceSlice a (pderiv (.inr i) L))) := by
            have hh :
                g (2 * referenceSlice a (pderiv (.inr i) L)) =
                  (2 : F3 K) *
                    g (referenceSlice a (pderiv (.inr i) L)) := by
              calc
                g (2 * referenceSlice a (pderiv (.inr i) L)) =
                    g (2 : B3 K) *
                      g (referenceSlice a (pderiv (.inr i) L)) :=
                        map_mul g _ _
                _ = (2 : F3 K) *
                    g (referenceSlice a (pderiv (.inr i) L)) := by rw [hg2]
            exact congrArg _root_.Polynomial.C hh.symm
  refine ⟨Q, hQ, ?_⟩
  change quadraticFamilyEval (fun j k => (Q j k).map g)
      (fun j =>
        _root_.Polynomial.C (g (MvPolynomial.X j)) +
          _root_.Polynomial.X * _root_.Polynomial.C (V (.inr j))) =
        _root_.Polynomial.C (g (2 * referenceSlice a (pderiv (.inr i) L)))
  rw [hQfun, hZfun]
  exact htransport.trans hbase

/-- Polynomial quadratic residue at *any* source Hessian determinant
component with a domain-valued residue map, obtained exclusively from
the actual gradient transport and normalized source characteristic.

The velocity is never assumed polynomial. -/
theorem exists_sourceCubic_cramerQuadraticResidue
    {E : Type*} [CommRing E] [IsDomain E]
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (res : B3 K →+* E)
    (hdetzero :
      res (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det = 0)
    (i : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let r := sourceNegativeMixedHessian a L
    ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
      (∀ j k : Fin 3,
        (Q j k).map (algebraMap (B3 K) (F3 K)) =
          lineEval (transverseGenericPoint a) V
            (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) ∧
      quadraticFamilyEval
        (fun j k : Fin 3 => (Q j k).map res)
        (fun j : Fin 3 =>
          _root_.Polynomial.C (res ((H.adjugate *ᵥ r) j))) = 0 := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) := sourceTransverseHessian a L
  let r : Fin 3 → B3 K := sourceNegativeMixedHessian a L
  obtain ⟨Q, hQ, htrans⟩ :=
    exists_sourceCubic_baseQuadraticTransport F a V hV hgrad i
  have hk :
      (H.map (algebraMap (B3 K) (F3 K))) *ᵥ
        (fun j : Fin 3 => V (.inr j)) =
      fun j : Fin 3 => algebraMap (B3 K) (F3 K) (r j) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  have hres :=
    cramerNumerator_quadraticResidue H r
      (fun j : Fin 3 => V (.inr j)) hk
      res hdetzero Q
      (2 * referenceSlice a (pderiv (.inr i) L))
      htrans
  exact ⟨Q, hQ, hres⟩

end
end HC4.Polynomial.RankThreeCubic
