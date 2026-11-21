import HC4.Polynomial.RankThreeCubicThirdDerivativeBasePolynomialTime
import HC4.Polynomial.RankThreeCubicCramerQuadraticResidue
import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
import Mathlib.Tactic

/-!
# Source-derived Cramer quadratic residue equation

The cubic source's full gradient transport admits a quadratic expansion
whose coefficient family consists of actual source triple transverse
derivatives.  These coefficients have representatives in K[y][t].

Cramer's numerator therefore satisfies a quadratic residue equation at
every domain-valued ring map killing the actual transverse Hessian
determinant. The *same* coefficient family used in the residue equation
is proved to be the image of the source's third derivatives. This avoids
the vacuous choice of a zero quadratic family.

This theorem is a residue constraint, not yet a contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev PB (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev PF (K : Type*) [Field K] := FractionRing (PB K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- For the actual cubic source and any normalized transported
characteristic, the true third-derivative coefficient family has a
polynomial representative in K[y][t] whose quadratic evaluation
annihilates Cramer's numerator after every domain-valued determinant
residue map. No squarefree or nonvanishing assumption is inserted. -/
theorem exists_sourceCubic_cramerQuadraticResidue
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → PF K)
    (hV : V (.inl ()) = 1)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      lineEval (transverseGenericPoint a) V
        (pderiv i (initialForm transverseCubicWeight 3 F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval (transverseGenericPoint a)
          (pderiv i (initialForm transverseCubicWeight 3 F))))
    {E : Type*} [CommRing E] [IsDomain E]
    (res : PB K →+* E)
    (hdetzero : res (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det = 0) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let r := sourceNegativeMixedHessian a L
    let g := algebraMap (PB K) (PF K)
    ∃ Q : Fin 3 → Fin 3 → Fin 3 → _root_.Polynomial (PB K),
      (∀ i j k : Fin 3,
        (Q i j k).map g =
          lineEval (transverseGenericPoint a) V
            (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L)))) ∧
      (∀ i : Fin 3,
        quadraticFamilyEval
          (fun j k : Fin 3 => (Q i j k).map res)
          (fun j : Fin 3 =>
            _root_.Polynomial.C (res ((H.adjugate *ᵥ r) j))) = 0) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (PB K) := sourceTransverseHessian a L
  let r : Fin 3 → PB K := sourceNegativeMixedHessian a L
  let g : PB K →+* PF K := algebraMap (PB K) (PF K)
  let z := transverseGenericPoint a
  let T : SB K →ₐ[K] _root_.Polynomial (PF K) := lineEval z V
  obtain ⟨Q, hQ⟩ :=
    exists_sourceCubic_thirdTransverse_basePolynomialFamily F a V hV
  have hkernel :
      (H.map g) *ᵥ (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 => g (r i) :=
    sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
  refine ⟨Q, ?_, ?_⟩
  · intro i j k
    exact (hQ i j k).symm
  · intro i
    let P : SB K := pderiv (.inr i) L
    let b : PB K := 2 * referenceSlice a P
    have hX (j : Fin 3) :
        T (MvPolynomial.X (.inr j)) =
          _root_.Polynomial.C (g (MvPolynomial.X j)) +
            _root_.Polynomial.X *
              _root_.Polynomial.C (V (.inr j)) := by
      simp [T, lineEval, z, transverseGenericPoint, mul_comm]
    have hCoeff (j k : Fin 3) :
        (Q i j k).map g =
          T (pderiv (.inr k) (pderiv (.inr j) P)) := by
      exact (hQ i j k).symm
    have hb : (2 : _root_.Polynomial (PF K)) *
          _root_.Polynomial.C (MvPolynomial.aeval z P) =
        _root_.Polynomial.C (g b) := by
      have hbase : g b = (2 : PF K) * MvPolynomial.aeval z P := by
        simp [b, map_mul, referenceSlice_fractionEvaluation]
      rw [hbase]
      norm_num [map_mul]
    have ht := sourceCubic_transportedGradient_quadraticFamily
      F a V hgrad i
    have hq :
        quadraticFamilyEval
          (fun j k : Fin 3 => (Q i j k).map g)
          (fun j : Fin 3 =>
            _root_.Polynomial.C (g (MvPolynomial.X j)) +
              _root_.Polynomial.X *
                _root_.Polynomial.C (V (.inr j))) =
          _root_.Polynomial.C (g b) := by
      calc
        quadraticFamilyEval
            (fun j k : Fin 3 => (Q i j k).map g)
            (fun j : Fin 3 =>
              _root_.Polynomial.C (g (MvPolynomial.X j)) +
                _root_.Polynomial.X *
                  _root_.Polynomial.C (V (.inr j))) =
          quadraticFamilyEval
            (fun j k : Fin 3 =>
              T (pderiv (.inr k) (pderiv (.inr j) P)))
            (fun j : Fin 3 => T (MvPolynomial.X (.inr j))) := by
              congr 1
              · funext j k
                exact hCoeff j k
              · funext j
                exact (hX j).symm
        _ = (2 : _root_.Polynomial (PF K)) *
            _root_.Polynomial.C (MvPolynomial.aeval z P) := ht
        _ = _root_.Polynomial.C (g b) := hb
    exact cramerNumerator_quadraticResidue
      H r (fun j : Fin 3 => V (.inr j))
      hkernel res hdetzero (fun j k : Fin 3 => Q i j k) b hq

end
end HC4.Polynomial.RankThreeCubic
