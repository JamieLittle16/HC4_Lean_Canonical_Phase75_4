import HC4.Polynomial.TransverseLeadingCharacteristics
import HC4.Polynomial.RankThreeCubicSourceDegrees
import Mathlib.Tactic

/-!
# Arbitrary-degree full transverse rank: nilpotent linear or genuine pole

A regular anchor of the actual leading layer admits a straight rational
characteristic. In arbitrary transverse degree n+2, its Hessian equation
has coefficient degrees n and n+1. Euler rigidity makes any pole-free
representative linear. Descending the gradient transport to the
polynomial ring then forces det(I+tN)=1, hence N^3=0.

The nilpotent shear is injective on original source polynomials.
This is a classification of the leading characteristic, not a claim
that a nonlinear source change preserves the full Hessian determinant.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev S (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The actual transverse Hessian and mixed row have adjacent homogeneous
degrees, for any transverse weight n+2. -/
theorem sourceLeading_homogeneousHessianDegrees
    (a : K) (F : S K) (n : ℕ) :
    let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
    (∀ i j : Fin 3, (sourceTransverseHessian a L i j).IsHomogeneous n) ∧
    (∀ i : Fin 3, (sourceNegativeMixedHessian a L i).IsHomogeneous (n + 1)) := by
  dsimp only
  let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
  have hL : L.IsWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 2) :=
    initialForm_isWeightedHomogeneous transverseCubicWeight ((n : ℤ) + 2) F
  constructor
  · intro i j
    have h : MvPolynomial.IsWeightedHomogeneous transverseCubicWeight
        (pderiv (Sum.inr j) (pderiv (Sum.inr i) L)) (n : ℤ) := by
      have hh := pderiv_isWeightedHomogeneous
        (pderiv_isWeightedHomogeneous hL (Sum.inr i)) (Sum.inr j)
      convert hh using 1 <;> simp [transverseCubicWeight] <;> omega
    exact referenceSlice_isHomogeneous_of_transverseWeight a _ n h
  · intro i
    have h : MvPolynomial.IsWeightedHomogeneous transverseCubicWeight
        (pderiv (Sum.inl ()) (pderiv (Sum.inr i) L)) ((n + 1 : ℕ) : ℤ) := by
      have hh := pderiv_isWeightedHomogeneous
        (pderiv_isWeightedHomogeneous hL (Sum.inr i)) (Sum.inl ())
      convert hh using 1 <;> simp [transverseCubicWeight, Nat.cast_add] <;> omega
    exact (referenceSlice_isHomogeneous_of_transverseWeight a _ (n + 1) h).neg

/-- A polynomial linear velocity representing an anchored rational
characteristic inherits its exact gradient transport over K[y][t]. -/
theorem linearGradientTransport_of_fractionCharacteristic
    (a : K) (L : S K) (V : Unit ⊕ Fin 3 → E K)
    (N : Matrix (Fin 3) (Fin 3) K)
    (hV : V (.inl ()) = 1)
    (hN : ∀ i : Fin 3, V (.inr i) =
      algebraMap (B K) (E K) (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C
        (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) :
    ∀ i : Unit ⊕ Fin 3, linearLineEval a N (pderiv i L) =
      _root_.Polynomial.C (referenceSlice a (pderiv i L)) := by
  classical
  let g : B K →+* E K := algebraMap (B K) (E K)
  let f := _root_.Polynomial.mapRingHom g
  have hg : Function.Injective g := IsFractionRing.injective (B K) (E K)
  have hcomp : f.comp (linearLineEval a N).toRingHom =
      (lineEval (transverseGenericPoint a) V).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : g (MvPolynomial.C c) = algebraMap K (E K) c :=
        (IsScalarTower.algebraMap_apply K (B K) (E K) c).symm
      have hleft : linearLineEval a N (MvPolynomial.C c) =
          _root_.Polynomial.C (MvPolynomial.C c) := by
        simp [linearLineEval, lineEval,
          IsScalarTower.algebraMap_apply K (B K) (_root_.Polynomial (B K)),
          _root_.Polynomial.algebraMap_eq]
      have hright : lineEval (transverseGenericPoint a) V (MvPolynomial.C c) =
          _root_.Polynomial.C (algebraMap K (E K) c) := by
        simp [lineEval, IsScalarTower.algebraMap_apply K (E K)
          (_root_.Polynomial (E K)), _root_.Polynomial.algebraMap_eq]
      change f (linearLineEval a N (MvPolynomial.C c)) =
        lineEval (transverseGenericPoint a) V (MvPolynomial.C c)
      rw [hleft, hright]
      change _root_.Polynomial.map g (_root_.Polynomial.C (MvPolynomial.C c)) = _
      rw [_root_.Polynomial.map_C, hc]
    · intro j
      change f (linearLineEval a N (X j)) =
        lineEval (transverseGenericPoint a) V (X j)
      cases j with
      | inl u =>
        cases u
        have hc : g (MvPolynomial.C a) = algebraMap K (E K) a :=
          (IsScalarTower.algebraMap_apply K (B K) (E K) a).symm
        simp [linearLineEval, lineEval, transverseGenericPoint, f, hV, hc]
      | inr i =>
        have hi := hN i
        change V (.inr i) = g (∑ j : Fin 3, MvPolynomial.C (N i j) * X j) at hi
        simp only [linearLineEval, lineEval, MvPolynomial.aeval_X,
          Sum.elim_inr, transverseGenericPoint, map_add, map_mul,
          f, _root_.Polynomial.mapRingHom_apply, _root_.Polynomial.map_C,
          _root_.Polynomial.map_X, hi]
        <;> rfl
  intro i
  apply _root_.Polynomial.map_injective g hg
  change f (linearLineEval a N (pderiv i L)) =
    f (_root_.Polynomial.C (referenceSlice a (pderiv i L)))
  calc
    f (linearLineEval a N (pderiv i L)) =
      lineEval (transverseGenericPoint a) V (pderiv i L) :=
        RingHom.congr_fun hcomp _
    _ = _root_.Polynomial.C
        (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)) := hgrad i
    _ = f (_root_.Polynomial.C (referenceSlice a (pderiv i L))) := by
      change _ = _root_.Polynomial.map g _
      rw [_root_.Polynomial.map_C]
      exact congrArg _root_.Polynomial.C (referenceSlice_fractionEvaluation a _).symm

/-- Arbitrary-degree leading-layer dichotomy, retaining the actual
source-derived gradient transport in both branches. In the pole-free
branch the velocity is linear, nilpotent, and yields an injective
polynomial characteristic substitution. -/
theorem exists_sourceLeading_nilpotentLinear_or_nonPolynomial
    (F : S K) (n : ℕ)
    (hcap : IsWeightLE transverseCubicWeight ((n : ℤ) + 2) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight ((n : ℤ) + 2) F)).submatrix
      Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → E K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
        _root_.Polynomial.C
          (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          (∀ i : Fin 3, V (.inr i) =
            algebraMap (B K) (E K) (∑ j : Fin 3, MvPolynomial.C (N i j) * X j)) ∧
          N ^ 3 = 0 ∧
          (∀ i : Unit ⊕ Fin 3, linearLineEval a N (pderiv i L) =
            _root_.Polynomial.C (referenceSlice a (pderiv i L))) ∧
          Function.Injective (linearLineEval a N : S K → _root_.Polynomial (B K)))
        ∨ ∃ i : Fin 3, ∀ p : B K, algebraMap (B K) (E K) p ≠ V (.inr i)) := by
  classical
  dsimp only
  let L := initialForm transverseCubicWeight ((n : ℤ) + 2) F
  obtain ⟨a, ha⟩ := exists_regular_transverseGenericPoint htrans
  obtain ⟨V, hV, hgrad⟩ :=
    transverseLeading_exists_anchored_characteristic F ((n : ℤ) + 2)
      (by omega) hcap hdet (transverseGenericPoint a) ha
  have hreg := sourceTransverseHessian_det_ne_zero_of_generic a L ha
  refine ⟨a, V, hreg, hV, hgrad, ?_⟩
  let g : B K →+* E K := algebraMap (B K) (E K)
  have hg : Function.Injective g := IsFractionRing.injective (B K) (E K)
  by_cases hpoly : ∀ i : Fin 3, ∃ p : B K, g p = V (.inr i)
  · left
    obtain ⟨hH, hr⟩ := sourceLeading_homogeneousHessianDegrees a F n
    have hker := sourceFractionHessianEquation_of_gradientTransport a L V hV hgrad
    obtain ⟨N, hN⟩ := exists_linear_matrix_of_poleFree_homogeneousFractionKernel
      g hg n (sourceTransverseHessian a L) (sourceNegativeMixedHessian a L)
      (fun i : Fin 3 => V (.inr i)) hH hr hreg hker hpoly
    have htransport := linearGradientTransport_of_fractionCharacteristic a L V N hV hN hgrad
    have hreg' : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := by
      intro hz
      apply ha
      rw [← referenceSlice_fractionEvaluation, hz, map_zero]
    have hdetN := det_linearCharacteristic_eq_one a N L hreg'
      (fun i => htransport (.inr i))
    have h3 : N ^ 3 = 0 := by
      simpa using matrix_pow_card_eq_zero_of_det_linear_eq_one N hdetN
    exact ⟨N, hN, h3, htransport, linearLineEval_injective_of_cube_zero a N h3⟩
  · right
    push_neg at hpoly
    exact hpoly

end
end HC4.Polynomial.RankThreeCubic
