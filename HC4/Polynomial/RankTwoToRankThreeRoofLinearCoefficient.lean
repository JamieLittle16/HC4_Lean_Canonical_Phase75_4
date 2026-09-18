import HC4.Polynomial.RankThreePencils
import HC4.Valuation.ParameterGapDualJet
import Mathlib.Tactic

/-!
# Linear coefficient opening a rank-two roof to rank three

For a central exponent supported on two active coordinates,

    v = (p, 0, r),

and a first roof departure

    u = (a, D, b),

the coefficient-weighted three-by-three Hessian-core pencil is

    C M(v) + X A M(u).

The constant matrix has a two-by-two active block in coordinates `0,2`.
Its determinant vanishes.  The linear determinant coefficient is exactly the
active constant minor times the new diagonal entry:

    A C^2 D(D-1) p r (1-p-r).

Thus in characteristic zero, if `p,r>0`, `D>=2`, and the two honest source
coefficients are nonzero, the roof pencil has nonzero determinant.  This is
the state-free rank-two-to-rank-three opening used by the central
finite-staircase closure.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Three-coordinate exponent Hessian core. -/
def vectorHessianCore3 {K : Type*} [CommRing K]
    (z : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => z i * z j - if i = j then z i else 0

/-- Coefficient-weighted polynomial pencil from a two-active-coordinate base
to a three-active-coordinate first layer. -/
def rankTwoToRankThreeRoofPencil
    {K : Type*} [CommRing K]
    (p r a D b C A : K) :
    Matrix (Fin 3) (Fin 3) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C C *
        Polynomial.C (vectorHessianCore3 (K := K) ![p, 0, r] i j) +
      Polynomial.X * Polynomial.C A *
        Polynomial.C (vectorHessianCore3 (K := K) ![a, D, b] i j)

set_option maxHeartbeats 2000000

/-- Formal-derivative form of the exact linear determinant coefficient.
Using the derivative at zero avoids expanding coefficient extraction through
the irrelevant quadratic and cubic determinant terms. -/
theorem derivative_det_rankTwoToRankThreeRoofPencil_eval_zero
    {K : Type*} [CommRing K]
    (p r a D b C A : K) :
    Polynomial.eval 0
        (Polynomial.derivative
          (rankTwoToRankThreeRoofPencil p r a D b C A).det) =
      A * C ^ 2 * D * (D - 1) * p * r * (1 - p - r) := by
  simp [rankTwoToRankThreeRoofPencil, vectorHessianCore3,
    Matrix.det_fin_three,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul]
  ring

/-- **Exact linear determinant coefficient for the roof opening.** -/
theorem coeff_one_det_rankTwoToRankThreeRoofPencil
    {K : Type*} [CommRing K]
    (p r a D b C A : K) :
    (rankTwoToRankThreeRoofPencil p r a D b C A).det.coeff 1 =
      A * C ^ 2 * D * (D - 1) * p * r * (1 - p - r) := by
  have h := derivative_det_rankTwoToRankThreeRoofPencil_eval_zero
    (K := K) p r a D b C A
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  simpa [Polynomial.coeff_derivative] using h

/-- A genuine nonprimitive axis opening makes the three-coordinate roof
Hessian determinant nonzero. -/
theorem rankTwoToRankThreeRoofPencil_det_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {p r a D b : ℕ} {C A : K}
    (hp : 0 < p) (hr : 0 < r) (hD : 2 ≤ D)
    (hC : C ≠ 0) (hA : A ≠ 0) :
    (rankTwoToRankThreeRoofPencil (K := K)
      p r a D b C A).det ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun q : Polynomial K => q.coeff 1) hzero
  rw [coeff_one_det_rankTwoToRankThreeRoofPencil] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  have hpK : (p : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hrK : (r : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hr)
  have hDK : (D : K) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by omega)
  have hDm1K : (D : K) - 1 ≠ 0 := by
    intro hz
    have hcast : (D : K) = 1 := sub_eq_zero.mp hz
    have hnat : D = 1 := by exact_mod_cast hcast
    omega
  have hlast : (1 : K) - (p : K) - (r : K) ≠ 0 := by
    intro hz
    have hcast : (p : K) + (r : K) = 1 := by
      linear_combination -hz
    have hnat : p + r = 1 := by exact_mod_cast hcast
    omega
  have hne :
      A * C ^ 2 * (D : K) * ((D : K) - 1) *
          (p : K) * (r : K) * (1 - (p : K) - (r : K)) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact hA
    · exact pow_ne_zero 2 hC
    · exact hDK
    · exact hDm1K
    · exact hpK
    · exact hrK
    · exact hlast
  exact hne hcoeff


/-! ## Gap-jet form for an arbitrary honest roof family -/

/-- Lift a three-by-three polynomial matrix into the parameter-gap subring. -/
noncomputable def matrix3ToParameterGap
    {R : Type*} [CommRing R] {j : ℕ}
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hM : ∀ r s : Fin 3, HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s)) :
    Matrix (Fin 3) (Fin 3) (HC4.Valuation.parameterGapSubring (R := R) j) :=
  fun r s => ⟨M r s, hM r s⟩

/-- Entrywise dual jet at a positive gap order for a three-by-three matrix. -/
noncomputable def matrix3ParameterGapDualJet
    {R : Type*} [CommRing R] {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hM : ∀ r s : Fin 3, HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s)) :
    Matrix (Fin 3) (Fin 3) (DualNumber R) :=
  (HC4.Valuation.parameterGapDualJet (R := R) j hj).mapMatrix
    (matrix3ToParameterGap M hM)

@[simp] theorem matrix3ParameterGapDualJet_apply
    {R : Type*} [CommRing R] {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hM : ∀ r s : Fin 3, HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (r s : Fin 3) :
    matrix3ParameterGapDualJet hj M hM r s =
      ((M r s).coeff 0, (M r s).coeff j) := by
  rfl

/-- The nilpotent determinant component is the selected coefficient of the
honest three-by-three determinant. -/
theorem snd_det_matrix3ParameterGapDualJet
    {R : Type*} [CommRing R] {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hM : ∀ r s : Fin 3, HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s)) :
    TrivSqZeroExt.snd (matrix3ParameterGapDualJet hj M hM).det =
      M.det.coeff j := by
  let J := HC4.Valuation.parameterGapDualJet (R := R) j hj
  let G := matrix3ToParameterGap M hM
  have hmap : J G.det = (J.mapMatrix G).det := J.map_det G
  have hsub :=
    (HC4.Valuation.parameterGapSubring (R := R) j).subtype.map_det G
  have hmatrix :
      (HC4.Valuation.parameterGapSubring (R := R) j).subtype.mapMatrix G = M := by
    ext r s
    rfl
  rw [hmatrix] at hsub
  change TrivSqZeroExt.snd ((J.mapMatrix G).det) = M.det.coeff j
  rw [← hmap]
  change ((G.det : HC4.Valuation.parameterGapSubring (R := R) j) :
      Polynomial R).coeff j = _
  simpa using congrArg (fun p : Polynomial R => p.coeff j) hsub

/-- Rank-two constant three-by-three block with middle kernel coordinate. -/
def rankTwoRoofZeroKernelBase
    {R : Type*} [CommRing R] (a b c d : R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![a, 0, b;
     0, 0, 0;
     c, 0, d]

/-- Dual first jet around a rank-two roof block. -/
def rankTwoRoofFirstJet
    {R : Type*} [CommRing R] (a b c d : R)
    (B : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) (DualNumber R) :=
  fun i k => (rankTwoRoofZeroKernelBase a b c d i k, B i k)

/-- The first determinant variation only sees the new middle diagonal. -/
theorem snd_det_rankTwoRoofFirstJet
    {R : Type*} [CommRing R] (a b c d : R)
    (B : Matrix (Fin 3) (Fin 3) R) :
    TrivSqZeroExt.snd (rankTwoRoofFirstJet a b c d B).det =
      (a * d - b * c) * B 1 1 := by
  simp [rankTwoRoofFirstJet, rankTwoRoofZeroKernelBase,
    Matrix.det_fin_three, DualNumber.snd_mul]
  ring

/-- **Honest gap-family rank-two to rank-three bridge.**

If a three-by-three polynomial Hessian block has a positive parameter gap,
its constant layer is rank two with nonzero active minor, and its determinant
vanishes identically, then the middle diagonal of the first layer must vanish.
-/
theorem middleDiagonal_eq_zero_of_polynomialMatrix3_gap
    {R : Type*} [CommRing R] [IsDomain R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hgap : ∀ r s : Fin 3,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s : Fin 3,
      (M r s).coeff 0 = rankTwoRoofZeroKernelBase a b c d r s)
    (hactive : a * d - b * c ≠ 0)
    (hdet : M.det = 0) :
    (M 1 1).coeff j = 0 := by
  let B : Matrix (Fin 3) (Fin 3) R :=
    fun r s => (M r s).coeff j
  have hjet :
      matrix3ParameterGapDualJet hj M hgap =
        rankTwoRoofFirstJet a b c d B := by
    ext r s
    simp [matrix3ParameterGapDualJet_apply, rankTwoRoofFirstJet,
      B, hbase]
  have hzero :
      TrivSqZeroExt.snd
        (matrix3ParameterGapDualJet hj M hgap).det = 0 := by
    rw [snd_det_matrix3ParameterGapDualJet, hdet]
    simp
  rw [hjet, snd_det_rankTwoRoofFirstJet] at hzero
  have hB : B 1 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hactive
  exact hB


/-- A three-by-three polynomial matrix whose entries all have a parameter gap
has determinant in the same parameter-gap subring. -/
theorem matrix3_det_hasNoPositiveParameterCoeffBelow
    {R : Type*} [CommRing R]
    {j : ℕ}
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hM : ∀ r s : Fin 3,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s)) :
    HC4.Valuation.HasNoPositiveParameterCoeffBelow j M.det := by
  let S : Subring (Polynomial R) :=
    HC4.Valuation.parameterGapSubring (R := R) j
  let H : Matrix (Fin 3) (Fin 3) S :=
    fun r s => ⟨M r s, hM r s⟩
  have hmatrix : S.subtype.mapMatrix H = M := by
    ext r s
    rfl
  have hmap := S.subtype.map_det H
  have hdet : M.det = S.subtype H.det := by
    rw [← hmatrix]
    exact hmap.symm
  rw [hdet]
  exact H.det.property

/-- Exact leading coefficient of a three-by-three rank-two roof family at its
first positive parameter layer. -/
theorem coeff_det_polynomialMatrix3_gap
    {R : Type*} [CommRing R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hgap : ∀ r s : Fin 3,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s : Fin 3,
      (M r s).coeff 0 = rankTwoRoofZeroKernelBase a b c d r s) :
    M.det.coeff j =
      (a * d - b * c) * (M 1 1).coeff j := by
  let B : Matrix (Fin 3) (Fin 3) R :=
    fun r s => (M r s).coeff j
  have hjet :
      matrix3ParameterGapDualJet hj M hgap =
        rankTwoRoofFirstJet a b c d B := by
    ext r s
    simp [matrix3ParameterGapDualJet_apply, rankTwoRoofFirstJet,
      B, hbase]
  calc
    M.det.coeff j =
        TrivSqZeroExt.snd
          (matrix3ParameterGapDualJet hj M hgap).det := by
      symm
      exact snd_det_matrix3ParameterGapDualJet hj M hgap
    _ =
        TrivSqZeroExt.snd
          (rankTwoRoofFirstJet a b c d B).det := by rw [hjet]
    _ = (a * d - b * c) * B 1 1 :=
      snd_det_rankTwoRoofFirstJet a b c d B
    _ = (a * d - b * c) * (M 1 1).coeff j := rfl


/-- Nonzero active base minor and nonzero first roof diagonal make the exact
leading determinant coefficient nonzero. -/
theorem coeff_det_polynomialMatrix3_gap_ne_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hgap : ∀ r s : Fin 3,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s : Fin 3,
      (M r s).coeff 0 = rankTwoRoofZeroKernelBase a b c d r s)
    (hactive : a * d - b * c ≠ 0)
    (hdiag : (M 1 1).coeff j ≠ 0) :
    M.det.coeff j ≠ 0 := by
  rw [coeff_det_polynomialMatrix3_gap hj M hgap a b c d hbase]
  exact mul_ne_zero hactive hdiag

/-- **Nonzero first roof diagonal forces a genuine rank-three minor.**

This is the contrapositive form used by the source-facing central staircase
adapter.  Higher parameter layers remain completely arbitrary. -/
theorem polynomialMatrix3_gap_det_ne_zero_of_middleDiagonal
    {R : Type*} [CommRing R] [IsDomain R]
    {j : ℕ} (hj : 0 < j)
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hgap : ∀ r s : Fin 3,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow j (M r s))
    (a b c d : R)
    (hbase : ∀ r s : Fin 3,
      (M r s).coeff 0 = rankTwoRoofZeroKernelBase a b c d r s)
    (hactive : a * d - b * c ≠ 0)
    (hdiag : (M 1 1).coeff j ≠ 0) :
    M.det ≠ 0 := by
  intro hdet
  exact hdiag
    (middleDiagonal_eq_zero_of_polynomialMatrix3_gap
      hj M hgap a b c d hbase hactive hdet)

end

end HC4.Polynomial
