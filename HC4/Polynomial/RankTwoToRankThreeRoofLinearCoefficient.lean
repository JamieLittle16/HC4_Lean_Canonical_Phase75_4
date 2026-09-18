import HC4.Polynomial.RankThreePencils
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

/-- **Exact linear determinant coefficient for the roof opening.** -/
set_option maxHeartbeats 2000000 in
theorem coeff_one_det_rankTwoToRankThreeRoofPencil
    {K : Type*} [CommRing K]
    (p r a D b C A : K) :
    (rankTwoToRankThreeRoofPencil p r a D b C A).det.coeff 1 =
      A * C ^ 2 * D * (D - 1) * p * r * (1 - p - r) := by
  simp [rankTwoToRankThreeRoofPencil, vectorHessianCore3,
    Matrix.det_fin_three]
  ring

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

end

end HC4.Polynomial
