import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Actual Hessian four-block extraction at the Smith departure frontier

The matrix Schur clock of `FirstSchurDepartureBridge` should be fed by the
*actual parameter family*, not by identifying the retained Smith packet with
the whole special fibre.  The latter would be too strong: the canonical Smith
packet is an exposed subface.

This file therefore separates the two issues cleanly.

1. `parameterFirstEquiv` swaps

       K[x₀,x₁,x₂,x₃][X]  <->  (K[x₀,x₁,x₂,x₃])[X]

   by the canonical multivariate-polynomial equivalences.  Applying it
   entrywise to the actual Hessian gives an honest polynomial Hessian series.
   Its determinant is proved to be exactly `X^defect` by `RingEquiv.map_det`.

2. `FrontierRigidPacketSchurExposure` records only the remaining geometric
   exposure statement: the constant cleared Schur block of that actual
   Hessian series is a nonzero common polynomial multiple of the rigid Smith
   packet block, and the active determinant is a unit at the special fibre.

Under that single exposure certificate the already-green canonical Smith
outcome and matrix Schur clock give an exact dichotomy: strict rank-one to
rank-two progress, or a transverse departure at the determinant-closing
order.  No equality between the Smith subface and the complete special fibre
is assumed.
-/

namespace HC4.Valuation

open HC4.Newton
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- Coefficient formula for formal partial derivatives over a general
commutative ring.  The older project backport was field-specialised; the
parameter family has coefficient ring `Polynomial K`, so we record the
ring-level form here. -/
theorem coeff_pderiv_commRing
    {σ R : Type*} [CommRing R]
    (i : σ)
    (F : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.pderiv i F) =
      MvPolynomial.coeff (m + Finsupp.single i 1) F *
        ((m i + 1 : ℕ) : R) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp [hP, hQ, add_mul]
  | monomial n a =>
      rw [MvPolynomial.pderiv_monomial,
        MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases h : n = m + Finsupp.single i 1
      · simp [h]
      · simp only [h, if_false, zero_mul]
        by_cases hn : n i = 0
        · simp [hn]
        · apply if_neg
          have hle : Finsupp.single i 1 ≤ n := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.mpr hn
          intro hsub
          apply h
          exact (tsub_eq_iff_eq_add_of_le hle).mp hsub

/-- Formal mixed partials commute over a commutative ring. -/
theorem pderiv_comm_commRing
    {σ R : Type*} [CommRing R]
    (i j : σ)
    (F : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i F) := by
  classical
  ext m
  rw [coeff_pderiv_commRing, coeff_pderiv_commRing,
    coeff_pderiv_commRing, coeff_pderiv_commRing]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_apply, hij, hji,
      add_comm, add_left_comm, add_assoc]
    ring

/-! ## Swapping the parameter and spatial polynomial layers -/

/-- Canonical equivalence which views a spatial multivariate polynomial with
univariate polynomial coefficients as a polynomial in the parameter whose
coefficients are spatial multivariate polynomials. -/
noncomputable def parameterFirstEquiv (K : Type*) [Field K] :
    MvPolynomial (Fin 4) (Polynomial K) ≃ₐ[K]
      Polynomial (MvPolynomial (Fin 4) K) :=
  (MvPolynomial.optionEquivRight K (Fin 4)).symm.trans
    (MvPolynomial.optionEquivLeft K (Fin 4))

/-- The coefficient parameter `X` is sent to the outer polynomial variable. -/
theorem parameterFirstEquiv_C_X :
    parameterFirstEquiv K (MvPolynomial.C Polynomial.X) =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) := by
  have hright :
      (MvPolynomial.optionEquivRight K (Fin 4)).symm
          (MvPolynomial.C Polynomial.X) =
        MvPolynomial.X (none : Option (Fin 4)) := by
    apply (MvPolynomial.optionEquivRight K (Fin 4)).injective
    simp
  change
    MvPolynomial.optionEquivLeft K (Fin 4)
        ((MvPolynomial.optionEquivRight K (Fin 4)).symm
          (MvPolynomial.C Polynomial.X)) = Polynomial.X
  rw [hright]
  exact MvPolynomial.optionEquivLeft_X_none K (Fin 4)

/-- Hence an exact coefficient-ring monomial `X^Delta` becomes the same
outer parameter monomial. -/
theorem parameterFirstEquiv_C_X_pow (Delta : ℕ) :
    parameterFirstEquiv K
        (MvPolynomial.C (Polynomial.X ^ Delta)) =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
  rw [MvPolynomial.C_pow]
  rw [map_pow]
  rw [parameterFirstEquiv_C_X]

/-- The actual Hessian family, now regarded as a polynomial in the parameter
with spatial-polynomial matrix coefficients. -/
noncomputable def parameterFirstHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (MvPolynomial (Fin 4) K)) :=
  (parameterFirstEquiv K).toRingEquiv.mapMatrix
    (HC4.Polynomial.hessian P)

/-- Mixed partial symmetry survives the parameter swap. -/
theorem parameterFirstHessian_symmetric
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    parameterFirstHessian P i j = parameterFirstHessian P j i := by
  change
    parameterFirstEquiv K
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) =
      parameterFirstEquiv K
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j P))
  congr 1
  exact (pderiv_comm_commRing i j P).symm

/-- Determinant transport for the actual parameter-first Hessian. -/
theorem parameterFirstHessian_det
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (parameterFirstHessian P).det =
      parameterFirstEquiv K (HC4.Polynomial.hessianDeterminant P) := by
  unfold parameterFirstHessian HC4.Polynomial.hessianDeterminant
  exact
    (RingEquiv.map_det
      (parameterFirstEquiv K).toRingEquiv
      (HC4.Polynomial.hessian P)).symm

/-- An exact Hessian defect becomes the exact outer-parameter determinant
clock `X^Delta`. -/
theorem parameterFirstHessian_det_eq_X_pow
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (parameterFirstHessian P).det =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
  rw [parameterFirstHessian_det, hdef]
  exact parameterFirstEquiv_C_X_pow Delta

/-! ## The canonical actual four-block -/

/-- The actual Hessian parameter series, packed into the general symmetric
`2+2` four-block used by the matrix Schur clock.  The active variables are
coordinates `0,1` and the transverse variables are `2,3`. -/
noncomputable def familyHessianFourBlock
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix (parameterFirstHessian P)

/-- Displaying the canonical four-block recovers the transported Hessian
matrix exactly. -/
theorem familyHessianFourBlock_matrix
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (familyHessianFourBlock P).matrix = parameterFirstHessian P := by
  exact GeneralFourBlock.matrix_ofSymmetricMatrix
    (parameterFirstHessian P)
    (parameterFirstHessian_symmetric P)

/-- **Actual four-block determinant extraction.**
The determinant core of the canonical block is exactly the Hessian defect
monomial.  No Schur-exposure hypothesis enters this theorem. -/
theorem familyHessianFourBlock_determinantCore_eq_X_pow
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (familyHessianFourBlock P).determinantCore =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
  calc
    (familyHessianFourBlock P).determinantCore =
        (familyHessianFourBlock P).matrix.det :=
      (GeneralFourBlock.matrix_det (familyHessianFourBlock P)).symm
    _ = (parameterFirstHessian P).det := by
      rw [familyHessianFourBlock_matrix]
    _ = (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta :=
      parameterFirstHessian_det_eq_X_pow P hdef

/-- The actual block attached to a retained departure frontier. -/
noncomputable def frontierHessianFourBlock
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  familyHessianFourBlock f.lossless.family

/-- The denominator-cleared quadratic block carried by the retained Smith
subface.  This remains deliberately distinct from the actual Hessian block. -/
noncomputable def frontierPersistentPacketBlock
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    BinarySchurBlock K :=
  rankOnePacketQuadraticBlock
    (0 : Fin 4) 1 2 D
    (canonicalSpecialFiberSmithPolynomial
      (polynomialFamilySpecialFiber f.lossless.family))

/-! ## The honest remaining Smith-to-Schur exposure interface -/

/-- The exact geometric information still required to expose the retained
rigid Smith packet in the constant cleared Schur block of the *actual*
Hessian family.

The common factor is allowed to be an arbitrary nonzero spatial polynomial;
this is important because the Smith packet is an exposed subface rather than
the complete special fibre. -/
structure FrontierRigidPacketSchurExposure
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) where
  activeDet_coeff_zero_ne_zero :
    (frontierHessianFourBlock f).activeDet.coeff 0 ≠ 0
  scale : MvPolynomial (Fin 4) K
  scale_ne_zero : scale ≠ 0
  active_coeff :
    (frontierHessianFourBlock f).polynomialSchurSeries.active.coeff 0 =
      scale * MvPolynomial.C (frontierPersistentPacketBlock f).a
  offDiag_coeff :
    (frontierHessianFourBlock f).polynomialSchurSeries.offDiag.coeff 0 =
      scale * MvPolynomial.C (frontierPersistentPacketBlock f).b
  kernel_coeff :
    (frontierHessianFourBlock f).polynomialSchurSeries.kernel.coeff 0 =
      scale * MvPolynomial.C (frontierPersistentPacketBlock f).c

namespace FrontierRigidPacketSchurExposure

/-- A rigid scalar Smith packet transfers to the ring-level pivot certificate
for the actual constant Schur block as soon as the exposure relation above is
known. -/
theorem rigidSeries_of_packetRigid
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (E : FrontierRigidPacketSchurExposure f)
    (hrigid :
      HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D
        (canonicalSpecialFiberSmithPolynomial
          (polynomialFamilySpecialFiber f.lossless.family))) :
    (frontierHessianFourBlock f).polynomialSchurSeries.LeftPivot ∨
      (frontierHessianFourBlock f).polynomialSchurSeries.RightAxisPivot := by
  let q := frontierPersistentPacketBlock f
  rcases hrigid.2 with hleft | hright
  · left
    have hqa : q.a ≠ 0 := hleft.1.1
    have hqdet : q.a * q.c = q.b * q.b := hleft.1.2
    constructor
    · rw [E.active_coeff]
      exact mul_ne_zero E.scale_ne_zero (MvPolynomial.C_ne_zero.mpr hqa)
    · rw [E.active_coeff, E.offDiag_coeff, E.kernel_coeff]
      calc
        (E.scale * MvPolynomial.C q.a) *
            (E.scale * MvPolynomial.C q.c) =
          E.scale ^ 2 * MvPolynomial.C (q.a * q.c) := by
            rw [MvPolynomial.C_mul]
            ring
        _ = E.scale ^ 2 * MvPolynomial.C (q.b * q.b) := by
          rw [hqdet]
        _ = (E.scale * MvPolynomial.C q.b) *
            (E.scale * MvPolynomial.C q.b) := by
          rw [MvPolynomial.C_mul]
          ring
  · right
    have hqa : q.a = 0 := hright.1.1
    have hqb : q.b = 0 := hright.1.2.1
    have hqc : q.c ≠ 0 := hright.1.2.2
    constructor
    · rw [E.active_coeff, hqa]
      simp
    constructor
    · rw [E.offDiag_coeff, hqb]
      simp
    · rw [E.kernel_coeff]
      exact mul_ne_zero E.scale_ne_zero (MvPolynomial.C_ne_zero.mpr hqc)

/-- A rigid packet plus the honest exposure certificate produces the exact
four-block object expected by the green matrix Schur clock. -/
noncomputable def toExactFourBlockSchurData
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (E : FrontierRigidPacketSchurExposure f)
    (hrigid :
      HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D
        (canonicalSpecialFiberSmithPolynomial
          (polynomialFamilySpecialFiber f.lossless.family))) :
    FrontierExactFourBlockSchurData f where
  block := frontierHessianFourBlock f
  fullDet :=
    familyHessianFourBlock_determinantCore_eq_X_pow
      f.lossless.family f.hessianDefect
  activeDet_coeff_zero_ne_zero := E.activeDet_coeff_zero_ne_zero
  rigid := E.rigidSeries_of_packetRigid hrigid

/-- **Local Smith-frontier exhaustion modulo the single exposure theorem.**
The pre-existing canonical Smith outcome is now enough to give either
strict rank-one to rank-two repair progress immediately, or a concrete
transverse coefficient at the determinant-closing order.

In the already-rank-two canonical outcome no exposure information is used;
the certificate is needed only for the rigid rank-one packet branch. -/
theorem repairProgress_or_closing
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (E : FrontierRigidPacketSchurExposure f) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
    (∃ S : FrontierExactRankOneSchurClock f,
      S.firstOrder = f.defect ∧
        (S.series.offDiag.coeff f.defect ≠ 0 ∨
         S.series.kernel.coeff f.defect ≠ 0)) := by
  rcases f.lossless.canonicalOutcome with hrigid | hrankTwo
  · let B := E.toExactFourBlockSchurData hrigid
    rcases B.rankTwoProgress_or_closing with ⟨S, hprogress | hclose⟩
    · exact Or.inl ⟨hprogress.1, hprogress.2.2⟩
    · exact Or.inr ⟨S, hclose⟩
  · exact Or.inl ⟨hrankTwo.2.1, hrankTwo.2.2⟩

end FrontierRigidPacketSchurExposure

end

end HC4.Valuation
