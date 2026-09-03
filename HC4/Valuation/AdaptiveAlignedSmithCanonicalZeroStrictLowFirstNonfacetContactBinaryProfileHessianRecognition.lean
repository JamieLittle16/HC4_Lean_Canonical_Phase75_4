import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryHomogenization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryEulerSchurTransport
import Mathlib.Tactic

/-!
# A19.R18: recognize the binary parameter/longitudinal Hessian layers

After transverse inflation the honest contact Rees has pure binary grading:
a longitudinal coefficient of degree `n` occurs at parameter order
`D - r*n`.  Consequently the family-level parameter Hessian entries

* `τ² ∂τ² F`,
* `τ ∂τ (E₀ F)`, and
* the Euler-scaled longitudinal Hessian entry

have, at that exact parameter layer and longitudinal degree, precisely the
integral staircase coefficients `H00`, `H01`, and `H11`.

This module records that recognition before any active Schur cancellation and
serves as the parameter/longitudinal half of the final A19.R18 adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The binary family layer at the profile order `D-r*n`, restricted to
longitudinal degree `n`, is exactly the raw transverse profile coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_parameterLayer_longitudinal_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer P.binaryHomogenizedFamily
        (T.topFace.degree - P.profileWeight * n))).coeff n =
      R.profile.coeff n := by
  rw [R.profile_eq]
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [qsContactRawLongitudinalProfile]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have hcoeff := Polynomial.coeff_X_pow_mul
    (Polynomial.C
      (MvPolynomial.coeff (m.cons n)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)))
    (T.topFace.degree - P.profileWeight * n) 0
  simpa using hcoeff

private theorem profile_order_cast
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {n : ℕ}
    (hn : R.profile.coeff n ≠ 0) :
    ((T.topFace.degree - P.profileWeight * n : ℕ) :
        MvPolynomial (Fin 3) K) =
      (T.topFace.degree : MvPolynomial (Fin 3) K) -
        (P.profileWeight : MvPolynomial (Fin 3) K) *
          (n : MvPolynomial (Fin 3) K) := by
  have hnmem : n ∈ R.profile.support := Polynomial.mem_support_iff.mpr hn
  have hnle : n ≤ R.profile.natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hnmem
  have hmul : n * P.profileWeight ≤ R.profile.natDegree * P.profileWeight :=
    Nat.mul_le_mul_right P.profileWeight hnle
  have hle : P.profileWeight * n ≤ T.topFace.degree := by
    rw [Nat.mul_comm P.profileWeight n]
    exact hmul.trans R.support_bound
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- Exact `H00` recognition at every nonzero profile coefficient. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryParameterHessian00_layer
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ)
    (hn : R.profile.coeff n ≠ 0) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (familyParameterSecondEuler P.binaryHomogenizedFamily)
        (T.topFace.degree - P.profileWeight * n))).coeff n =
      R.profileHessian00.coeff n := by
  let q := T.topFace.degree - P.profileWeight * n
  have hlayer := familyParameterLayer_familyParameterSecondEuler
    P.binaryHomogenizedFamily q
  have hcoeff := congrArg
    (fun F : MvPolynomial (Fin 4) K =>
      (MvPolynomial.finSuccEquiv K 3 F).coeff n) hlayer
  have hbase := P.binaryHomogenized_parameterLayer_longitudinal_coeff R n
  have hbaseq :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer P.binaryHomogenizedFamily q)).coeff n =
        R.profile.coeff n := by
    simpa [q] using hbase
  have hcoeff' :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (familyParameterSecondEuler P.binaryHomogenizedFamily) q)).coeff n =
        (q : MvPolynomial (Fin 3) K) *
          ((q : MvPolynomial (Fin 3) K) - 1) * R.profile.coeff n := by
    calc
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (familyParameterSecondEuler P.binaryHomogenizedFamily) q)).coeff n =
          (((q : Polynomial (MvPolynomial (Fin 3) K)) *
              ((q : Polynomial (MvPolynomial (Fin 3) K)) - 1)) *
            (MvPolynomial.finSuccEquiv K 3
              (familyParameterLayer P.binaryHomogenizedFamily q))).coeff n := by
        simpa only [map_mul, map_sub, map_one, map_natCast] using hcoeff
      _ = (q : MvPolynomial (Fin 3) K) *
            ((q : MvPolynomial (Fin 3) K) - 1) *
              (MvPolynomial.finSuccEquiv K 3
                (familyParameterLayer P.binaryHomogenizedFamily q)).coeff n := by
        rw [show
          (q : Polynomial (MvPolynomial (Fin 3) K)) *
              ((q : Polynomial (MvPolynomial (Fin 3) K)) - 1) =
            Polynomial.C
              ((q : MvPolynomial (Fin 3) K) *
                ((q : MvPolynomial (Fin 3) K) - 1)) by
          have hqC :
              (q : Polynomial (MvPolynomial (Fin 3) K)) =
                Polynomial.C (q : MvPolynomial (Fin 3) K) :=
            (map_natCast
              (Polynomial.C : MvPolynomial (Fin 3) K →+*
                Polynomial (MvPolynomial (Fin 3) K)) q).symm
          rw [hqC, ← Polynomial.C_1, ← Polynomial.C_sub,
            ← Polynomial.C_mul]]
        rw [Polynomial.coeff_C_mul]
      _ = (q : MvPolynomial (Fin 3) K) *
            ((q : MvPolynomial (Fin 3) K) - 1) * R.profile.coeff n := by
        rw [hbaseq]
  have hq := profile_order_cast P R hn
  rw [R.coeff_profileHessian00]
  rw [← hq]
  simpa [q] using hcoeff'

/-- Exact `H01` recognition at every nonzero profile coefficient. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryParameterHessian01_layer
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ)
    (hn : R.profile.coeff n ≠ 0) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (familyParameterEuler
          (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily))
        (T.topFace.degree - P.profileWeight * n))).coeff n =
      R.profileHessian01.coeff n := by
  let q := T.topFace.degree - P.profileWeight * n
  have hlayer := familyParameterLayer_familyParameterEuler
    (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) q
  have hcoeff := congrArg
    (fun F : MvPolynomial (Fin 4) K =>
      (MvPolynomial.finSuccEquiv K 3 F).coeff n) hlayer
  have hEulerLayer :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) q)).coeff n =
        (n : MvPolynomial (Fin 3) K) * R.profile.coeff n := by
    ext m
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    rw [familyParameterLayer_coeff]
    rw [coeff_mvEuler]
    have hbase := P.binaryHomogenized_parameterLayer_longitudinal_coeff R n
    have hm := congrArg (fun A : MvPolynomial (Fin 3) K => MvPolynomial.coeff m A) hbase
    change MvPolynomial.coeff m
        ((MvPolynomial.finSuccEquiv K 3
          (familyParameterLayer P.binaryHomogenizedFamily
            (T.topFace.degree - P.profileWeight * n))).coeff n) =
      MvPolynomial.coeff m (R.profile.coeff n) at hm
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hm
    rw [familyParameterLayer_coeff] at hm
    have hmq :
        (MvPolynomial.coeff (Finsupp.cons n m) P.binaryHomogenizedFamily).coeff q =
          MvPolynomial.coeff m (R.profile.coeff n) := by
      simpa [q] using hm
    rw [Finsupp.cons_zero]
    rw [Polynomial.coeff_natCast_mul]
    rw [show (n : MvPolynomial (Fin 3) K) =
        MvPolynomial.C (n : K) by
      exact (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm]
    rw [MvPolynomial.coeff_C_mul]
    exact congrArg (fun a : K => (n : K) * a) hmq
  have hcoeff' :
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)) q)).coeff n =
        (q : MvPolynomial (Fin 3) K) *
          (n : MvPolynomial (Fin 3) K) * R.profile.coeff n := by
    calc
      (MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer
          (familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)) q)).coeff n =
          ((q : Polynomial (MvPolynomial (Fin 3) K)) *
            (MvPolynomial.finSuccEquiv K 3
              (familyParameterLayer
                (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) q))).coeff n := by
        simpa only [map_mul, map_natCast] using hcoeff
      _ = (q : MvPolynomial (Fin 3) K) *
            (MvPolynomial.finSuccEquiv K 3
              (familyParameterLayer
                (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) q)).coeff n := by
        rw [Polynomial.coeff_natCast_mul]
      _ = (q : MvPolynomial (Fin 3) K) *
            ((n : MvPolynomial (Fin 3) K) * R.profile.coeff n) := by
        rw [hEulerLayer]
      _ = (q : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) * R.profile.coeff n := by
        ring
  have hq := profile_order_cast P R hn
  rw [R.coeff_profileHessian01]
  rw [← hq]
  simpa [q, mul_assoc, mul_comm, mul_left_comm] using hcoeff'

/-- Exact `H11` recognition at every nonzero profile coefficient. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryParameterHessian11_layer
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ)
    (_hn : R.profile.coeff n ≠ 0) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer
        (HC4.Polynomial.eulerScaledHessian
          P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4))
        (T.topFace.degree - P.profileWeight * n))).coeff n =
      R.profileHessian11.coeff n := by
  let q := T.topFace.degree - P.profileWeight * n
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  rw [coeff_eulerScaledHessian]
  simp only [if_pos]
  have hbase := P.binaryHomogenized_parameterLayer_longitudinal_coeff R n
  have hm := congrArg (fun A : MvPolynomial (Fin 3) K => MvPolynomial.coeff m A) hbase
  change MvPolynomial.coeff m
      ((MvPolynomial.finSuccEquiv K 3
        (familyParameterLayer P.binaryHomogenizedFamily
          (T.topFace.degree - P.profileWeight * n))).coeff n) =
    MvPolynomial.coeff m (R.profile.coeff n) at hm
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hm
  rw [familyParameterLayer_coeff] at hm
  have hmq :
      (MvPolynomial.coeff (Finsupp.cons n m) P.binaryHomogenizedFamily).coeff q =
        MvPolynomial.coeff m (R.profile.coeff n) := by
    simpa [q] using hm
  rw [R.coeff_profileHessian11]
  rw [Finsupp.cons_zero]
  rw [show
      (n : Polynomial K) * (n : Polynomial K) - (n : Polynomial K) =
        Polynomial.C ((n : K) * ((n : K) - 1)) by
    have hnC :
        (n : Polynomial K) = Polynomial.C (n : K) :=
      (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
    rw [hnC, ← Polynomial.C_mul, ← Polynomial.C_sub]
    congr 1
    ring]
  rw [Polynomial.coeff_C_mul]
  rw [show
      (n : MvPolynomial (Fin 3) K) *
          ((n : MvPolynomial (Fin 3) K) - 1) =
        MvPolynomial.C ((n : K) * ((n : K) - 1)) by
    have hnC :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hnC, ← MvPolynomial.C_1, ← MvPolynomial.C_sub,
      ← MvPolynomial.C_mul]]
  rw [MvPolynomial.coeff_C_mul]
  exact congrArg
    (fun a : K => ((n : K) * ((n : K) - 1)) * a) hmq

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation