import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetResidualDegreeGap
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoAlgebra
import Mathlib.Tactic

/-!
# A19.91: the lower degree-one `qs` ray cannot end in codimension two

A19.75/A19.79 identify the genuine lower `qs` ray with a primitive
coordinate-zero step and coefficient degree one.  A19.90 upgrades its
rank-three terminal equation to the exact autonomous normal form

    T = X - X^2.

The expensive pure algebra is isolated in
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoAlgebra`.
This file now only extracts the small scalar data needed from the large
restart-state records and assembles the contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.RationalRigidity
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

-- Keep the public elimination theorem thin so command-local heartbeat budgets reset.

/-- The six state-free scalars consumed by the A19.91 algebra.  Naming this
small record once prevents Lean from repeatedly weak-head-normalising the full
dependent ray record while elaborating later theorem signatures. -/
private structure QsRayDegreeOneScalars (K : Type u) where
  A : ℕ
  B : ℕ
  C : ℕ
  Q : K
  R : K
  S : K

/-- Extract the state-free scalar face of the lower `qs` ray. -/
private def qs_ray_degreeOne_scalars
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : QsRayDegreeOneScalars K where
  A := C.ray.facetExponent (1 : Fin 4)
  B := C.ray.facetExponent (2 : Fin 4)
  C := C.ray.facetExponent (3 : Fin 4)
  Q := C.ray.zeroSlope (1 : Fin 4)
  R := C.ray.zeroSlope (2 : Fin 4)
  S := C.ray.zeroSlope (3 : Fin 4)

/-- The exact raw polynomial identity, stated only over the compact scalar
record. -/
private def QsRayDegreeOneScalars.RawIdentity
    (D : QsRayDegreeOneScalars K) : Prop :=
  (Polynomial.X - Polynomial.X ^ 2) *
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S =
    HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S

/-- Cast-normalised rank-three terminal certificate.  Keeping this conversion
in its own declaration prevents later proofs from repeatedly normalising the
full dependent terminal record. -/
private theorem qs_ray_degreeOne_terminalCertificate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := C.ray.zeroCoefficientPolynomial)
      ((C.ray.facetExponent 1 : ℕ) : K)
      ((C.ray.facetExponent 2 : ℕ) : K)
      ((C.ray.facetExponent 3 : ℕ) : K)
      (1 : K)
      (C.ray.zeroSlope (1 : Fin 4))
      (C.ray.zeroSlope (2 : Fin 4))
      (C.ray.zeroSlope (3 : Fin 4)) := by
  have hcert0 := C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
  simpa only [Nat.cast_one] using hcert0

/-- Positivity of the three transverse base exponents, already projected onto
the compact scalar record. -/
private theorem qs_ray_degreeOne_scalars_positive
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    0 < (qs_ray_degreeOne_scalars C).A ∧
      0 < (qs_ray_degreeOne_scalars C).B ∧
      0 < (qs_ray_degreeOne_scalars C).C := by
  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  simpa [qs_ray_degreeOne_scalars] using
    And.intro hcoords.2.1 (And.intro hcoords.2.2.1 hcoords.2.2.2)

set_option maxHeartbeats 1000000 in
/-- Extract the autonomous degree-one raw identity once.  Its result type is
now deliberately opaque with respect to the large dependent ray record. -/
private theorem qs_ray_degreeOne_raw_identity
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    (qs_ray_degreeOne_scalars C).RawIdentity := by
  let D := qs_ray_degreeOne_scalars C
  rcases qs_ray_degreeOne_scalars_positive C hthree with ⟨hA, hB, hC⟩
  have hphiDeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hphi0 : C.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    C.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert0 := qs_ray_degreeOne_terminalCertificate C hthree
  have hcert :
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := C.ray.zeroCoefficientPolynomial)
        (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S := by
    simpa [D, qs_ray_degreeOne_scalars] using hcert0
  rcases
      HC4.RationalRigidity.exists_rankThree_raw_target_X_sub_X_sq_identity_of_source_degree_one
        hA hB hC (by norm_num) hphiDeg hphi0 hcert with
    ⟨_hPone, _hphi1, hraw⟩
  simpa [D, QsRayDegreeOneScalars.RawIdentity] using hraw

/-- Extract coordinate zero and the three transverse affine endpoint equations
against the same compact scalar record used by the raw identity. -/
private theorem qs_ray_outside_affine_data
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.ray.outsideExponent (0 : Fin 4) = 1 ∧
      ((C.ray.outsideExponent (1 : Fin 4) : ℕ) : K) =
        ((qs_ray_degreeOne_scalars C).A : K) +
          (qs_ray_degreeOne_scalars C).Q ∧
      ((C.ray.outsideExponent (2 : Fin 4) : ℕ) : K) =
        ((qs_ray_degreeOne_scalars C).B : K) +
          (qs_ray_degreeOne_scalars C).R ∧
      ((C.ray.outsideExponent (3 : Fin 4) : ℕ) : K) =
        ((qs_ray_degreeOne_scalars C).C : K) +
          (qs_ray_degreeOne_scalars C).S := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have haff := C.ray.zero_support_affine C.ray.outside_mem_face
  refine ⟨hout0, ?_, ?_, ?_⟩
  · have h := congrFun haff (1 : Fin 4)
    simpa [qs_ray_degreeOne_scalars,
      HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  · have h := congrFun haff (2 : Fin 4)
    simpa [qs_ray_degreeOne_scalars,
      HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  · have h := congrFun haff (3 : Fin 4)
    simpa [qs_ray_degreeOne_scalars,
      HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h

/-- **A19.91 lower codimension-two elimination.**  Under the surviving
rank-three `.qs` hypothesis, the actual degree-one outside endpoint cannot be
codimension two. -/
theorem qs_ray_outside_codimensionTwo_impossible
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtTwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary
      C.ray.outsideExponent) : False := by
  let D := qs_ray_degreeOne_scalars C
  rcases qs_ray_degreeOne_scalars_positive C hthree with ⟨hA, hB, hC⟩

  have hraw0 := qs_ray_degreeOne_raw_identity C hthree
  have hraw :
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S := by
    simpa [D, QsRayDegreeOneScalars.RawIdentity] using hraw0

  rcases qs_ray_outside_affine_data C hthree with
    ⟨hout0, h1aff0, h2aff0, h3aff0⟩
  have h1aff : ((C.ray.outsideExponent (1 : Fin 4) : ℕ) : K) =
      (D.A : K) + D.Q := by simpa [D] using h1aff0
  have h2aff : ((C.ray.outsideExponent (2 : Fin 4) : ℕ) : K) =
      (D.B : K) + D.R := by simpa [D] using h2aff0
  have h3aff : ((C.ray.outsideExponent (3 : Fin 4) : ℕ) : K) =
      (D.C : K) + D.S := by simpa [D] using h3aff0

  have hpairs :=
    HC4.Valuation.transversePair_zero_of_codimensionTwoBoundary
      C.ray.outsideExponent hout0 houtTwo
  have hall :=
    HC4.Valuation.degreeOneRaw_codimensionTwoPair_forcesAll
      hA hB hC hraw h1aff h2aff h3aff hpairs

  have houtDeg : HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent = 1 := by
    simp [HC4.Polynomial.ordinaryDegree4, hout0, hall.1, hall.2.1, hall.2.2]

  rcases C.qs_ray_strictLow_sourceCodimensionTwo_degree_lt_outside hthree with
    ⟨d, _hd, hdeg3, _hd0, _htwo, hlt⟩
  rw [houtDeg] at hlt
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
