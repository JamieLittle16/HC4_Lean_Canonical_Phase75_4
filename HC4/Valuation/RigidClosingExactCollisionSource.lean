import HC4.Valuation.CanonicalSmithDefectExposureCollision
import HC4.Valuation.RigidPacketZeroSchurBridge

/-!
# Source-level data retained at a rigid determinant closing

`RigidClosingCertificate` records the rigid packet, pivot chart, exact
zero-Schur four-block, and closing clock.  The terminal associated-graded
construction additionally needs the *actual polynomial family* together with
its moving exact collision.

The previous phase had not yet transported those marked sections through the
defect-preserving Smith exposure.  `CanonicalSmithDefectExposureCollision`
now does so.  This file packages the two sides without identifying an
evaluated Schur clock with a global Newton/Rees initial form.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Everything source-level that is already forced at a rigid closing.

The family and the two sections are the *same actual objects* used by the
rigid Schur bridge.  In particular this record contains no existential
replacement family and no terminal-exposure assumption. -/
structure CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Type _ where
  closing : f.RigidClosingCertificate
  homogeneous : f.defectSmithExposureFamily.IsHomogeneous D
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K)
      f.defectSmithExposureFamily
      (alignedSmithRamificationIndex * f.defect)
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection
  leftSpecial :
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection =
      (fun _ => (0 : K))
  rightSpecial :
    polynomialSectionSpecialPoint f.defectSmithExposureRightSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  specialPoints_ne :
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection ≠
      polynomialSectionSpecialPoint f.defectSmithExposureRightSection
  specialFiberPacket :
    polynomialFamilySpecialFiber f.defectSmithExposureFamily =
      f.lossless.packet

/-- Every provenance-preserving rigid closing certificate canonically extends
to exact-collision source data on the defect-preserving exposure family. -/
noncomputable def CanonicalSmithDepartureFrontier.rigidClosingExactCollisionSourceData
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hclosing : f.RigidClosingCertificate) :
    f.RigidClosingExactCollisionSourceData :=
  { closing := hclosing
    homogeneous := f.defectSmithExposure_isHomogeneous
    hessianDefect := f.defectSmithExposure_hessianDefect
    exactCollision := f.defectSmithExposure_exactCollision
    leftSpecial := f.defectSmithExposure_leftSpecial
    rightSpecial := f.defectSmithExposure_rightSpecial
    specialPoints_ne := f.defectSmithExposure_specialPoints_ne
    specialFiberPacket := f.specialFiber_defectSmithExposure_eq_packet }

/-- Forget the closing clock and retain only the source-level pointed exact
collision on the actual exposure family. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingExactCollisionSourceData.pointedExactCollision
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingExactCollisionSourceData) :
    HasPolynomialFamilyExactGradientCollision
      f.defectSmithExposureFamily
      f.defectSmithExposureLeftSection
      f.defectSmithExposureRightSection ∧
    polynomialSectionSpecialPoint f.defectSmithExposureLeftSection ≠
      polynomialSectionSpecialPoint f.defectSmithExposureRightSection := by
  exact ⟨S.exactCollision, S.specialPoints_ne⟩

end

end HC4.Valuation
