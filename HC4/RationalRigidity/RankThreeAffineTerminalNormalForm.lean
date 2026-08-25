import HC4.RationalRigidity.RankThreeTranslatedPurePower
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import Mathlib.Tactic

/-!
# A18.5.39: complete scalar normal form of an honest affine rank-three terminal

The terminal splice should not repeatedly reopen the autonomous-rigidity
stack.  By A18.5.31, A18.5.35--38, and the affine top-boundary theorem, an
honest singular affine rank-three edge has four simultaneous consequences:

* the omitted-coordinate step is primitive, `P = 1`;
* the first positive coefficient layer is genuinely present;
* after translation to a nonzero root the coefficient polynomial is a
  nonzero scalar multiple of `X^D`, where `D = natDegree phi`;
* the far exponent `L.exponent D` lies on the toric boundary.

This file packages those already-proved facts into the endpoint interface
wanted by the remaining toric/pencil classification.  No new ODE or Hessian
calculation is introduced here.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complete scalar/geometric normal form attached to a genuine affine
rank-three terminal certificate. -/
structure RankThreeAffineTerminalNormalForm
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C P Q R S phi) where
  unitLongitudinalStep : P = 1
  firstLayer_ne : phi.coeff 1 ≠ 0
  root : K
  scalar : K
  root_ne : root ≠ 0
  scalar_ne : scalar ≠ 0
  translatedPurePower :
    HC4.Polynomial.translatePolynomial root phi =
      Polynomial.C scalar * Polynomial.X ^ phi.natDegree
  topBoundary : MvExponentOnBoundary (L.exponent phi.natDegree)

/-- **Affine terminal normal form.**  All scalar autonomous analysis is now
hidden behind one lossless package for the terminal toric/pencil endgame. -/
theorem rankThreeAffineTerminal_normalForm
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C P Q R S phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    Nonempty (RankThreeAffineTerminalNormalForm L) := by
  have hstep :=
    rankThree_unit_longitudinal_step_of_certificate
      hA hB hC hP hphiDeg hphi0 hcert
  rcases hstep with ⟨hPone, hphi1⟩
  rcases exists_rankThree_translated_pure_power
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨alpha, c, halpha, hc, hpure⟩
  have hboundary :=
    rankThreeAffineLine_topExponent_on_boundary_of_certificate
      L hA hB hC hP hphiDeg hphi0 hcert
  exact ⟨{
    unitLongitudinalStep := hPone
    firstLayer_ne := hphi1
    root := alpha
    scalar := c
    root_ne := halpha
    scalar_ne := hc
    translatedPurePower := hpure
    topBoundary := hboundary
  }⟩

end

end HC4.RationalRigidity
