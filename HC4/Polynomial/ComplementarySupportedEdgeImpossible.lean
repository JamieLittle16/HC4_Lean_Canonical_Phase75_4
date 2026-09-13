import HC4.Polynomial.ComplementaryLineRecognition
import HC4.Polynomial.ComplementaryEdgeRigidity
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A18.5.26: actual and exposed complementary support edges are impossible

A18.5.25 reconstructs the canonical complementary-line polynomial from an
actual multivariate support edge.  The already-green complementary-edge
rigidity theorem can therefore be applied directly to Newton output.

The second theorem removes even the edge-singularity obligation: when the
edge is an exact maximal initial form of a zero-Hessian polynomial, the
generic maximal-initial theorem supplies zero Hessian determinant
automatically.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Actual complementary support edge contradiction.** -/
theorem complementary_supported_edge_hessian_impossible
    {a1 a2 b1 b2 h k M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
    (hsupp : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M F)
    (hstart :
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0) : False := by
  let phi := complementaryLineCoefficientPolynomial a1 a2 b1 b2 h k M F
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    rw [coeff_zero_complementaryLineCoefficientPolynomial]
    exact hstart
  have hphiM : phi.coeff M ≠ 0 := by
    dsimp [phi]
    rw [coeff_M_complementaryLineCoefficientPolynomial]
    exact hend
  have hdeg : phi.natDegree ≤ M := by
    dsimp [phi]
    exact complementaryLineCoefficientPolynomial_natDegree_le
      a1 a2 b1 b2 h k M F
  have hline :
      F = complementaryLinePolynomial a1 a2 b1 b2 h k M phi := by
    dsimp [phi]
    exact eq_complementaryLinePolynomial_of_supported ha1 hh hsupp
  have hdetLine :
      hessianDeterminant
        (complementaryLinePolynomial a1 a2 b1 b2 h k M phi) = 0 := by
    rw [← hline]
    exact hdet
  exact complementary_line_hessian_impossible
    ha1 ha2 hb1 hb2 hM hh hk hphi0 hphiM hdeg hdetLine

/-- **Exposed complementary edge contradiction.**

An exact maximal initial form of a zero-Hessian carrier cannot be a genuine
complementary edge with both endpoint coefficients nonzero. -/
theorem complementary_exposed_edge_hessian_impossible
    {P : MvPolynomial (Fin 4) K}
    {w : Fin 4 → ℤ} {level : ℤ}
    {a1 a2 b1 b2 h k M : ℕ}
    (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k)
    (hbound : IsWeightLE w level P)
    (hzero : hessianDeterminant P = 0)
    (hsupp : IsSupportedOnComplementaryLine a1 a2 b1 b2 h k M
      (initialForm w level P))
    (hstart :
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M 0)
        (initialForm w level P) ≠ 0)
    (hend :
      MvPolynomial.coeff
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M M)
        (initialForm w level P) ≠ 0) : False := by
  have hdet : hessianDeterminant (initialForm w level P) = 0 :=
    hessianDeterminant_initialForm_eq_zero_of_eq_zero
      w level P hbound hzero
  exact complementary_supported_edge_hessian_impossible
    ha1 ha2 hb1 hb2 hM hh hk hsupp hstart hend hdet

end

end HC4.Polynomial
