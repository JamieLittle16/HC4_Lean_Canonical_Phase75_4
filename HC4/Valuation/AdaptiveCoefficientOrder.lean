import HC4.Valuation.AlignedSmithWallArithmetic

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Proof-independent exact parameter order of a source coefficient, local
to the adaptive first-contact construction. -/
noncomputable def adaptiveSourceCoefficientParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ := by
  classical
  exact
    if h : MvPolynomial.coeff d P = 0 then
      0
    else
      polynomialParameterOrder (MvPolynomial.coeff d P) h

/-- Proof-independent primitive part of a source coefficient.  It is zero
off the source support and has nonzero constant coefficient on the support. -/
noncomputable def adaptiveSourceCoefficientPrimitivePart
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : Polynomial K := by
  classical
  exact
    if h : MvPolynomial.coeff d P = 0 then
      0
    else
      polynomialParameterPrimitivePart (MvPolynomial.coeff d P) h

theorem adaptiveSourceCoefficient_exactFactorization
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    MvPolynomial.coeff d P =
      Polynomial.X ^ adaptiveSourceCoefficientParameterOrder P d *
        adaptiveSourceCoefficientPrimitivePart P d := by
  have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  simp only [adaptiveSourceCoefficientParameterOrder,
    adaptiveSourceCoefficientPrimitivePart, dif_neg hcoeff]
  exact polynomialParameterPrimitivePart_spec _ hcoeff

theorem adaptiveSourceCoefficientPrimitivePart_constantCoeff_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    Polynomial.constantCoeff
        (adaptiveSourceCoefficientPrimitivePart P d) ≠ 0 := by
  have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  simp only [adaptiveSourceCoefficientPrimitivePart, dif_neg hcoeff]
  exact polynomialParameterPrimitivePart_constantCoeff_ne_zero _ hcoeff

end

end HC4.Valuation
