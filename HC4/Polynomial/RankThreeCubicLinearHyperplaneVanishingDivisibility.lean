import HC4.Polynomial.RankThreeCubicLinearPolePointwiseDivisibility

/-!
# Vanishing on a rational linear hyperplane implies polynomial divisibility

The geometric proof is provided by
`linearPole_dvd_of_forall_pointEval_zero`, which uses a polynomial
projection onto the hyperplane and polynomial extensionality over
the characteristic-zero field. This file preserves the original API
without maintaining a second, equivalent projection proof.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- A polynomial vanishing at every rational point of a nonzero
linear hyperplane is divisible by the defining linear form. -/
theorem linearHyperplane_dvd_of_vanishes_on_plane
    (p Q : B3 K) (ell : Fin 3 → K)
    (hpoly : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (hell : ell ≠ 0)
    (hzero : ∀ z : Fin 3 → K,
      MvPolynomial.aeval z p = 0 →
        MvPolynomial.aeval z Q = 0) :
    p ∣ Q :=
  linearPole_dvd_of_forall_pointEval_zero p Q ell hpoly hell hzero

end
end HC4.Polynomial.RankThreeCubic
