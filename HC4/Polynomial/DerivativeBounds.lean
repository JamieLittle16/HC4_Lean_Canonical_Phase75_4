import HC4.Polynomial.WeightBounds
import HC4.Polynomial.DerivativeWeight

/-!
# Differentiation of weak and strict weight bounds

Using the already verified commutation of exact weighted components with
`pderiv`, differentiation lowers both weak and strict upper weight bounds by
the weight of the differentiated variable.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

variable {σ K : Type*} [CommRing K] [DecidableEq σ]

/-- Partial differentiation lowers a weak weight bound. -/
theorem IsWeightLE.pderiv
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (i : σ) :
    IsWeightLE w (m - w i) (MvPolynomial.pderiv i p) := by
  intro d hd
  by_contra hnot
  have hgt : m - w i < Finsupp.weight w d := by omega
  let n : ℤ := Finsupp.weight w d
  have htop : initialForm w n (MvPolynomial.pderiv i p) = 0 := by
    have hmn : m < n + w i := by
      dsimp [n]
      omega
    have hpzero : initialForm w (n + w i) p = 0 :=
      initialForm_eq_zero_of_isWeightLE hp hmn
    have hcomm := pderiv_initialForm w (n + w i) p i
    have hshift : n + w i - w i = n := by abel
    rw [hpzero, hshift] at hcomm
    simpa using hcomm.symm
  have hcoeff : coeff d (MvPolynomial.pderiv i p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcomponent :
      coeff d (initialForm w n (MvPolynomial.pderiv i p)) =
        coeff d (MvPolynomial.pderiv i p) := by
    rw [coeff_initialForm]
    simp [n]
  rw [htop] at hcomponent
  simp at hcomponent
  exact hcoeff hcomponent.symm

/-- Partial differentiation lowers a strict weight bound. -/
theorem IsWeightLT.pderiv
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (i : σ) :
    IsWeightLT w (m - w i) (MvPolynomial.pderiv i p) := by
  intro d hd
  by_contra hnot
  have hge : m - w i ≤ Finsupp.weight w d := by omega
  let n : ℤ := Finsupp.weight w d
  have htop : initialForm w n (MvPolynomial.pderiv i p) = 0 := by
    have hmn : m ≤ n + w i := by
      dsimp [n]
      omega
    have hpzero : initialForm w (n + w i) p = 0 :=
      initialForm_eq_zero_of_isWeightLT hp hmn
    have hcomm := pderiv_initialForm w (n + w i) p i
    have hshift : n + w i - w i = n := by abel
    rw [hpzero, hshift] at hcomm
    simpa using hcomm.symm
  have hcoeff : coeff d (MvPolynomial.pderiv i p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcomponent : coeff d (initialForm w n (MvPolynomial.pderiv i p)) = coeff d (MvPolynomial.pderiv i p) := by
    rw [coeff_initialForm]
    simp [n]
  rw [htop] at hcomponent
  simp at hcomponent
  exact hcoeff hcomponent.symm

/-- Hessian entries lower a weak bound by both variable weights. -/
theorem IsWeightLE.hessian_entry
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLE w m p) (i j : σ) :
    IsWeightLE w (m - w i - w j) (hessian p i j) := by
  exact (hp.pderiv i).pderiv j

/-- Hessian entries lower a strict bound by both variable weights. -/
theorem IsWeightLT.hessian_entry
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : IsWeightLT w m p) (i j : σ) :
    IsWeightLT w (m - w i - w j) (hessian p i j) := by
  exact (hp.pderiv i).pderiv j

end

end HC4.Polynomial
