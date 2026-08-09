import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Axis-normal homogeneous binary packets

Phase 91.4 proves that the HC4 fixed-kernel hypotheses force a directional
derivative to vanish.  Before transporting a general kernel direction by a
linear coordinate change, it is useful to record the exact normal form in
the coordinate-axis case.

Suppose `F` has exact transverse degree `n` in variables `i,j`:

    d i + d j = n

for every nonzero monomial `d` of `F`.

If `pderiv i F = 0`, characteristic zero forces `d i = 0` on every
nonzero monomial. Hence `d j = n`. Thus the entire transverse support of
`F` is the single monomial direction `j^n`; all remaining variation can
only occur in the other variables.

This is precisely the support-theoretic form of

    F = a(other variables) * X_j^n.

The symmetric statement holds with `i` and `j` exchanged.

The next phase can therefore focus only on transporting a general fixed
kernel direction to an axis; the homogeneous normal form on that axis is
already rigid.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Every nonzero monomial has transverse exponents `(0,n)` in the
distinguished variables `i,j`.  Other variable exponents are unrestricted. -/
def HasPureRightAxisTransverseDegree
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 ->
    d i = 0 ∧ d j = n

/-- Every nonzero monomial has transverse exponents `(n,0)`. -/
def HasPureLeftAxisTransverseDegree
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 ->
    d i = n ∧ d j = 0

/-- Pure right-axis transverse degree implies exact transverse degree. -/
theorem hasExactTransverseDegree_of_pureRightAxis
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hpure : HasPureRightAxisTransverseDegree i j n F) :
    HasExactTransverseDegree i j n F := by
  intro d hd
  rcases hpure d hd with ⟨hi, hj⟩
  simp [hi, hj]

/-- Pure left-axis transverse degree implies exact transverse degree. -/
theorem hasExactTransverseDegree_of_pureLeftAxis
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hpure : HasPureLeftAxisTransverseDegree i j n F) :
    HasExactTransverseDegree i j n F := by
  intro d hd
  rcases hpure d hd with ⟨hi, hj⟩
  simp [hi, hj]

/-- **Axis-normal homogeneous rigidity, right form.**
In characteristic zero, exact transverse degree plus vanishing first
partial derivative forces all transverse support onto the `j`-axis. -/
theorem pureRightAxis_of_pderiv_first_eq_zero_of_exactDegree
    [CharZero K]
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hexact : HasExactTransverseDegree i j n F)
    (hderiv : MvPolynomial.pderiv i F = 0) :
    HasPureRightAxisTransverseDegree i j n F := by
  intro d hd
  have hi : d i = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero i F hderiv d hd
  have hdeg : d i + d j = n := hexact d hd
  have hj : d j = n := by
    simpa [hi] using hdeg
  exact ⟨hi, hj⟩

/-- Symmetric axis-normal rigidity, left form. -/
theorem pureLeftAxis_of_pderiv_second_eq_zero_of_exactDegree
    [CharZero K]
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hexact : HasExactTransverseDegree i j n F)
    (hderiv : MvPolynomial.pderiv j F = 0) :
    HasPureLeftAxisTransverseDegree i j n F := by
  intro d hd
  have hj : d j = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero j F hderiv d hd
  have hdeg : d i + d j = n := hexact d hd
  have hi : d i = n := by
    simpa [hj] using hdeg
  exact ⟨hi, hj⟩

/-- A directional derivative in the axis direction `(1,0)` is just the
first partial derivative. -/
theorem binaryDirectionalDeriv_one_zero
    (i j : σ)
    (F : MvPolynomial σ K) :
    binaryDirectionalDeriv (1 : K) 0 i j F =
      MvPolynomial.pderiv i F := by
  simp [binaryDirectionalDeriv]

/-- A directional derivative in the axis direction `(0,1)` is just the
second partial derivative. -/
theorem binaryDirectionalDeriv_zero_one
    (i j : σ)
    (F : MvPolynomial σ K) :
    binaryDirectionalDeriv 0 (1 : K) i j F =
      MvPolynomial.pderiv j F := by
  simp [binaryDirectionalDeriv]

/-- Directional-derivative version of the right-axis normal form. -/
theorem pureRightAxis_of_axisDirectionalDeriv_eq_zero
    [CharZero K]
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hexact : HasExactTransverseDegree i j n F)
    (hdir :
      binaryDirectionalDeriv (1 : K) 0 i j F = 0) :
    HasPureRightAxisTransverseDegree i j n F := by
  apply pureRightAxis_of_pderiv_first_eq_zero_of_exactDegree
    i j n F hexact
  simpa [binaryDirectionalDeriv] using hdir

/-- Directional-derivative version of the left-axis normal form. -/
theorem pureLeftAxis_of_axisDirectionalDeriv_eq_zero
    [CharZero K]
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hexact : HasExactTransverseDegree i j n F)
    (hdir :
      binaryDirectionalDeriv 0 (1 : K) i j F = 0) :
    HasPureLeftAxisTransverseDegree i j n F := by
  apply pureLeftAxis_of_pderiv_second_eq_zero_of_exactDegree
    i j n F hexact
  simpa [binaryDirectionalDeriv] using hdir

/-- The pure-right-axis predicate is exactly the support statement that the
transverse monomial is `X_j^n`: the `i` exponent vanishes and the `j`
exponent is fixed to `n`. -/
theorem pureRightAxis_support_shape
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hpure : HasPureRightAxisTransverseDegree i j n F)
    {d : σ →₀ ℕ}
    (hd : d ∈ F.support) :
    d i = 0 ∧ d j = n := by
  apply hpure d
  simpa [MvPolynomial.mem_support_iff] using hd

/-- Symmetric support-shape statement for the left axis. -/
theorem pureLeftAxis_support_shape
    (i j : σ) (n : ℕ)
    (F : MvPolynomial σ K)
    (hpure : HasPureLeftAxisTransverseDegree i j n F)
    {d : σ →₀ ℕ}
    (hd : d ∈ F.support) :
    d i = n ∧ d j = 0 := by
  apply hpure d
  simpa [MvPolynomial.mem_support_iff] using hd

end

end HC4.Newton
