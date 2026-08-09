import HC4.Newton.FixedKernelHessian
import Mathlib.Tactic

/-!
# Positive transverse degree versus transverse independence

There is an important distinction between ordinary total homogeneity and
homogeneity in the two transverse variables of a binary Hessian packet.

The implication

    D²F = 0  ==>  DF = 0

is false for an arbitrary homogeneous polynomial: for example `F = x*y`
and `D = ∂/∂x`.

The HC4 corank-entry argument uses a stronger fact.  The two Hessian-row
kernel equations will imply that `DF` is independent of both transverse
variables, while transverse homogeneity says that every nonzero monomial
of `DF` still has strictly positive transverse degree.  Those two support
conditions are incompatible unless `DF = 0`.

This file formalises that support-theoretic incompatibility.  The next
phase will derive transverse independence from the actual Hessian-kernel
equations in characteristic zero.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Every nonzero monomial of `F` has strictly positive total exponent in
the two distinguished transverse variables `i,j`. -/
def HasPositiveTransverseSupport
    (i j : σ) (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 -> 0 < d i + d j

/-- Every nonzero monomial of `F` has exact transverse degree `n` in the
two distinguished variables `i,j`. -/
def HasExactTransverseDegree
    (i j : σ) (n : ℕ) (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 -> d i + d j = n

/-- `F` is support-theoretically independent of both transverse variables:
every nonzero monomial has exponent zero in each of them. -/
def IsTransverselyIndependent
    (i j : σ) (F : MvPolynomial σ K) : Prop :=
  ∀ d, MvPolynomial.coeff d F ≠ 0 -> d i = 0 ∧ d j = 0

/-- Positive exact transverse degree implies positive transverse support. -/
theorem hasPositiveTransverseSupport_of_exact
    (i j : σ) (n : ℕ) (F : MvPolynomial σ K)
    (hn : 0 < n)
    (hexact : HasExactTransverseDegree i j n F) :
    HasPositiveTransverseSupport i j F := by
  intro d hd
  rw [hexact d hd]
  exact hn

/-- Transverse independence forces exact transverse degree zero. -/
theorem hasExactTransverseDegree_zero_of_independent
    (i j : σ) (F : MvPolynomial σ K)
    (hind : IsTransverselyIndependent i j F) :
    HasExactTransverseDegree i j 0 F := by
  intro d hd
  rcases hind d hd with ⟨hi, hj⟩
  simp [hi, hj]

/-- **Support rigidity.**
A polynomial cannot simultaneously have positive transverse support and be
independent of both transverse variables unless it is zero. -/
theorem eq_zero_of_positiveTransverseSupport_of_independent
    (i j : σ) (F : MvPolynomial σ K)
    (hpos : HasPositiveTransverseSupport i j F)
    (hind : IsTransverselyIndependent i j F) :
    F = 0 := by
  ext d
  by_cases hd : MvPolynomial.coeff d F = 0
  · simp [hd]
  · have hposd : 0 < d i + d j := hpos d hd
    rcases hind d hd with ⟨hi, hj⟩
    have hzero : d i + d j = 0 := by
      simp [hi, hj]
    rw [hzero] at hposd
    exact False.elim ((Nat.not_lt_zero 0) hposd)

/-- Exact positive transverse degree and transverse independence are
therefore incompatible for a nonzero polynomial. -/
theorem eq_zero_of_exactPositiveTransverseDegree_of_independent
    (i j : σ) (n : ℕ) (F : MvPolynomial σ K)
    (hn : 0 < n)
    (hexact : HasExactTransverseDegree i j n F)
    (hind : IsTransverselyIndependent i j F) :
    F = 0 := by
  apply eq_zero_of_positiveTransverseSupport_of_independent i j F
  · exact hasPositiveTransverseSupport_of_exact i j n F hn hexact
  · exact hind

/-- Directional-derivative form of the support-rigidity theorem.  This is
the exact endpoint needed from the next characteristic-zero integrability
phase: once `DF` is transversely independent and retains positive
transverse degree, it must vanish. -/
theorem binaryDirectionalDeriv_eq_zero_of_exactPositiveDegree_of_independent
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K)
    (n : ℕ)
    (hn : 0 < n)
    (hexact :
      HasExactTransverseDegree i j n
        (binaryDirectionalDeriv u v i j F))
    (hind :
      IsTransverselyIndependent i j
        (binaryDirectionalDeriv u v i j F)) :
    binaryDirectionalDeriv u v i j F = 0 := by
  exact eq_zero_of_exactPositiveTransverseDegree_of_independent
    i j n (binaryDirectionalDeriv u v i j F) hn hexact hind

end

end HC4.Newton
