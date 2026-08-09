import HC4.Newton.TransverseSliceClassification
import Mathlib.Tactic

/-!
# Packet-level linear-power normal form

Phase 91.10 proves the linear-power classification on every frozen external
coefficient slice of an `MvPolynomial`.

This file packages those slice theorems into the packet-level normal form
used by the HC4 corank-entry argument.

For fixed transverse variables `i,j`, degree `n`, and direction `(u,v)`,
we say that `F` has linear-power transverse normal form if

1. every nonzero monomial of `F` has exact transverse degree `n`; and
2. there is an amplitude function `a(r)`, depending only on a frozen
   external exponent vector `r` with `r i = r j = 0`, such that

       coeff(r + k e_i + (n-k)e_j, F)
         = a(r) * choose(n,k) * v^k * (-u)^(n-k)

   for every `k ≤ n`.

This is the precise coefficientwise content of

    F = a(X) * (v Y_i - u Y_j)^n,

where `X` denotes the non-transverse variables.

No arbitrary linear-change API or polynomial factorisation infrastructure
is required: the statement is exactly what the later Newton/Rees argument
uses.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Canonical amplitude attached to a frozen external exponent vector.
It is chosen from the left endpoint of the transverse slice. -/
def transverseSliceAmplitude
    (u : K)
    (F : MvPolynomial σ K)
    (r : σ →₀ ℕ)
    (i j : σ)
    (n : ℕ) : K :=
  linearPowerScalar u n (transverseSliceCoeff F r i j n)

/-- Coefficientwise packet-level normal form corresponding to
`a(X) * (v Y_i - u Y_j)^n`. -/
def HasLinearPowerTransverseNormalForm
    (u v : K)
    (i j : σ)
    (n : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  HasExactTransverseDegree i j n F ∧
    ∃ a : (σ →₀ ℕ) → K,
      ∀ r,
        r i = 0 ->
        r j = 0 ->
        ∀ k, k ≤ n ->
          transverseSliceCoeff F r i j n k =
            a r *
              ((Nat.choose n k : ℕ) : K) *
              v ^ k *
              (-u) ^ (n - k)

/-- The canonical amplitude function realises the normal form once the
directional derivative vanishes. -/
theorem transverseSlice_eq_canonicalAmplitude
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (F : MvPolynomial σ K)
    (hdir : binaryDirectionalDeriv u v i j F = 0)
    (r : σ →₀ ℕ)
    (hri : r i = 0)
    (hrj : r j = 0)
    (n k : ℕ)
    (hk : k ≤ n) :
    transverseSliceCoeff F r i j n k =
      transverseSliceAmplitude u F r i j n *
        ((Nat.choose n k : ℕ) : K) *
        v ^ k *
        (-u) ^ (n - k) := by
  unfold transverseSliceAmplitude
  exact transverseSlice_eq_binomialProfile
    u v hu hij F hdir r hri hrj n k hk

/-- **Packet-level linear-power normal form.**
Exact transverse degree together with a nonzero fixed direction annihilating
`F` forces the entire packet into the coefficientwise form
`a(X) * (v Y_i - u Y_j)^n`. -/
theorem hasLinearPowerTransverseNormalForm_of_directionalDeriv_eq_zero
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (n : ℕ)
    (F : MvPolynomial σ K)
    (hexact : HasExactTransverseDegree i j n F)
    (hdir : binaryDirectionalDeriv u v i j F = 0) :
    HasLinearPowerTransverseNormalForm u v i j n F := by
  refine ⟨hexact, ?_⟩
  refine ⟨(fun r => transverseSliceAmplitude u F r i j n), ?_⟩
  intro r hri hrj k hk
  exact transverseSlice_eq_canonicalAmplitude
    u v hu hij F hdir r hri hrj n k hk

/-- Direct composition with the Phase 91.4 Hessian-kernel rigidity theorem.
If the fixed Hessian-kernel direction is nonzero in its first component and
the first directional derivative has positive exact transverse degree, then
that derivative vanishes.  If the original packet itself has exact
transverse degree `n`, this theorem packages the resulting linear-power
normal form once directional vanishing is supplied. -/
theorem hasLinearPowerTransverseNormalForm_of_hessianKernel
    [CharZero K]
    (u v : K)
    (hu : u ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (n m : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmpos : 0 < m)
    (hexactD :
      HasExactTransverseDegree i j m
        (binaryDirectionalDeriv u v i j F))
    (hkernel : HasFixedBinaryHessianKernel u v i j F) :
    HasLinearPowerTransverseNormalForm u v i j n F := by
  apply hasLinearPowerTransverseNormalForm_of_directionalDeriv_eq_zero
    u v hu hij n F hexactF
  exact
    binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree
      u v i j F m hmpos hkernel hexactD

/-- Left-pivot specialization using the canonical nonzero kernel direction
`(-b,a)`.  The hypothesis `q.b ≠ 0` selects the orientation in which the
first direction scalar `-b` is nonzero; the complementary case is already
the axis-normal branch handled by Phase 91.5. -/
theorem hasLinearPowerTransverseNormalForm_of_leftPivotKernel
    [CharZero K]
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (hb : q.b ≠ 0)
    {i j : σ}
    (hij : i ≠ j)
    (n m : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmpos : 0 < m)
    (hexactD :
      HasExactTransverseDegree i j m
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hkernel : HasLeftPivotHessianKernel q i j F) :
    HasLinearPowerTransverseNormalForm
      (-q.b) q.a i j n F := by
  have hu : -q.b ≠ 0 := neg_ne_zero.mpr hb
  exact
    hasLinearPowerTransverseNormalForm_of_hessianKernel
      (-q.b) q.a hu hij n m F
      hexactF hmpos hexactD hkernel

end

end HC4.Newton
