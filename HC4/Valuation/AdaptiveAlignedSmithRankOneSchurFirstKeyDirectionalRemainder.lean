import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLongitudinalFactor
import HC4.Newton.TransverseSliceClassification
import Mathlib.Tactic

/-!
# The unique affine remainder behind a fixed first-key Hessian direction

Stage 4B4 reduces an ordinary-homogeneous first source key to the
coefficientwise shape

    x₀^(D-m) * H_m(x₁,x₂,x₃).

The existing characteristic-zero Hessian-kernel theorem already says that,
for a *fixed* binary direction `(u,v)` in the Schur variables `(x₂,x₃)`, the
first directional derivative

    D_(u,v) R

is independent of `x₂,x₃` whenever `(u,v)` is a binary Hessian-kernel
direction of `R`.

There is one important subtlety: independence does not by itself imply that
this derivative is zero.  The Stage-4B3 grading shows that every nonzero
monomial of the derivative still has total transverse degree `m-1` and the
same longitudinal exponent `D-m`.  Hence transverse independence leaves
exactly one possible support exponent,

    x₀^(D-m) * x₁^(m-1).

This file formalises that reduction.  In particular, after the already-green
Hessian-kernel rigidity theorem, killing one single coefficient kills the
entire directional derivative.  Once that coefficient is zero, the existing
frozen-slice recurrence classifier gives the linear-power profile on every
`(x₀,x₁)`-frozen `(x₂,x₃)` slice.

Thus the next source-to-Schur provenance theorem does not have to prove a
new polynomial classification.  It only has to show that this one affine
remainder coefficient is zero (or expose the certified repair that prevents
it from vanishing).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace FirstTransverseKeyHomogeneousSliceData

/-- The only exponent at which a fixed-kernel directional derivative of the
Stage-4B3 slice can survive after transverse independence is imposed. -/
noncomputable def directionalRemainderExponent
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m) :
    Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) (S.ordinaryDegree - m) +
    Finsupp.single (1 : Fin 4) (m - 1)

/-- Before using any Hessian-kernel equation, every nonzero coefficient of a
binary directional derivative comes from an adjacent source monomial of the
Stage-4B3 slice.  Consequently it has the same longitudinal exponent and its
total transverse degree is exactly one less than the source key degree. -/
theorem binaryDirectionalDeriv_supportShape
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (u v : K)
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) ≠ 0) :
    d (0 : Fin 4) = S.ordinaryDegree - m ∧
      pureLongitudinalTransverseDegree d + 1 = m := by
  let d2 : Fin 4 →₀ ℕ := d + Finsupp.single (2 : Fin 4) 1
  let d3 : Fin 4 →₀ ℕ := d + Finsupp.single (3 : Fin 4) 1

  have hsource :
      MvPolynomial.coeff d2 S.slice ≠ 0 ∨
        MvPolynomial.coeff d3 S.slice ≠ 0 := by
    by_cases h2 : MvPolynomial.coeff d2 S.slice ≠ 0
    · exact Or.inl h2
    · by_cases h3 : MvPolynomial.coeff d3 S.slice ≠ 0
      · exact Or.inr h3
      · have h2z : MvPolynomial.coeff d2 S.slice = 0 := not_ne_iff.mp h2
        have h3z : MvPolynomial.coeff d3 S.slice = 0 := not_ne_iff.mp h3
        have hcoeff :=
          coeff_binaryDirectionalDeriv
            u v (2 : Fin 4) (3 : Fin 4) S.slice d
        change
          MvPolynomial.coeff d
              (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) =
            u *
                (MvPolynomial.coeff d2 S.slice *
                  ((d (2 : Fin 4) + 1 : ℕ) : K)) +
              v *
                (MvPolynomial.coeff d3 S.slice *
                  ((d (3 : Fin 4) + 1 : ℕ) : K)) at hcoeff
        rw [h2z, h3z] at hcoeff
        simp only [zero_mul, mul_zero, add_zero] at hcoeff
        exact False.elim (hd hcoeff)

  rcases hsource with h2 | h3
  · have hlong := S.slice_longitudinalExponent d2 h2
    have htrans := S.slice_exactTransverseDegree d2 h2
    have h0 : d2 (0 : Fin 4) = d (0 : Fin 4) := by
      simp [d2]
    have h1 : d2 (1 : Fin 4) = d (1 : Fin 4) := by
      simp [d2]
    have h2coord : d2 (2 : Fin 4) = d (2 : Fin 4) + 1 := by
      simp [d2]
    have h3coord : d2 (3 : Fin 4) = d (3 : Fin 4) := by
      simp [d2]
    rw [h0] at hlong
    unfold pureLongitudinalTransverseDegree at htrans ⊢
    rw [h1, h2coord, h3coord] at htrans
    constructor
    · exact hlong
    · omega
  · have hlong := S.slice_longitudinalExponent d3 h3
    have htrans := S.slice_exactTransverseDegree d3 h3
    have h0 : d3 (0 : Fin 4) = d (0 : Fin 4) := by
      simp [d3]
    have h1 : d3 (1 : Fin 4) = d (1 : Fin 4) := by
      simp [d3]
    have h2coord : d3 (2 : Fin 4) = d (2 : Fin 4) := by
      simp [d3]
    have h3coord : d3 (3 : Fin 4) = d (3 : Fin 4) + 1 := by
      simp [d3]
    rw [h0] at hlong
    unfold pureLongitudinalTransverseDegree at htrans ⊢
    rw [h1, h2coord, h3coord] at htrans
    constructor
    · exact hlong
    · omega

/-- Exact support description of the only possible affine remainder after a
fixed binary Hessian-kernel direction has been imposed. -/
theorem binaryDirectionalDeriv_affineRemainderSupport
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (u v : K)
    (hkernel :
      HasFixedBinaryHessianKernel
        u v (2 : Fin 4) (3 : Fin 4) S.slice) :
    ∀ d : Fin 4 →₀ ℕ,
      MvPolynomial.coeff d
          (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) ≠ 0 →
        d (0 : Fin 4) = S.ordinaryDegree - m ∧
          d (1 : Fin 4) + 1 = m ∧
          d (2 : Fin 4) = 0 ∧
          d (3 : Fin 4) = 0 := by
  have hind :
      IsTransverselyIndependent
        (2 : Fin 4) (3 : Fin 4)
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) :=
    binaryDirectionalDeriv_independent_of_hessianKernel
      u v (2 : Fin 4) (3 : Fin 4) S.slice hkernel
  intro d hd
  rcases S.binaryDirectionalDeriv_supportShape u v d hd with ⟨h0, htrans⟩
  rcases hind d hd with ⟨h2, h3⟩
  have h1 : d (1 : Fin 4) + 1 = m := by
    unfold pureLongitudinalTransverseDegree at htrans
    rw [h2, h3] at htrans
    omega
  exact ⟨h0, h1, h2, h3⟩

/-- Every surviving coefficient of the fixed-kernel directional derivative
is located at the single canonical affine-remainder exponent. -/
theorem binaryDirectionalDeriv_support_eq_remainderExponent
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (u v : K)
    (hkernel :
      HasFixedBinaryHessianKernel
        u v (2 : Fin 4) (3 : Fin 4) S.slice)
    (d : Fin 4 →₀ ℕ)
    (hd :
      MvPolynomial.coeff d
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) ≠ 0) :
    d = S.directionalRemainderExponent := by
  rcases S.binaryDirectionalDeriv_affineRemainderSupport
      u v hkernel d hd with ⟨h0, h1, h2, h3⟩
  have hmpos : 0 < m := by omega
  ext i
  fin_cases i
  · simpa [directionalRemainderExponent] using h0
  · simp [directionalRemainderExponent]
    omega
  · simpa [directionalRemainderExponent] using h2
  · simpa [directionalRemainderExponent] using h3

/-- **One-coefficient reduction of fixed first-key directional rigidity.**

The existing Hessian-kernel theorem reduces the directional derivative to a
single possible support exponent.  Therefore vanishing of that one
coefficient forces the complete directional derivative to vanish. -/
theorem binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_remainderCoeff_eq_zero
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (u v : K)
    (hkernel :
      HasFixedBinaryHessianKernel
        u v (2 : Fin 4) (3 : Fin 4) S.slice)
    (hrem :
      MvPolynomial.coeff S.directionalRemainderExponent
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) = 0) :
    binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice = 0 := by
  ext d
  by_cases hd :
      MvPolynomial.coeff d
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) = 0
  · simpa [hd]
  · have heq :=
      S.binaryDirectionalDeriv_support_eq_remainderExponent
        u v hkernel d hd
    rw [heq, hrem]
    simp

/-- Once the unique affine remainder is killed, do not reprove the binary
classification: every frozen `(x₀,x₁)` slice is exactly the already-green
linear-power binomial profile. -/
theorem frozenBinarySlice_eq_binomialProfile_of_remainderCoeff_eq_zero
    {Q : MvPolynomial (Fin 4) K}
    {m : ℕ}
    (S : FirstTransverseKeyHomogeneousSliceData Q m)
    (u v : K)
    (hu : u ≠ 0)
    (hkernel :
      HasFixedBinaryHessianKernel
        u v (2 : Fin 4) (3 : Fin 4) S.slice)
    (hrem :
      MvPolynomial.coeff S.directionalRemainderExponent
        (binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice) = 0)
    (r : Fin 4 →₀ ℕ)
    (hr2 : r (2 : Fin 4) = 0)
    (hr3 : r (3 : Fin 4) = 0)
    (n : ℕ) :
    ∀ k, k ≤ n →
      transverseSliceCoeff S.slice r (2 : Fin 4) (3 : Fin 4) n k =
        linearPowerScalar u n
            (transverseSliceCoeff S.slice r (2 : Fin 4) (3 : Fin 4) n) *
          ((Nat.choose n k : ℕ) : K) *
          v ^ k *
          (-u) ^ (n - k) := by
  have hdir :
      binaryDirectionalDeriv u v (2 : Fin 4) (3 : Fin 4) S.slice = 0 :=
    S.binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_remainderCoeff_eq_zero
      u v hkernel hrem
  exact
    transverseSlice_eq_binomialProfile
      u v hu (by decide) S.slice hdir r hr2 hr3 n

end FirstTransverseKeyHomogeneousSliceData

end

end HC4.Valuation
