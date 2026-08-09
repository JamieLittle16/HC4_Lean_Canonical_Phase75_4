import HC4.Newton.BinaryPivotGeometry
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Fixed-kernel binary Hessian integrability

Phase 91.1 turns a nonzero determinant-zero binary Schur packet into an
explicit one-direction square packet.  The next Hessian-specific fact is
that a fixed kernel direction annihilating both rows of the binary Hessian
also annihilates the second directional derivative of the potential.

For two variables `i,j` and a fixed scalar direction `(u,v)`, define

    D_{u,v} F = u * ∂ᵢF + v * ∂ⱼF.

If `(u,v)` lies in both Hessian rows,

    D_{u,v}(∂ᵢF) = 0,
    D_{u,v}(∂ⱼF) = 0,

then

    D_{u,v}(D_{u,v} F) = 0.

This is an actual `MvPolynomial.pderiv` theorem.  No analytic
differentiation is involved.  It is the formal integrability bridge needed
before homogeneity is used to strengthen `D²F = 0` to invariance in the
kernel direction.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Directional formal derivative in the two coordinate directions `i,j`. -/
noncomputable def binaryDirectionalDeriv
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.C u * MvPolynomial.pderiv i F +
    MvPolynomial.C v * MvPolynomial.pderiv j F

/-- The fixed direction `(u,v)` lies in both rows of the binary Hessian of
`F` in coordinates `i,j`. -/
def HasFixedBinaryHessianKernel
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K) : Prop :=
  binaryDirectionalDeriv u v i j (MvPolynomial.pderiv i F) = 0 ∧
    binaryDirectionalDeriv u v i j (MvPolynomial.pderiv j F) = 0

/-- Directional derivative distributes over a scalar linear combination of
the two first partial derivatives.  This is the formal algebra behind the
fixed-kernel Hessian argument. -/
theorem binaryDirectionalDeriv_self_expand
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K) :
    binaryDirectionalDeriv u v i j
        (binaryDirectionalDeriv u v i j F) =
      MvPolynomial.C u *
          binaryDirectionalDeriv u v i j (MvPolynomial.pderiv i F) +
        MvPolynomial.C v *
          binaryDirectionalDeriv u v i j (MvPolynomial.pderiv j F) := by
  simp only [binaryDirectionalDeriv, map_add, MvPolynomial.pderiv_C_mul]
  ring

/-- **Fixed-kernel integrability.**
If a fixed direction lies in both binary Hessian rows, the second
directional derivative of the potential in that direction vanishes. -/
theorem binaryDirectionalDeriv_sq_eq_zero_of_hessianKernel
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasFixedBinaryHessianKernel u v i j F) :
    binaryDirectionalDeriv u v i j
        (binaryDirectionalDeriv u v i j F) = 0 := by
  rw [binaryDirectionalDeriv_self_expand]
  rw [hkernel.1, hkernel.2]
  simp

/-- The two row equations can be recovered directly from the packaged
kernel predicate. -/
theorem hessianKernel_firstRow
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasFixedBinaryHessianKernel u v i j F) :
    binaryDirectionalDeriv u v i j (MvPolynomial.pderiv i F) = 0 :=
  hkernel.1

/-- Second Hessian-row form of the fixed-kernel condition. -/
theorem hessianKernel_secondRow
    (u v : K) (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasFixedBinaryHessianKernel u v i j F) :
    binaryDirectionalDeriv u v i j (MvPolynomial.pderiv j F) = 0 :=
  hkernel.2

/-- Left-pivot specialization.  The canonical kernel direction supplied by
Phase 91.1 is `(-b,a)`. -/
def HasLeftPivotHessianKernel
    (q : BinarySchurBlock K)
    (i j : σ)
    (F : MvPolynomial σ K) : Prop :=
  HasFixedBinaryHessianKernel (-q.b) q.a i j F

/-- A potential carrying the canonical left-pivot Hessian kernel has zero
second directional derivative in that kernel direction. -/
theorem leftPivot_directionalDeriv_sq_eq_zero
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot)
    (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasLeftPivotHessianKernel q i j F) :
    binaryDirectionalDeriv (-q.b) q.a i j
        (binaryDirectionalDeriv (-q.b) q.a i j F) = 0 := by
  exact binaryDirectionalDeriv_sq_eq_zero_of_hessianKernel
    (-q.b) q.a i j F hkernel

/-- The Phase 91.1 left-pivot kernel direction is genuinely nonzero, so the
directional vanishing above is not vacuous. -/
theorem leftPivot_kernelDirection_nonzero
    (q : BinarySchurBlock K)
    (hleft : q.LeftPivot) :
    (-q.b) ≠ 0 ∨ q.a ≠ 0 :=
  q.leftKernel_nonzero hleft

/-- Right-axis specialization: the fixed kernel direction is the first
coordinate axis `(1,0)`. -/
def HasRightAxisHessianKernel
    (i j : σ)
    (F : MvPolynomial σ K) : Prop :=
  HasFixedBinaryHessianKernel (1 : K) 0 i j F

/-- In the pure right-axis pivot case, the second derivative in the first
coordinate direction vanishes. -/
theorem rightAxis_directionalDeriv_sq_eq_zero
    (i j : σ)
    (F : MvPolynomial σ K)
    (hkernel : HasRightAxisHessianKernel i j F) :
    binaryDirectionalDeriv (1 : K) 0 i j
        (binaryDirectionalDeriv (1 : K) 0 i j F) = 0 := by
  exact binaryDirectionalDeriv_sq_eq_zero_of_hessianKernel
    (1 : K) 0 i j F hkernel

end

end HC4.Newton
