import HC4.Newton.LongitudinalHessianTopDegree

/-!
# Euler cancellation with leading mixed kernel derivatives retained

The leading coefficient `y*k(z,w)` has mixed derivatives `k_z,k_w`.
They need not vanish. Its scaled top Hessian has the exact determinant below.
The ordinary homogeneous Euler equations for `k` reduce the adjugate quadratic
term and give an obstruction on this same coefficient's transverse minor.

The second half records the genuinely bidegree-symmetric version.  For a
single carrier `x^n y^r k(z,w)`, after multiplying the `x` and `y` Hessian
rows and columns by their corresponding variables, the entire top matrix is
`bigradedHessianCoupledKernelBlock`.  Its determinant has a closed form, and
Euler homogeneity of `k` again collapses the gradient-adjugate correction.
This is the algebraic engine needed for an exposed mixed `(n,r)` source
vertex; no claim is made here that an arbitrary terminal already supplies
such a uniquely exposed carrier.
-/

namespace HC4.Newton
noncomputable section
variable {R : Type*} [CommRing R]

def longitudinalHessianCoupledKernelBlock
    (n k kz kw kzz kzw kww : R) : GeneralFourBlock R where
  a := n*(n-1)*k
  b := n*k
  p := n*kz
  q := n*kw
  d := 0
  r := kz
  s := kw
  x := kzz
  y := kzw
  z := kww

/-- The mixed kernel entries are retained literally. -/
theorem longitudinalHessianCoupledKernelBlock_determinant
    (n k kz kw kzz kzw kww : R) :
    (longitudinalHessianCoupledKernelBlock n k kz kw kzz kzw kww).determinantCore =
      -n*k*(n*k*(kzz*kww-kzw^2) -
        (n+1)*(kz^2*kww-2*kz*kw*kzw+kw^2*kzz)) := by
  simp only [longitudinalHessianCoupledKernelBlock, GeneralFourBlock.determinantCore]
  ring

/-- Euler and its two derivatives identify the adjugate quadratic form,
without division by the homogeneous degree minus one. -/
theorem binary_euler_adjugate_quadratic
    (m z w k kz kw kzz kzw kww : R)
    (he : z*kz+w*kw=m*k)
    (hez : z*kzz+w*kzw=(m-1)*kz)
    (hew : z*kzw+w*kww=(m-1)*kw) :
    (m-1)*(kz^2*kww-2*kz*kw*kzw+kw^2*kzz) = m*k*(kzz*kww-kzw^2) := by
  linear_combination (kzz*kww-kzw^2)*he -
    (kz*kww-kw*kzw)*hez - (kw*kzz-kz*kzw)*hew

/-- A polynomial identity, valid even in homogeneous degree one. -/
theorem longitudinalHessianCoupledKernelBlock_euler_determinant
    (n m z w k kz kw kzz kzw kww : R)
    (he : z*kz+w*kw=m*k)
    (hez : z*kzz+w*kzw=(m-1)*kz)
    (hew : z*kzw+w*kww=(m-1)*kw) :
    (m-1)*(longitudinalHessianCoupledKernelBlock n k kz kw kzz kzw kww).determinantCore =
      n*(n+m)*k^2*(kzz*kww-kzw^2) := by
  rw [longitudinalHessianCoupledKernelBlock_determinant]
  have hq := binary_euler_adjugate_quadratic m z w k kz kw kzz kzw kww he hez hew
  linear_combination n*k*(n+1)*hq

/-- A singular coupled top matrix with an ordinary homogeneous kernel
coefficient has either zero kernel coefficient or zero transverse minor.
This replaces the zero-mixed-derivative hypothesis by literal Euler equations. -/
theorem longitudinalHessianCoupledKernelBlock_kernel_or_minor_eq_zero
    [IsDomain R] [CharZero R]
    (n m : ℕ) (hn : 0 < n) (z w k kz kw kzz kzw kww : R)
    (he : z*kz+w*kw=(m : R)*k)
    (hez : z*kzz+w*kzw=((m : R)-1)*kz)
    (hew : z*kzw+w*kww=((m : R)-1)*kw)
    (hdet : (longitudinalHessianCoupledKernelBlock (n : R) k kz kw kzz kzw kww).determinantCore = 0) :
    k = 0 ∨ kzz*kww-kzw^2 = 0 := by
  have h := longitudinalHessianCoupledKernelBlock_euler_determinant
    (n : R) (m : R) z w k kz kw kzz kzw kww he hez hew
  rw [hdet, mul_zero] at h
  have hnR : (n : R) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnm : (n : R)+(m : R) ≠ 0 := by
    have hp : 0 < n+m := by omega
    exact_mod_cast Nat.ne_of_gt hp
  have hprod : k^2*(kzz*kww-kzw^2) = 0 := by
    apply (mul_eq_zero.mp (show (n : R)*((n : R)+(m : R)) *
      (k^2*(kzz*kww-kzw^2)) = 0 by linear_combination -h)).resolve_left
    exact mul_ne_zero hnR hnm
  rcases mul_eq_zero.mp hprod with hk | hminor
  · exact Or.inl (pow_eq_zero hk)
  · exact Or.inr hminor

/-! ## Two marked source coordinates -/

/-- The balanced Hessian block of a single carrier `x^n y^r k(z,w)`.
Multiplying the `x` and `y` Hessian rows and columns by `x` and `y`
respectively restores the original `(n,r)` bidegree in every entry. -/
def bigradedHessianCoupledKernelBlock
    (n r k kz kw kzz kzw kww : R) : GeneralFourBlock R where
  a := n*(n-1)*k
  b := n*r*k
  p := n*kz
  q := n*kw
  d := r*(r-1)*k
  r := r*kz
  s := r*kw
  x := kzz
  y := kzw
  z := kww

/-- Exact determinant of the balanced Hessian block of `x^n y^r k(z,w)`.
The formula is symmetric in the two marked exponents `n,r`. -/
theorem bigradedHessianCoupledKernelBlock_determinant
    (n r k kz kw kzz kzw kww : R) :
    (bigradedHessianCoupledKernelBlock n r k kz kw kzz kzw kww).determinantCore =
      -n*r*k *
        ((n+r-1)*k*(kzz*kww-kzw^2) -
          (n+r)*(kz^2*kww-2*kz*kw*kzw+kw^2*kzz)) := by
  simp only [bigradedHessianCoupledKernelBlock, GeneralFourBlock.determinantCore]
  ring

/-- Euler collapse for the full mixed-bidegree block.  If `k` is homogeneous
of ordinary degree `m`, its three Euler equations turn the determinant into
one scalar times `k^2` times the binary transverse Hessian minor.  No division
by `m-1` is used. -/
theorem bigradedHessianCoupledKernelBlock_euler_determinant
    (n r m z w k kz kw kzz kzw kww : R)
    (he : z*kz+w*kw=m*k)
    (hez : z*kzz+w*kzw=(m-1)*kz)
    (hew : z*kzw+w*kww=(m-1)*kw) :
    (m-1) *
        (bigradedHessianCoupledKernelBlock n r k kz kw kzz kzw kww).determinantCore =
      n*r*(n+r+m-1)*k^2*(kzz*kww-kzw^2) := by
  rw [bigradedHessianCoupledKernelBlock_determinant]
  have hq := binary_euler_adjugate_quadratic m z w k kz kw kzz kzw kww he hez hew
  linear_combination n*r*k*(n+r)*hq

/-- Domain-level consumer for an exposed mixed carrier.  The arithmetic
nonvanishing assumptions are stated directly in the coefficient ring so the
lemma is reusable for natural, integer, or already-cast source exponents. -/
theorem bigradedHessianCoupledKernelBlock_kernel_or_minor_eq_zero
    [IsDomain R]
    (n r m z w k kz kw kzz kzw kww : R)
    (hn : n ≠ 0) (hr : r ≠ 0) (hnrm : n+r+m-1 ≠ 0)
    (he : z*kz+w*kw=m*k)
    (hez : z*kzz+w*kzw=(m-1)*kz)
    (hew : z*kzw+w*kww=(m-1)*kw)
    (hdet :
      (bigradedHessianCoupledKernelBlock n r k kz kw kzz kzw kww).determinantCore = 0) :
    k = 0 ∨ kzz*kww-kzw^2 = 0 := by
  have h := bigradedHessianCoupledKernelBlock_euler_determinant
    n r m z w k kz kw kzz kzw kww he hez hew
  rw [hdet, mul_zero] at h
  have hscalar : n*r*(n+r+m-1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn hr) hnrm
  have hprod : k^2*(kzz*kww-kzw^2) = 0 := by
    apply (mul_eq_zero.mp
      (show (n*r*(n+r+m-1)) * (k^2*(kzz*kww-kzw^2)) = 0 by
        linear_combination -h)).resolve_left
    exact hscalar
  rcases mul_eq_zero.mp hprod with hk | hminor
  · exact Or.inl (pow_eq_zero hk)
  · exact Or.inr hminor

end
end HC4.Newton
