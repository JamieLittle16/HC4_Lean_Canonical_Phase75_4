import HC4.Newton.LongitudinalHessianTopDegree

/-!
# Euler cancellation with the leading mixed kernel derivatives retained

The leading coefficient `y*k(z,w)` has mixed derivatives `k_z,k_w`.
They need not vanish. Its scaled top Hessian has the exact determinant below.
The ordinary homogeneous Euler equations for `k` reduce the adjugate quadratic
term and give an obstruction on this same coefficient's transverse minor.
No claim is made that an arbitrary terminal has this homogeneous leading form.
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

end
end HC4.Newton
