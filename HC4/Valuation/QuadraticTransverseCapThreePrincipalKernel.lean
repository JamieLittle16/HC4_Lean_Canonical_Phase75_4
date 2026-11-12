import HC4.Valuation.QuadraticTransverseCapTwoRowKernel
import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# All three principal Schur pivots give the same kernel line

The polynomial singular-transverse branch now supplies one of the three
original principal 2x2 minors, not necessarily the (0,1) minor.

A symmetric 3x3 matrix over a domain with an active principal 2x2 pivot
has a one-dimensional kernel. We prove its three wedge identities
directly from the existing two-row theorem, using finite *index
reorderings*, not new source coordinates or a hypothetical source shear.

This removes the artificial (0,1)-pivot restriction from the
unimodular polynomial drift endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every principal 2x2 pivot alternative yields the full wedge
identities for any two kernel vectors of the same symmetric 3x3 block. -/
theorem quadraticTransverse_threePrincipalKernel_wedges
    (C : GeneralThreeBlock R)
    (w z : Fin 3 → R)
    (hpivot :
      C.d * C.f - C.e * C.e ≠ 0 ∨
      C.a * C.f - C.c * C.c ≠ 0 ∨
      C.a * C.d - C.b * C.b ≠ 0)
    (hw0 : C.a * w 0 + C.b * w 1 + C.c * w 2 = 0)
    (hw1 : C.b * w 0 + C.d * w 1 + C.e * w 2 = 0)
    (hw2 : C.c * w 0 + C.e * w 1 + C.f * w 2 = 0)
    (hz0 : C.a * z 0 + C.b * z 1 + C.c * z 2 = 0)
    (hz1 : C.b * z 0 + C.d * z 1 + C.e * z 2 = 0)
    (hz2 : C.c * z 0 + C.e * z 1 + C.f * z 2 = 0) :
    (w 0 * z 1 - w 1 * z 0 = 0) ∧
    (w 0 * z 2 - w 2 * z 0 = 0) ∧
    (w 1 * z 2 - w 2 * z 1 = 0) := by
  rcases hpivot with h12 | h02 | h01
  · -- Pivot (1,2), with the remaining coordinate moved to position 2.
    let ww : Fin 3 → R := ![w 1, w 2, w 0]
    let zz : Fin 3 → R := ![z 1, z 2, z 0]
    have hww0 :
        C.d * ww 0 + C.e * ww 1 + C.b * ww 2 = 0 := by
      change C.d * w 1 + C.e * w 2 + C.b * w 0 = 0
      linear_combination hw1
    have hww1 :
        C.e * ww 0 + C.f * ww 1 + C.c * ww 2 = 0 := by
      change C.e * w 1 + C.f * w 2 + C.c * w 0 = 0
      linear_combination hw2
    have hzz0 :
        C.d * zz 0 + C.e * zz 1 + C.b * zz 2 = 0 := by
      change C.d * z 1 + C.e * z 2 + C.b * z 0 = 0
      linear_combination hz1
    have hzz1 :
        C.e * zz 0 + C.f * zz 1 + C.c * zz 2 = 0 := by
      change C.e * z 1 + C.f * z 2 + C.c * z 0 = 0
      linear_combination hz2
    obtain ⟨hfirst, hsecond, hthird⟩ :=
      quadraticTransverse_twoRowPrincipalKernel_wedges
        C.d C.e C.b C.f C.c ww zz h12 hww0 hww1 hzz0 hzz1
    have h12' : w 1 * z 2 - w 2 * z 1 = 0 := by
      simpa [ww, zz] using hfirst
    have h10' : w 1 * z 0 - w 0 * z 1 = 0 := by
      simpa [ww, zz] using hsecond
    have h20' : w 2 * z 0 - w 0 * z 2 = 0 := by
      simpa [ww, zz] using hthird
    refine ⟨?_, ?_, h12'⟩
    · linear_combination -h10'
    · linear_combination -h20'
  · -- Pivot (0,2), with the remaining coordinate moved to position 2.
    let ww : Fin 3 → R := ![w 0, w 2, w 1]
    let zz : Fin 3 → R := ![z 0, z 2, z 1]
    have hww0 :
        C.a * ww 0 + C.c * ww 1 + C.b * ww 2 = 0 := by
      change C.a * w 0 + C.c * w 2 + C.b * w 1 = 0
      linear_combination hw0
    have hww1 :
        C.c * ww 0 + C.f * ww 1 + C.e * ww 2 = 0 := by
      change C.c * w 0 + C.f * w 2 + C.e * w 1 = 0
      linear_combination hw2
    have hzz0 :
        C.a * zz 0 + C.c * zz 1 + C.b * zz 2 = 0 := by
      change C.a * z 0 + C.c * z 2 + C.b * z 1 = 0
      linear_combination hz0
    have hzz1 :
        C.c * zz 0 + C.f * zz 1 + C.e * zz 2 = 0 := by
      change C.c * z 0 + C.f * z 2 + C.e * z 1 = 0
      linear_combination hz2
    obtain ⟨hfirst, hsecond, hthird⟩ :=
      quadraticTransverse_twoRowPrincipalKernel_wedges
        C.a C.c C.b C.f C.e ww zz h02 hww0 hww1 hzz0 hzz1
    have h02' : w 0 * z 2 - w 2 * z 0 = 0 := by
      simpa [ww, zz] using hfirst
    have h01' : w 0 * z 1 - w 1 * z 0 = 0 := by
      simpa [ww, zz] using hsecond
    have h21' : w 2 * z 1 - w 1 * z 2 = 0 := by
      simpa [ww, zz] using hthird
    refine ⟨h01', h02', ?_⟩
    · linear_combination -h21'
  · exact quadraticTransverse_twoRowPrincipalKernel_wedges
      C.a C.b C.c C.d C.e w z h01 hw0 hw1 hz0 hz1

end

end HC4.Valuation
