import HC4.Valuation.AdaptiveAlignedSmithExactFourBlockSchur
import HC4.Valuation.ActualParameterLayer
import HC4.Polynomial.HessianDeterminant
import Mathlib.Tactic

/-!
# Determinant-map API probe

Temporary.  The adaptive family/four-block APIs are now known.  This probe
only resolves the exact mathlib theorem name for commuting `Matrix.det` with
a ring hom.
-/

#check Matrix.map
#check Matrix.det_apply
#check Matrix.det_transpose
#check Matrix.det_mul
#check Matrix.det_one

#check map_det
#check Matrix.map_det
#check RingHom.map_det
#check Matrix.det_map'
#check Matrix.det_mapRingHom
