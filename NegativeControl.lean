import HC4

-- This file must be rejected by Lean. The verification script treats a
-- successful compilation as a failure of the verification harness.
example : (0 : Nat) = 1 := by
  rfl
