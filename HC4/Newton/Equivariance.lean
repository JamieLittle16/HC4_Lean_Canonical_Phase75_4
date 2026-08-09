import HC4.Newton.ExposedFaces
import HC4.Toric.BranchReversal

/-!
# Equivariance of exposed faces

An equivalence of exponent spaces transports exposed faces by transporting the
support, the face, and the weight.  The coordinate-reversal case is then an
immediate specialisation.  This is the Newton-support counterpart of the
branch and gradient conjugacy results.
-/

namespace HC4.Newton

variable {α β : Type*}

/-- Transport an exposed face along an equivalence. -/
theorem map_exposedFace_equiv
    (e : α ≃ β)
    {S F : Set α} {w : α → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) :
    IsExposedFace (e '' S) (e '' F) (fun y => w (e.symm y)) c := by
  constructor
  · ext y
    constructor
    · rintro ⟨x, hxF, rfl⟩
      refine ⟨⟨x, hF.subset hxF, rfl⟩, ?_⟩
      simpa using hF.weight_eq hxF
    · rintro ⟨⟨x, hxS, rfl⟩, hlevel⟩
      have hxF : x ∈ F := hF.mem_iff.mpr ⟨hxS, by simpa using hlevel⟩
      exact ⟨x, hxF, rfl⟩
  · intro y hy
    rcases hy with ⟨x, hxS, rfl⟩
    simpa using hF.weight_le hxS

/-- Coordinate reversal transports an exposed face to the reversed support. -/
theorem reverse_exposedFace
    {S F : Set HC4.Toric.Exponent}
    {w : HC4.Toric.Exponent → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) :
    IsExposedFace
      (HC4.Toric.reverseSet S)
      (HC4.Toric.reverseSet F)
      (fun u => w (HC4.Toric.reverseExponent u)) c := by
  simpa [HC4.Toric.reverseSet, HC4.Toric.reverseExponentEquiv] using
    (map_exposedFace_equiv HC4.Toric.reverseExponentEquiv hF)

end HC4.Newton
