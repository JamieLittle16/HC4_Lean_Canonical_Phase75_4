import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHomogeneousRigidity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Pointed reflection of the final mixed-degree blocker

After the degree-pure blocker has been eliminated, the only concrete blocker
geometry is an explicit mixed-degree pair in the longitudinally right-
recentered raw special fibre

    F_rec(x₀,x⊥) = F(x₀ + 1,x⊥).

For the eventual family-level Rees exposure we want to keep the marked
collision in the canonical order `0 ~ e₀`.  The affine involution

    x₀ ↦ 1 - x₀

does exactly that: it swaps the two distinguished source points.  Static
mixedness is preserved because

    F(1 - x₀,x⊥)
      = sign₀ (F(x₀ + 1,x⊥)),

where `sign₀` is the linear involution `x₀ ↦ -x₀`.

The key proof below deliberately avoids coefficient-by-coefficient support
transport.  Linear sign substitution preserves every ordinary homogeneous
degree, and is an involution.  Hence if the pointed reflection were
homogeneous, the recentered fibre would be homogeneous too, contradicting
the two explicit ordinary degrees retained by
`AdaptiveAlignedSmithMixedDegreeBlockerEndpoint`.

No Hessian/collision covariance is claimed here; this is the static support
bridge needed before the actual family-level pointed reflection.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Linear sign change in the distinguished longitudinal source coordinate:
`x₀ ↦ -x₀`, with all transverse coordinates fixed. -/
noncomputable def longitudinalSignHom :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases
      (-MvPolynomial.X (0 : Fin 4))
      (fun j : Fin 3 => MvPolynomial.X j.succ))

@[simp]
theorem longitudinalSignHom_X_zero :
    longitudinalSignHom (K := K) (MvPolynomial.X (0 : Fin 4)) =
      -MvPolynomial.X (0 : Fin 4) := by
  simp [longitudinalSignHom]

@[simp]
theorem longitudinalSignHom_X_succ
    (j : Fin 3) :
    longitudinalSignHom (K := K) (MvPolynomial.X j.succ) =
      MvPolynomial.X j.succ := by
  simp [longitudinalSignHom]

/-- The longitudinal sign change is literally an involution. -/
theorem longitudinalSignHom_involutive
    (F : MvPolynomial (Fin 4) K) :
    longitudinalSignHom (K := K)
        (longitudinalSignHom (K := K) F) = F := by
  let φ : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
    (longitudinalSignHom (K := K)).comp
      (longitudinalSignHom (K := K))
  have hφ :
      φ = RingHom.id (MvPolynomial (Fin 4) K) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ, longitudinalSignHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [φ, longitudinalSignHom]
      · simp [φ, longitudinalSignHom]
  change φ F = F
  rw [hφ]
  rfl

/-- Linear sign substitution preserves every ordinary homogeneous degree. -/
theorem longitudinalSignHom_isHomogeneous
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    (hF : F.IsHomogeneous D) :
    (longitudinalSignHom (K := K) F).IsHomogeneous D := by
  have h :=
    hF.eval₂
      MvPolynomial.C
      (Fin.cases
        (-MvPolynomial.X (0 : Fin 4))
        (fun j : Fin 3 => MvPolynomial.X j.succ))
      (by
        intro r
        exact MvPolynomial.isHomogeneous_C (Fin 4) r)
      (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (MvPolynomial.isHomogeneous_X K (0 : Fin 4)).neg
        · exact MvPolynomial.isHomogeneous_X K j.succ)
  simpa [longitudinalSignHom] using h

/-- The pointed longitudinal reflection `x₀ ↦ 1 - x₀`. -/
noncomputable def pointedLongitudinalReflectionHom :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases
      (MvPolynomial.C 1 - MvPolynomial.X (0 : Fin 4))
      (fun j : Fin 3 => MvPolynomial.X j.succ))

@[simp]
theorem pointedLongitudinalReflectionHom_X_zero :
    pointedLongitudinalReflectionHom (K := K)
        (MvPolynomial.X (0 : Fin 4)) =
      MvPolynomial.C 1 - MvPolynomial.X (0 : Fin 4) := by
  simp [pointedLongitudinalReflectionHom]

@[simp]
theorem pointedLongitudinalReflectionHom_X_succ
    (j : Fin 3) :
    pointedLongitudinalReflectionHom (K := K)
        (MvPolynomial.X j.succ) =
      MvPolynomial.X j.succ := by
  simp [pointedLongitudinalReflectionHom]

/-- Pointed reflection is exactly right recentering followed by the
longitudinal sign involution:

`F(1-x₀,x⊥) = sign₀(F(x₀+1,x⊥))`. -/
theorem pointedLongitudinalReflectionHom_eq_sign_recenter
    (F : MvPolynomial (Fin 4) K) :
    pointedLongitudinalReflectionHom (K := K) F =
      longitudinalSignHom (K := K)
        (longitudinalRightRecenterHom (K := K) F) := by
  let φ : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
    pointedLongitudinalReflectionHom (K := K)
  let ψ : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K :=
    (longitudinalSignHom (K := K)).comp
      (longitudinalRightRecenterHom (K := K))
  have hφψ : φ = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ, ψ, pointedLongitudinalReflectionHom,
        longitudinalSignHom, longitudinalRightRecenterHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [φ, ψ, pointedLongitudinalReflectionHom,
          longitudinalSignHom, longitudinalRightRecenterHom]
        ring
      · simp [φ, ψ, pointedLongitudinalReflectionHom,
          longitudinalSignHom, longitudinalRightRecenterHom]
  change φ F = ψ F
  exact RingHom.congr_fun hφψ F

/-- Applying the sign involution to the pointed reflection recovers the
ordinary right-recentered polynomial. -/
theorem longitudinalSignHom_pointedReflection
    (F : MvPolynomial (Fin 4) K) :
    longitudinalSignHom (K := K)
        (pointedLongitudinalReflectionHom (K := K) F) =
      longitudinalRightRecenterHom (K := K) F := by
  rw [pointedLongitudinalReflectionHom_eq_sign_recenter]
  exact
    longitudinalSignHom_involutive
      (longitudinalRightRecenterHom (K := K) F)

/-! ## Mixedness transfer -/

/-- A support monomial of a homogeneous four-variable polynomial has exactly
the polynomial's ordinary degree. -/
theorem ordinaryDegree4_eq_of_isHomogeneous
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {d : Fin 4 →₀ ℕ}
    (hF : F.IsHomogeneous D)
    (hd : d ∈ F.support) :
    HC4.Polynomial.ordinaryDegree4 d = D := by
  have hw :
      Finsupp.weight (1 : Fin 4 → ℕ) d = D :=
    hF (MvPolynomial.mem_support_iff.mp hd)
  have hweightDegree :
      Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  exact
    (finsuppDegree_eq_ordinaryDegree4 d).symm.trans
      (hweightDegree.symm.trans hw)

/-- The recentered fibre carried by a mixed blocker cannot be homogeneous in
any ordinary degree. -/
theorem AdaptiveAlignedSmithMixedDegreeBlockerEndpoint.recentered_not_isHomogeneous
    {degreeCap : ℕ}
    (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
      (K := K) degreeCap)
    (D : ℕ) :
    ¬ (longitudinalRightRecenterHom
        (K := K) M.blocker.aligned.endpoint.rawSpecialFiber).IsHomogeneous D := by
  intro hhom
  have hD0 :
      HC4.Polynomial.ordinaryDegree4 M.d₀ = D :=
    ordinaryDegree4_eq_of_isHomogeneous hhom M.d₀_mem
  have hD1 :
      HC4.Polynomial.ordinaryDegree4 M.d₁ = D :=
    ordinaryDegree4_eq_of_isHomogeneous hhom M.d₁_mem
  exact M.degree_ne (hD0.trans hD1.symm)

/-- **Pointed reflection preserves the final blocker's mixed-degree
obstruction.**

The reflected raw special fibre cannot be homogeneous in any ordinary
degree.  This is the exact static fact needed before constructing the
family-level pointed reflection and ordinary-degree Rees exposure.
-/
theorem AdaptiveAlignedSmithMixedDegreeBlockerEndpoint.pointedReflection_not_isHomogeneous
    {degreeCap : ℕ}
    (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
      (K := K) degreeCap)
    (D : ℕ) :
    ¬ (pointedLongitudinalReflectionHom
        (K := K) M.blocker.aligned.endpoint.rawSpecialFiber).IsHomogeneous D := by
  intro hreflect
  have hsign :
      (longitudinalSignHom (K := K)
        (pointedLongitudinalReflectionHom
          (K := K) M.blocker.aligned.endpoint.rawSpecialFiber)).IsHomogeneous D :=
    longitudinalSignHom_isHomogeneous hreflect
  rw [longitudinalSignHom_pointedReflection] at hsign
  exact M.recentered_not_isHomogeneous D hsign

end

end HC4.Valuation
