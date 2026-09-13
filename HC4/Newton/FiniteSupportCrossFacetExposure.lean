import HC4.Newton.FirstContactHonestSlice
import Mathlib.Tactic

/-!
# A18.5.65c: finite-support cross-facet exposure

An arbitrary coordinate maximum of a first-contact carrier can collapse to a
single vertex or stay entirely on one side of the original facet.  The actual
Newton edge needed by RationalRigidity should instead be exposed so that it
contains both:

* an exponent on the original coordinate facet `d j = 0`; and
* an exponent genuinely outside it, `0 < d j`.

The construction is the same finite rational-slope argument already used by
`FirstContactSelection`, now applied a second time inside an arbitrary finite
carrier.  First choose a facet exponent `v` maximizing one auxiliary coordinate
`i`.  Among supported exponents with positive `j` coordinate, minimize

    (v_i - d_i) / d_j.

Clearing the denominator with the minimizing exponent produces an integral
weight whose exact maximal initial form contains both `v` and that outside
exponent.  Thus the resulting face is genuinely non-singleton and crosses the
facet by construction; no convex-polytope library is required.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Supported exponents lying on the coordinate facet `d j = 0`. -/
def zeroCoordinateSupport
    (j : Fin 4) (F : MvPolynomial (Fin 4) K) : Finset (Fin 4 →₀ ℕ) :=
  F.support.filter fun d => d j = 0

@[simp] theorem mem_zeroCoordinateSupport
    {j : Fin 4} {F : MvPolynomial (Fin 4) K} {d : Fin 4 →₀ ℕ} :
    d ∈ zeroCoordinateSupport j F ↔ d ∈ F.support ∧ d j = 0 := by
  simp [zeroCoordinateSupport]

/-- Supported exponents genuinely outside the coordinate facet `d j = 0`. -/
def positiveCoordinateSupport
    (j : Fin 4) (F : MvPolynomial (Fin 4) K) : Finset (Fin 4 →₀ ℕ) :=
  F.support.filter fun d => 0 < d j

@[simp] theorem mem_positiveCoordinateSupport
    {j : Fin 4} {F : MvPolynomial (Fin 4) K} {d : Fin 4 →₀ ℕ} :
    d ∈ positiveCoordinateSupport j F ↔ d ∈ F.support ∧ 0 < d j := by
  simp [positiveCoordinateSupport]

/-- A finite nonempty facet slice has an exponent maximizing any chosen
auxiliary coordinate. -/
theorem exists_zeroCoordinate_coordinateMax
    {j i : Fin 4} {F : MvPolynomial (Fin 4) K}
    (hne : (zeroCoordinateSupport j F).Nonempty) :
    ∃ v ∈ zeroCoordinateSupport j F,
      ∀ q ∈ zeroCoordinateSupport j F, q i ≤ v i := by
  exact Finset.exists_max_image (zeroCoordinateSupport j F) (fun d => d i) hne

/-- Rational slope of an outside exponent relative to a fixed facet exponent
and an auxiliary coordinate.  The numerator is integral because the outside
exponent may have larger auxiliary coordinate than the facet exponent. -/
def crossFacetSlope
    (i j : Fin 4) (v d : Fin 4 →₀ ℕ) : ℚ :=
  (((v i : ℤ) - (d i : ℤ) : ℤ) : ℚ) / (d j : ℚ)

/-- Comparing two positive-denominator secondary slopes is exactly the signed
integer cross-multiplication inequality. -/
theorem crossFacetSlope_le_iff_cross
    {i j : Fin 4} {v d₀ d : Fin 4 →₀ ℕ}
    (hd₀ : 0 < d₀ j) (hd : 0 < d j) :
    crossFacetSlope i j v d₀ ≤ crossFacetSlope i j v d ↔
      ((v i : ℤ) - (d₀ i : ℤ)) * (d j : ℤ) ≤
        ((v i : ℤ) - (d i : ℤ)) * (d₀ j : ℤ) := by
  have hd₀Q : (0 : ℚ) < (d₀ j : ℚ) := by exact_mod_cast hd₀
  have hdQ : (0 : ℚ) < (d j : ℚ) := by exact_mod_cast hd
  unfold crossFacetSlope
  rw [div_le_div_iff₀ hd₀Q hdQ]
  norm_cast

/-- Integral secondary exposing weight.  `scale` clears the selected outside
coordinate denominator and `bump` is allowed to be signed. -/
def crossFacetWeight
    (i j : Fin 4) (scale : ℕ) (bump : ℤ) : Fin 4 → ℤ :=
  fun k =>
    (scale : ℤ) * coordinateMaxWeight i k +
      bump * coordinateMaxWeight j k

/-- Explicit exponent formula for the secondary exposing weight. -/
theorem weight_crossFacetWeight
    (i j : Fin 4) (scale : ℕ) (bump : ℤ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (crossFacetWeight i j scale bump) d =
      (scale : ℤ) * (d i : ℤ) + bump * (d j : ℤ) := by
  rw [Finsupp.weight_apply]
  rw [Finsupp.sum_fintype]
  · fin_cases i <;> fin_cases j <;>
      simp [crossFacetWeight, coordinateMaxWeight, Fin.sum_univ_four] <;> ring
  · intro k
    simp

/-- Complete finite-support data for one exact face crossing the coordinate
facet. -/
structure CrossFacetInitialData
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) where
  facetExponent : Fin 4 →₀ ℕ
  outsideExponent : Fin 4 →₀ ℕ
  scale : ℕ
  bump : ℤ
  level : ℤ
  face : MvPolynomial (Fin 4) K
  facet_mem : facetExponent ∈ F.support
  facet_coordinate_zero : facetExponent j = 0
  outside_mem : outsideExponent ∈ F.support
  outside_coordinate_pos : 0 < outsideExponent j
  scale_pos : 0 < scale
  weight_bound : IsWeightLE (crossFacetWeight i j scale bump) level F
  face_eq : face = initialForm (crossFacetWeight i j scale bump) level F
  facet_mem_face : facetExponent ∈ face.support
  outside_mem_face : outsideExponent ∈ face.support

/-- **Finite-support cross-facet exposure.**

From one nonempty facet slice and one nonempty outside slice, construct an exact
integral initial form containing genuine support from both sides.  The facet
endpoint is first chosen maximal in the auxiliary coordinate, and the outside
endpoint is then chosen by the minimal rational secondary slope. -/
noncomputable def crossFacetInitialData
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (hfacet : (zeroCoordinateSupport j F).Nonempty)
    (hout : (positiveCoordinateSupport j F).Nonempty) :
    CrossFacetInitialData F i j := by
  classical
  have hvExists :
      ∃ v ∈ zeroCoordinateSupport j F,
        ∀ q ∈ zeroCoordinateSupport j F, q i ≤ v i :=
    exists_zeroCoordinate_coordinateMax (i := i) hfacet
  let v := Classical.choose hvExists
  have hvSpec :
      v ∈ zeroCoordinateSupport j F ∧
        ∀ q ∈ zeroCoordinateSupport j F, q i ≤ v i := by
    dsimp [v]
    exact Classical.choose_spec hvExists
  have hvZero : v ∈ zeroCoordinateSupport j F := hvSpec.1
  have hvMax : ∀ q ∈ zeroCoordinateSupport j F, q i ≤ v i := hvSpec.2
  have hvF : v ∈ F.support := (mem_zeroCoordinateSupport.mp hvZero).1
  have hvj : v j = 0 := (mem_zeroCoordinateSupport.mp hvZero).2

  have hminExists :
      ∃ d₀ ∈ positiveCoordinateSupport j F,
        ∀ d ∈ positiveCoordinateSupport j F,
          crossFacetSlope i j v d₀ ≤ crossFacetSlope i j v d :=
    Finset.exists_min_image
      (positiveCoordinateSupport j F)
      (fun d => crossFacetSlope i j v d) hout
  let d₀ := Classical.choose hminExists
  have hd₀Spec :
      d₀ ∈ positiveCoordinateSupport j F ∧
        ∀ d ∈ positiveCoordinateSupport j F,
          crossFacetSlope i j v d₀ ≤ crossFacetSlope i j v d := by
    dsimp [d₀]
    exact Classical.choose_spec hminExists
  have hd₀Pos : d₀ ∈ positiveCoordinateSupport j F := hd₀Spec.1
  have hmin : ∀ d ∈ positiveCoordinateSupport j F,
      crossFacetSlope i j v d₀ ≤ crossFacetSlope i j v d := hd₀Spec.2
  have hd₀F : d₀ ∈ F.support := (mem_positiveCoordinateSupport.mp hd₀Pos).1
  have hd₀j : 0 < d₀ j := (mem_positiveCoordinateSupport.mp hd₀Pos).2

  let scale : ℕ := d₀ j
  let bump : ℤ := (v i : ℤ) - (d₀ i : ℤ)
  let level : ℤ := (scale : ℤ) * (v i : ℤ)
  let w := crossFacetWeight i j scale bump
  let G := initialForm w level F

  have hscale : 0 < scale := by simpa [scale] using hd₀j

  have hbound : IsWeightLE w level F := by
    intro d hdF
    rw [show w = crossFacetWeight i j scale bump by rfl]
    rw [weight_crossFacetWeight]
    by_cases hdj0 : d j = 0
    · have hdZero : d ∈ zeroCoordinateSupport j F :=
        mem_zeroCoordinateSupport.mpr ⟨hdF, hdj0⟩
      have hdi : d i ≤ v i := hvMax d hdZero
      simp [level, bump, hdj0]
      exact_mod_cast Nat.mul_le_mul_left scale hdi
    · have hdj : 0 < d j := Nat.pos_of_ne_zero hdj0
      have hdPos : d ∈ positiveCoordinateSupport j F :=
        mem_positiveCoordinateSupport.mpr ⟨hdF, hdj⟩
      have hcross :
          ((v i : ℤ) - (d₀ i : ℤ)) * (d j : ℤ) ≤
            ((v i : ℤ) - (d i : ℤ)) * (d₀ j : ℤ) :=
        (crossFacetSlope_le_iff_cross hd₀j hdj).mp (hmin d hdPos)
      dsimp [level, bump, scale]
      nlinarith

  have hvWeight : Finsupp.weight w v = level := by
    rw [show w = crossFacetWeight i j scale bump by rfl]
    rw [weight_crossFacetWeight]
    simp [level, hvj]

  have hd₀Weight : Finsupp.weight w d₀ = level := by
    rw [show w = crossFacetWeight i j scale bump by rfl]
    rw [weight_crossFacetWeight]
    dsimp [level, bump, scale]
    ring

  have hvG : v ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [G]
    rw [coeff_initialForm]
    simp [hvWeight, MvPolynomial.mem_support_iff.mp hvF]

  have hd₀G : d₀ ∈ G.support := by
    apply MvPolynomial.mem_support_iff.mpr
    dsimp [G]
    rw [coeff_initialForm]
    simp [hd₀Weight, MvPolynomial.mem_support_iff.mp hd₀F]

  exact {
    facetExponent := v
    outsideExponent := d₀
    scale := scale
    bump := bump
    level := level
    face := G
    facet_mem := hvF
    facet_coordinate_zero := hvj
    outside_mem := hd₀F
    outside_coordinate_pos := hd₀j
    scale_pos := hscale
    weight_bound := hbound
    face_eq := rfl
    facet_mem_face := hvG
    outside_mem_face := hd₀G
  }

/-- The constructed face is genuinely non-singleton: its two certified support
exponents have different `j` coordinates. -/
theorem CrossFacetInitialData.facetExponent_ne_outsideExponent
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j) :
    D.facetExponent ≠ D.outsideExponent := by
  intro h
  have hj := congrArg (fun d : Fin 4 →₀ ℕ => d j) h
  change D.facetExponent j = D.outsideExponent j at hj
  rw [D.facet_coordinate_zero] at hj
  have : 0 < D.outsideExponent j := D.outside_coordinate_pos
  omega

/-- Support of the exact cross-facet face is inherited from the original
carrier. -/
theorem CrossFacetInitialData.support_subset
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j) :
    D.face.support ⊆ F.support := by
  rw [D.face_eq]
  exact support_initialForm_subset
    (crossFacetWeight i j D.scale D.bump) D.level F

/-- Toric balanced support passes unchanged to the cross-facet face. -/
theorem CrossFacetInitialData.balanced
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4} {a b : ℕ}
    (D : CrossFacetInitialData F i j)
    (hBal : HasBalancedMvSupport a b F) :
    HasBalancedMvSupport a b D.face := by
  rw [D.face_eq]
  exact hBal.initialForm
    (crossFacetWeight i j D.scale D.bump) D.level

/-- Hessian singularity passes unchanged to the exact cross-facet face. -/
theorem CrossFacetInitialData.hessian_zero
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j)
    (hzero : hessianDeterminant F = 0) :
    hessianDeterminant D.face = 0 := by
  rw [D.face_eq]
  exact hessianDeterminant_initialForm_eq_zero_of_eq_zero
    (crossFacetWeight i j D.scale D.bump) D.level F
    D.weight_bound hzero

end

end HC4.Newton
