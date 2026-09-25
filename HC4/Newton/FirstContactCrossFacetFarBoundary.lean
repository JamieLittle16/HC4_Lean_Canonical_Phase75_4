import HC4.Newton.FirstContactCrossFacetExtremeRayPositive
import HC4.Newton.InteriorVertex
import Mathlib.Tactic

/-!
# Far boundary endpoint of the genuine first-contact cross-facet line

The positive extreme-ray first-contact packet fixes the near endpoint of the
exact secondary face on a positive ray adjacent to `.qs`.  The same face is
already known to be one-dimensional: its contact coordinate is injective on
support.

This file exposes the opposite endpoint without introducing convex geometry.
Maximise the contact coordinate on the finite support of the exact cross-facet
face.  Injectivity makes the resulting coordinate-max initial form a literal
single monomial.  The outside support witness shows that its contact coordinate
is positive.  Since the entire carrier is nonlinear and Hessian-singular, the
existing exposed-monomial theorem puts this far endpoint on the toric boundary.

Thus both ends of the honest first-contact line are now genuine boundary
points.  The far point is immediately classified as either rank three on a
facet or lying on an extreme ray; this is the finite split consumed next by
the rank-three/complementary polynomial obstructions.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual far endpoint of an honest contact-zero cross-facet line,
together with its boundary-stratum classification. -/
structure CrossFacetFarBoundaryData
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)) where
  exponent : Fin 4 →₀ ℕ
  mem_face : exponent ∈ D.face.support
  contact_pos : 0 < exponent (0 : Fin 4)
  contact_max :
    ∀ d ∈ D.face.support, d (0 : Fin 4) ≤ exponent (0 : Fin 4)
  coeff_ne_zero : MvPolynomial.coeff exponent D.face ≠ 0
  boundary : MvExponentOnBoundary exponent
  stratum :
    (∃ F : ToricFacet, MvRankThreeOnFacet F exponent) ∨
      (∃ F H : ToricFacet,
        AdjacentFacets F H ∧
          OnRay a b F H (toToricExponent exponent))

/-- Rebase the already-recognised affine support line from the original
outside witness to the actual positive far endpoint.  Since both directions
are proportional to the same nonzero contact-coordinate direction, the far
endpoint itself may be used as the line direction for every support exponent. -/
theorem CrossFacetInitialData.support_far_affine_proportional
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D) :
    ∀ d ∈ D.face.support, ∀ k : Fin 4,
      (R.exponent (0 : Fin 4) : ℤ) *
          ((d k : ℤ) - (D.facetExponent k : ℤ)) =
        (d (0 : Fin 4) : ℤ) *
          ((R.exponent k : ℤ) - (D.facetExponent k : ℤ)) := by
  intro d hd k
  have hdLine :=
    D.support_crossFacet_affine_proportional
      ha hb hcontactScale hBal hcontact d hd k
  have hfarLine :=
    D.support_crossFacet_affine_proportional
      ha hb hcontactScale hBal hcontact R.exponent R.mem_face k
  have hout0 :
      (D.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.outside_coordinate_pos)
  have hscaled :
      (D.outsideExponent (0 : Fin 4) : ℤ) *
        ((R.exponent (0 : Fin 4) : ℤ) *
            ((d k : ℤ) - (D.facetExponent k : ℤ)) -
          (d (0 : Fin 4) : ℤ) *
            ((R.exponent k : ℤ) - (D.facetExponent k : ℤ))) = 0 := by
    linear_combination
      (R.exponent (0 : Fin 4) : ℤ) * hdLine -
        (d (0 : Fin 4) : ℤ) * hfarLine
  have hbracket :
      (R.exponent (0 : Fin 4) : ℤ) *
            ((d k : ℤ) - (D.facetExponent k : ℤ)) -
          (d (0 : Fin 4) : ℤ) *
            ((R.exponent k : ℤ) - (D.facetExponent k : ℤ)) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hout0
  exact sub_eq_zero.mp hbracket

/-- If the near and far endpoints of the honest cross-facet line both
vanish in one transverse coordinate, then the whole exact secondary face is
confined to that coordinate facet.  The proof uses the already-certified
affine proportionality and positivity of the contact coordinates. -/
theorem CrossFacetInitialData.face_support_coordinate_zero_of_far_zero
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (k : Fin 4)
    (hfacetZero : D.facetExponent k = 0)
    (hfarZero : R.exponent k = 0) :
    ∀ d ∈ D.face.support, d k = 0 := by
  have hfarLine :=
    D.support_crossFacet_affine_proportional
      ha hb hcontactScale hBal hcontact R.exponent R.mem_face k
  have hfar0Z : (R.exponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt R.contact_pos)
  have houtkProd :
      (R.exponent (0 : Fin 4) : ℤ) *
        (D.outsideExponent k : ℤ) = 0 := by
    simpa [D.facet_coordinate_zero, hfacetZero, hfarZero] using hfarLine.symm
  have houtkZ : (D.outsideExponent k : ℤ) = 0 :=
    (mul_eq_zero.mp houtkProd).resolve_left hfar0Z
  have houtk : D.outsideExponent k = 0 := by
    exact_mod_cast houtkZ

  intro d hd
  have hdLine :=
    D.support_crossFacet_affine_proportional
      ha hb hcontactScale hBal hcontact d hd k
  have hout0Z : (D.outsideExponent (0 : Fin 4) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.outside_coordinate_pos)
  have hprod :
      (D.outsideExponent (0 : Fin 4) : ℤ) * (d k : ℤ) = 0 := by
    simpa [D.facet_coordinate_zero, hfacetZero, houtk] using hdLine
  have hdkZ : (d k : ℤ) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hout0Z
  exact_mod_cast hdkZ

/-- The adjacent `q -> r` ray pairing lies entirely on the `.rq`
facet.  Only the two endpoint zero coordinates and honest affine-line
provenance are used. -/
theorem CrossFacetInitialData.face_on_rq_of_near_q_far_r
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear : D.facetExponent (3 : Fin 4) = 0)
    (hfar : R.exponent (3 : Fin 4) = 0) :
    MvSupportOnFacet .rq D.face := by
  intro d hd
  rw [onFacet_toToricExponent_iff]
  exact
    D.face_support_coordinate_zero_of_far_zero
      ha hb hcontactScale hBal hcontact R (3 : Fin 4) hnear hfar d hd

/-- Symmetrically, the adjacent `s -> p` pairing lies entirely on the
`.sp` facet. -/
theorem CrossFacetInitialData.face_on_sp_of_near_s_far_p
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear : D.facetExponent (2 : Fin 4) = 0)
    (hfar : R.exponent (2 : Fin 4) = 0) :
    MvSupportOnFacet .sp D.face := by
  intro d hd
  rw [onFacet_toToricExponent_iff]
  exact
    D.face_support_coordinate_zero_of_far_zero
      ha hb hcontactScale hBal hcontact R (2 : Fin 4) hnear hfar d hd

/-- A far endpoint has positive contact coordinate, so an extreme-ray
stratum there can only be the two rays with positive coordinate zero: the
`p` ray or the `r` ray.  The `q` and `s` rays are excluded literally
because their coordinate-zero exponent vanishes. -/
theorem CrossFacetFarBoundaryData.extremeRay_p_or_r
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    {D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)}
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hray :
      ∃ F H : ToricFacet,
        AdjacentFacets F H ∧
          OnRay a b F H (toToricExponent R.exponent)) :
    (∃ n : ℕ, 0 < n ∧
        toToricExponent R.exponent = Exponent.scale n pExponent) ∨
      (∃ n : ℕ, 0 < n ∧
        toToricExponent R.exponent = Exponent.scale n (rExponent a b)) := by
  rcases hray with ⟨F, H, hAdj, hRay⟩
  cases F <;> cases H <;>
    simp [AdjacentFacets, OppositeFacets, OnRay] at hAdj hRay
  all_goals
    rcases hRay with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnnot
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnnot
      have hx := congrArg (fun u : Exponent => u.x1) hn
      rw [hn0] at hx
      have hz : R.exponent (0 : Fin 4) = 0 := by
        simpa only [toToricExponent_x1, Exponent.scale_x1, zero_mul] using hx
      exact (Nat.ne_of_gt R.contact_pos hz).elim
    first
    | exact Or.inl ⟨n, hnpos, hn⟩
    | exact Or.inr ⟨n, hnpos, hn⟩
    | exfalso
      have hx := congrArg (fun u : Exponent => u.x1) hn
      have hz : R.exponent (0 : Fin 4) = 0 := by
        simpa only [toToricExponent_x1, Exponent.scale_x1,
          qExponent, sExponent, mul_zero] using hx
      exact (Nat.ne_of_gt R.contact_pos hz).elim

/-- Coordinate form of the preceding far-ray reduction.  These are the
two endpoint shapes used by the finite near/far pairing step. -/
theorem CrossFacetFarBoundaryData.extremeRay_coordinates_p_or_r
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    {D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)}
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hray :
      ∃ F H : ToricFacet,
        AdjacentFacets F H ∧
          OnRay a b F H (toToricExponent R.exponent)) :
    (∃ n : ℕ, 0 < n ∧
        R.exponent 0 = n ∧
        R.exponent 1 = 0 ∧
        R.exponent 2 = 0 ∧
        R.exponent 3 = n) ∨
      (∃ n : ℕ, 0 < n ∧
        R.exponent 0 = b * n ∧
        R.exponent 1 = 0 ∧
        R.exponent 2 = a * n ∧
        R.exponent 3 = 0) := by
  rcases R.extremeRay_p_or_r hray with hp | hr
  · rcases hp with ⟨n, hnpos, hn⟩
    left
    refine ⟨n, hnpos, ?_, ?_, ?_, ?_⟩
    · have h := congrArg (fun u : Exponent => u.x1) hn
      simpa [Exponent.scale, pExponent] using h
    · have h := congrArg (fun u : Exponent => u.x2) hn
      simpa [Exponent.scale, pExponent] using h
    · have h := congrArg (fun u : Exponent => u.x3) hn
      simpa [Exponent.scale, pExponent] using h
    · have h := congrArg (fun u : Exponent => u.x4) hn
      simpa [Exponent.scale, pExponent] using h
  · rcases hr with ⟨n, hnpos, hn⟩
    right
    refine ⟨n, hnpos, ?_, ?_, ?_, ?_⟩
    · have h := congrArg (fun u : Exponent => u.x1) hn
      simpa [Exponent.scale, rExponent, Nat.mul_comm] using h
    · have h := congrArg (fun u : Exponent => u.x2) hn
      simpa [Exponent.scale, rExponent] using h
    · have h := congrArg (fun u : Exponent => u.x3) hn
      simpa [Exponent.scale, rExponent, Nat.mul_comm] using h
    · have h := congrArg (fun u : Exponent => u.x4) hn
      simpa [Exponent.scale, rExponent] using h

/-- The four literal ray/ray pairings between the positive near endpoint
and a positive far endpoint.  This record is deliberately coordinate-level:
it is the finite interface consumed by the complementary/transition split. -/
inductive CrossFacetNearFarRayPairing
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    {D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)}
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D) : Prop
  | qToP
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = n)
      (near2 : D.facetExponent 2 = n)
      (near3 : D.facetExponent 3 = 0)
      (far0 : R.exponent 0 = m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = 0)
      (far3 : R.exponent 3 = m)
  | qToR
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = n)
      (near2 : D.facetExponent 2 = n)
      (near3 : D.facetExponent 3 = 0)
      (far0 : R.exponent 0 = b * m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = a * m)
      (far3 : R.exponent 3 = 0)
  | sToP
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = a * n)
      (near2 : D.facetExponent 2 = 0)
      (near3 : D.facetExponent 3 = b * n)
      (far0 : R.exponent 0 = m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = 0)
      (far3 : R.exponent 3 = m)
  | sToR
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = a * n)
      (near2 : D.facetExponent 2 = 0)
      (near3 : D.facetExponent 3 = b * n)
      (far0 : R.exponent 0 = b * m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = a * m)
      (far3 : R.exponent 3 = 0)

/-- Positive near-ray normal form and a far extreme-ray stratum give exactly
one of the four explicit pairings above. -/
theorem CrossFacetFarBoundaryData.nearFarRayPairing
    {a b : ℕ}
    {G : MvPolynomial (Fin 4) K}
    {D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)}
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n))
    (hray :
      ∃ F H : ToricFacet,
        AdjacentFacets F H ∧
          OnRay a b F H (toToricExponent R.exponent)) :
    CrossFacetNearFarRayPairing R := by
  rcases R.extremeRay_coordinates_p_or_r hray with hfarP | hfarR
  · rcases hfarP with ⟨m, hm, hf0, hf1, hf2, hf3⟩
    rcases hnear with hq | hs
    · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
      exact .qToP n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3
    · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
      exact .sToP n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3
  · rcases hfarR with ⟨m, hm, hf0, hf1, hf2, hf3⟩
    rcases hnear with hq | hs
    · rcases hq with ⟨n, hn, hn0, hn1, hn2, hn3⟩
      exact .qToR n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3
    · rcases hs with ⟨n, hn, hn0, hn1, hn2, hn3⟩
      exact .sToR n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3

/-- Primitive lattice parameterisation of the finite segment
`n*x + m*y = m*n`.

Writing `m = h*M` and `n = k*M` with coprime reduced factors, every
nonnegative lattice point on the segment has the unique shape
`x = h*j`, `y = k*(M-j)` for some `j ≤ M`.  This is exactly the
arithmetic normal form used by `complementaryLineExponentFinsupp`. -/
theorem exists_complementarySegment_parameter
    {m n x y : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hline : n * x + m * y = m * n) :
    ∃ M h k j : ℕ,
      0 < M ∧ 0 < h ∧ 0 < k ∧
      h.Coprime k ∧
      m = h * M ∧ n = k * M ∧
      j ≤ M ∧ x = h * j ∧ y = k * (M - j) := by
  rcases Nat.exists_coprime m n with
    ⟨h, k, hcop, hmRaw, hnRaw⟩
  let M := Nat.gcd m n
  have hmEq : m = h * M := by
    simpa [M] using hmRaw
  have hnEq : n = k * M := by
    simpa [M] using hnRaw
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.gcd_pos_of_pos_left n hm
  have hh : 0 < h := by
    by_contra hnot
    have hz : h = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hmEq, hz, zero_mul] at hm
    omega
  have hk : 0 < k := by
    by_contra hnot
    have hz : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hnEq, hz, zero_mul] at hn
    omega

  have hreduced : k * x + h * y = h * k * M := by
    have hscaled :
        M * (k * x + h * y) = M * (h * k * M) := by
      calc
        M * (k * x + h * y) =
            (k * M) * x + (h * M) * y := by ring
        _ = n * x + m * y := by rw [← hnEq, ← hmEq]
        _ = m * n := hline
        _ = (h * M) * (k * M) := by rw [hmEq, hnEq]
        _ = M * (h * k * M) := by ring
    exact Nat.mul_left_cancel hM hscaled

  have hdivSum : h ∣ k * x + h * y := by
    rw [hreduced]
    exact ⟨k * M, by ring⟩
  have hdivHY : h ∣ h * y := Nat.dvd_mul_right h y
  have hdivKX : h ∣ k * x :=
    (Nat.dvd_add_iff_left hdivHY).2 hdivSum
  have hdivX : h ∣ x :=
    hcop.dvd_of_dvd_mul_left hdivKX
  rcases hdivX with ⟨j, hx⟩

  have hfactor :
      h * (k * j + y) = h * (k * M) := by
    calc
      h * (k * j + y) = k * (h * j) + h * y := by ring
      _ = k * x + h * y := by rw [hx]
      _ = h * k * M := hreduced
      _ = h * (k * M) := by ring
  have hred : k * j + y = k * M :=
    Nat.mul_left_cancel hh hfactor
  have hkjle : k * j ≤ k * M := by
    exact ⟨y, hred⟩
  have hjle : j ≤ M :=
    Nat.le_of_mul_le_mul_left hkjle hk
  have hySub : y = k * M - k * j :=
    Nat.eq_sub_of_add_eq' hred
  have hy : y = k * (M - j) := by
    rw [hySub, Nat.mul_sub_left_distrib]

  exact ⟨M, h, k, j, hM, hh, hk, hcop,
    hmEq, hnEq, hjle, hx, hy⟩

/-- Every support exponent on an opposite `q -> p` chord has the
expected complementary coordinates and satisfies the primitive line equation
`n*x + m*y = m*n`. -/
theorem CrossFacetInitialData.qToP_support_equations
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (near0 : D.facetExponent 0 = 0)
    (near1 : D.facetExponent 1 = n)
    (near2 : D.facetExponent 2 = n)
    (near3 : D.facetExponent 3 = 0)
    (far0 : R.exponent 0 = m)
    (far1 : R.exponent 1 = 0)
    (far2 : R.exponent 2 = 0)
    (far3 : R.exponent 3 = m) :
    ∀ d ∈ D.face.support,
      d 0 = d 3 ∧
      d 1 = d 2 ∧
      n * d 0 + m * d 1 = m * n := by
  intro d hd
  have h1 := D.support_far_affine_proportional
    ha hb hcontactScale hBal hcontact R d hd (1 : Fin 4)
  have h2 := D.support_far_affine_proportional
    ha hb hcontactScale hBal hcontact R d hd (2 : Fin 4)
  have h3 := D.support_far_affine_proportional
    ha hb hcontactScale hBal hcontact R d hd (3 : Fin 4)
  rw [near0, near1, near2, near3, far0, far1, far2, far3] at h1 h2 h3
  have hmZ : (m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have h03Z : (d 0 : ℤ) = (d 3 : ℤ) := by
    have heq : (m : ℤ) * (d 3 : ℤ) = (m : ℤ) * (d 0 : ℤ) := by
      simpa [mul_comm] using h3
    exact (mul_left_cancel₀ hmZ heq).symm
  have h12Z : (d 1 : ℤ) = (d 2 : ℤ) := by
    have heq :
        (m : ℤ) * ((d 1 : ℤ) - (n : ℤ)) =
          (m : ℤ) * ((d 2 : ℤ) - (n : ℤ)) := by
      exact h1.trans h2.symm
    have hsub :
        (d 1 : ℤ) - (n : ℤ) =
          (d 2 : ℤ) - (n : ℤ) :=
      mul_left_cancel₀ hmZ heq
    linarith
  have hlineZ :
      (n : ℤ) * (d 0 : ℤ) + (m : ℤ) * (d 1 : ℤ) =
        (m : ℤ) * (n : ℤ) := by
    linear_combination h1
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast h03Z
  · exact_mod_cast h12Z
  · exact_mod_cast hlineZ

/-- On an opposite `s -> r` chord the two primitive ray blocks stay
proportional, and the first block satisfies the corresponding endpoint line
equation.  Coprimality of `a,b` will turn these relations into the canonical
complementary-line integer parameter in the next adapter. -/
theorem CrossFacetInitialData.sToR_support_equations
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (near0 : D.facetExponent 0 = 0)
    (near1 : D.facetExponent 1 = a * n)
    (near2 : D.facetExponent 2 = 0)
    (near3 : D.facetExponent 3 = b * n)
    (far0 : R.exponent 0 = b * m)
    (far1 : R.exponent 1 = 0)
    (far2 : R.exponent 2 = a * m)
    (far3 : R.exponent 3 = 0) :
    ∀ d ∈ D.face.support,
      b * d 2 = a * d 0 ∧
      b * d 1 = a * d 3 ∧
      b * m * d 1 + a * n * d 0 = a * b * m * n := by
  intro d hd
  have h1 := D.support_far_affine_proportional
    ha hb hcontactScale hBal hcontact R d hd (1 : Fin 4)
  have h2 := D.support_far_affine_proportional
    ha hb hcontactScale hBal hcontact R d hd (2 : Fin 4)
  rw [near0, near1, near2, near3, far0, far1, far2, far3] at h1 h2
  have hmZ : (m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hbZ : (b : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  have h20Z :
      (b : ℤ) * (d 2 : ℤ) = (a : ℤ) * (d 0 : ℤ) := by
    have heq :
        (m : ℤ) * ((b : ℤ) * (d 2 : ℤ)) =
          (m : ℤ) * ((a : ℤ) * (d 0 : ℤ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2
    exact mul_left_cancel₀ hmZ heq
  have hBalD : IsBalancedExponent a b d :=
    hBal d (D.support_subset hd)
  have h13Z :
      (b : ℤ) * (d 1 : ℤ) = (a : ℤ) * (d 3 : ℤ) := by
    unfold IsBalancedExponent at hBalD
    have hBalDZ :
        (a : ℤ) * (d 0 : ℤ) + (b : ℤ) * (d 1 : ℤ) =
          (b : ℤ) * (d 2 : ℤ) + (a : ℤ) * (d 3 : ℤ) := by
      exact_mod_cast hBalD
    linear_combination hBalDZ - h20Z
  have hlineZ :
      (b : ℤ) * (m : ℤ) * (d 1 : ℤ) +
          (a : ℤ) * (n : ℤ) * (d 0 : ℤ) =
        (a : ℤ) * (b : ℤ) * (m : ℤ) * (n : ℤ) := by
    linear_combination h1
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast h20Z
  · exact_mod_cast h13Z
  · exact_mod_cast hlineZ

/-- Final finite endpoint split for the honest first-contact line.  The two
adjacent ray pairings are immediately recognised as one-facet transitions;
only the two opposite chords remain as genuinely complementary cases.

Each constructor stores its literal endpoint coordinates, so downstream
consumers do not need to recover which constructor of
`CrossFacetNearFarRayPairing` was used. -/
inductive CrossFacetNearFarBoundaryOutcome
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D) : Prop
  | farRankThree
      (F : ToricFacet)
      (rankThree : MvRankThreeOnFacet F R.exponent)
  | adjacentRQ
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = n)
      (near2 : D.facetExponent 2 = n)
      (near3 : D.facetExponent 3 = 0)
      (far0 : R.exponent 0 = b * m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = a * m)
      (far3 : R.exponent 3 = 0)
      (support : MvSupportOnFacet .rq D.face)
  | adjacentSP
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = a * n)
      (near2 : D.facetExponent 2 = 0)
      (near3 : D.facetExponent 3 = b * n)
      (far0 : R.exponent 0 = m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = 0)
      (far3 : R.exponent 3 = m)
      (support : MvSupportOnFacet .sp D.face)
  | oppositeQP
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = n)
      (near2 : D.facetExponent 2 = n)
      (near3 : D.facetExponent 3 = 0)
      (far0 : R.exponent 0 = m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = 0)
      (far3 : R.exponent 3 = m)
  | oppositeSR
      (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
      (near0 : D.facetExponent 0 = 0)
      (near1 : D.facetExponent 1 = a * n)
      (near2 : D.facetExponent 2 = 0)
      (near3 : D.facetExponent 3 = b * n)
      (far0 : R.exponent 0 = b * m)
      (far1 : R.exponent 1 = 0)
      (far2 : R.exponent 2 = a * m)
      (far3 : R.exponent 3 = 0)

/-- The near/far geometry has no other cases. -/
theorem CrossFacetFarBoundaryData.nearFarBoundaryOutcome
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (R : CrossFacetFarBoundaryData (a := a) (b := b) D)
    (hnear :
      (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) :
    CrossFacetNearFarBoundaryOutcome D R := by
  rcases R.stratum with hthree | hray
  · rcases hthree with ⟨F, hF⟩
    exact .farRankThree F hF
  · have P := R.nearFarRayPairing hnear hray
    cases P with
    | qToP n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3 =>
        exact .oppositeQP n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3
    | qToR n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3 =>
        have hsupp : MvSupportOnFacet .rq D.face :=
          D.face_on_rq_of_near_q_far_r
            ha hb hcontactScale hBal hcontact R hn3 hf3
        exact .adjacentRQ n m hn hm hn0 hn1 hn2 hn3
          hf0 hf1 hf2 hf3 hsupp
    | sToP n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3 =>
        have hsupp : MvSupportOnFacet .sp D.face :=
          D.face_on_sp_of_near_s_far_p
            ha hb hcontactScale hBal hcontact R hn2 hf2
        exact .adjacentSP n m hn hm hn0 hn1 hn2 hn3
          hf0 hf1 hf2 hf3 hsupp
    | sToR n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3 =>
        exact .oppositeSR n m hn hm hn0 hn1 hn2 hn3 hf0 hf1 hf2 hf3

/-- **Far endpoint extraction for the exact first-contact line.**

The only nontrivial bookkeeping is singleton exposure.  A coordinate-zero
maximum of `D.face` has all support points at the same contact coordinate;
the already-proved contact-coordinate injectivity therefore makes that
coordinate-max face a single monomial. -/
noncomputable def CrossFacetInitialData.farBoundaryData
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {G : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b G)
    (hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant G = 0)
    (hnonlinear : ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) :
    CrossFacetFarBoundaryData (a := a) (b := b) D := by
  have hface_ne : D.face ≠ 0 := by
    intro hz
    have hmem := D.facet_mem_face
    rw [hz] at hmem
    simpa using hmem

  let E := coordinateMaxInitialData D.face hface_ne (0 : Fin 4)
  let far : Fin 4 →₀ ℕ := E.witness
  let c : K := MvPolynomial.coeff far E.face

  have hfarD : far ∈ D.face.support := by
    simpa [far, E] using E.witness_mem
  have hfarCoeffEq :
      MvPolynomial.coeff far E.face =
        MvPolynomial.coeff far D.face := by
    rw [E.face_eq, coeff_initialForm, weight_coordinateMaxWeight]
    have hcoord : far (0 : Fin 4) = E.level := by
      simpa [far, E] using E.witness_coordinate
    simp [hcoord]
  have hfarE : far ∈ E.face.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [hfarCoeffEq]
    exact MvPolynomial.mem_support_iff.mp hfarD

  have hfar_coord : far (0 : Fin 4) = E.level := by
    simpa [far, E] using E.witness_coordinate
  have hlevel_pos : 0 < E.level := by
    have hout_le :
        D.outsideExponent (0 : Fin 4) ≤ E.level :=
      E.maximal D.outsideExponent D.outside_mem_face
    exact lt_of_lt_of_le D.outside_coordinate_pos hout_le
  have hfar_pos : 0 < far (0 : Fin 4) := by
    rw [hfar_coord]
    exact hlevel_pos

  have hunique :
      ∀ q ∈ E.face.support, q = far := by
    intro q hq
    have hqD : q ∈ D.face.support :=
      E.support_subset hq
    have hq0 : q (0 : Fin 4) = far (0 : Fin 4) := by
      exact
        (E.coordinate_eq q hq).trans hfar_coord.symm
    exact D.support_eq_of_contactCoordinate_eq
      ha hb hcontactScale hBal hcontact hqD hfarD hq0

  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp hfarE

  have hmono : E.face = MvPolynomial.monomial far c := by
    apply MvPolynomial.ext
    intro q
    by_cases hq : q = far
    · subst q
      simp [c]
    · have hqzero : MvPolynomial.coeff q E.face = 0 := by
        by_contra hne
        have hqs : q ∈ E.face.support :=
          MvPolynomial.mem_support_iff.mpr hne
        exact hq (hunique q hqs)
      have hfarq : far ≠ q := by
        intro hfarq
        exact hq hfarq.symm
      rw [hqzero]
      simp [hfarq]

  have hinit :
      initialForm (coordinateMaxWeight (0 : Fin 4))
          (E.level : ℤ) D.face =
        MvPolynomial.monomial far c := by
    rw [← E.face_eq]
    exact hmono

  have hfarG : far ∈ G.support :=
    D.support_subset hfarD
  have hfar_deg : 3 ≤ ordinaryDegree4 far :=
    hnonlinear far hfarG
  have hface_zero : hessianDeterminant D.face = 0 :=
    D.hessian_zero hzero
  have hboundary : MvExponentOnBoundary far :=
    exposed_monomial_on_boundary_of_zero_hessian
      E.weight_bound hface_zero hinit hc hfar_deg

  have hBalFace : HasBalancedMvSupport a b D.face :=
    D.balanced hBal
  have hfarBal : IsBalancedExponent a b far :=
    hBalFace far hfarD
  have hstratum :=
    mvBoundary_rankThree_or_extremeRay
      ha hb hcop hfarBal hboundary

  refine {
    exponent := far
    mem_face := hfarD
    contact_pos := hfar_pos
    contact_max := ?_
    coeff_ne_zero := ?_
    boundary := hboundary
    stratum := hstratum
  }
  · intro d hd
    have hle : d (0 : Fin 4) ≤ E.level :=
      E.maximal d hd
    simpa [hfar_coord] using hle
  · exact MvPolynomial.mem_support_iff.mp hfarD

end

end HC4.Newton
