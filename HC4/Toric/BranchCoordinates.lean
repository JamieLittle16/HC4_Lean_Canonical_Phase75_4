import HC4.Toric.SupportIntersection

/-!
# Coordinates on fixed toric branch levels

Once the branch level is fixed, an `r`-branch exponent is uniquely determined
by `(u₄,u₂)`, and an `s`-branch exponent is uniquely determined by `(u₁,u₃)`.
This module packages those projections, their reconstruction formulae, and
injectivity on sparse supports.  These are the support coordinates needed to
reindex a branch into a two-variable coefficient system.
-/

namespace HC4.Toric

/-- The free `(p,q)` coordinates on an `r` branch. -/
def rCoordinates (u : Exponent) : ℕ × ℕ :=
  (u.x4, u.x2)

/-- The free `(p,q)` coordinates on an `s` branch. -/
def sCoordinates (u : Exponent) : ℕ × ℕ :=
  (u.x1, u.x3)

@[simp] theorem rCoordinates_rBranch (a b i j k : ℕ) :
    rCoordinates (rBranch a b i j k) = (i, j) := rfl

@[simp] theorem sCoordinates_sBranch (a b i j k : ℕ) :
    sCoordinates (sBranch a b i j k) = (i, j) := rfl

/-- Reconstruct an exponent from its coordinates on a fixed `r` level. -/
theorem reconstruct_of_onRLevel
    {a b k : ℕ} {S : Set Exponent}
    (hR : OnRLevel a b k S) {u : Exponent} (hu : u ∈ S) :
    u = rBranch a b (rCoordinates u).1 (rCoordinates u).2 k := by
  rcases hR u hu with ⟨i, j, hU⟩
  subst u
  rfl

/-- Reconstruct an exponent from its coordinates on a fixed `s` level. -/
theorem reconstruct_of_onSLevel
    {a b k : ℕ} {S : Set Exponent}
    (hS : OnSLevel a b k S) {u : Exponent} (hu : u ∈ S) :
    u = sBranch a b (sCoordinates u).1 (sCoordinates u).2 k := by
  rcases hS u hu with ⟨i, j, hU⟩
  subst u
  rfl

/-- `rCoordinates` is injective on a fixed `r` level. -/
theorem rCoordinates_injective_on_level
    {a b k : ℕ} {S : Set Exponent}
    (hR : OnRLevel a b k S) :
    Set.InjOn rCoordinates S := by
  intro u hu v hv hcoord
  calc
    u = rBranch a b (rCoordinates u).1 (rCoordinates u).2 k :=
      reconstruct_of_onRLevel hR hu
    _ = rBranch a b (rCoordinates v).1 (rCoordinates v).2 k := by rw [hcoord]
    _ = v := (reconstruct_of_onRLevel hR hv).symm

/-- `sCoordinates` is injective on a fixed `s` level. -/
theorem sCoordinates_injective_on_level
    {a b k : ℕ} {S : Set Exponent}
    (hS : OnSLevel a b k S) :
    Set.InjOn sCoordinates S := by
  intro u hu v hv hcoord
  calc
    u = sBranch a b (sCoordinates u).1 (sCoordinates u).2 k :=
      reconstruct_of_onSLevel hS hu
    _ = sBranch a b (sCoordinates v).1 (sCoordinates v).2 k := by rw [hcoord]
    _ = v := (reconstruct_of_onSLevel hS hv).symm

/-- Project a sparse support to its free coordinates on an `r` branch. -/
def rProjectedSupport {K : Type*} [Zero K]
    (f : SparsePolynomial K) : Finset (ℕ × ℕ) :=
  f.support.image rCoordinates

/-- Project a sparse support to its free coordinates on an `s` branch. -/
def sProjectedSupport {K : Type*} [Zero K]
    (f : SparsePolynomial K) : Finset (ℕ × ℕ) :=
  f.support.image sCoordinates

@[simp] theorem mem_rProjectedSupport_iff
    {K : Type*} [Zero K] {f : SparsePolynomial K} {p : ℕ × ℕ} :
    p ∈ rProjectedSupport f ↔
      ∃ u ∈ f.support, rCoordinates u = p := by
  simp [rProjectedSupport]

@[simp] theorem mem_sProjectedSupport_iff
    {K : Type*} [Zero K] {f : SparsePolynomial K} {p : ℕ × ℕ} :
    p ∈ sProjectedSupport f ↔
      ∃ u ∈ f.support, sCoordinates u = p := by
  simp [sProjectedSupport]

/-- On a fixed sparse `r` level, every projected coordinate has one preimage. -/
theorem rProjectedSupport_unique_preimage
    {K : Type*} [Zero K] {a b k : ℕ} {f : SparsePolynomial K}
    (hR : SparseOnRLevel a b k f) {p : ℕ × ℕ}
    (hp : p ∈ rProjectedSupport f) :
    ∃! u : Exponent, u ∈ f.support ∧ rCoordinates u = p := by
  rcases mem_rProjectedSupport_iff.mp hp with ⟨u, hu, hup⟩
  refine ⟨u, ⟨hu, hup⟩, ?_⟩
  intro v hv
  exact (rCoordinates_injective_on_level
    (S := (↑f.support : Set Exponent)) (fun x hx => hR x hx))
      hv.1 hu (hv.2.trans hup.symm)

/-- On a fixed sparse `s` level, every projected coordinate has one preimage. -/
theorem sProjectedSupport_unique_preimage
    {K : Type*} [Zero K] {a b k : ℕ} {f : SparsePolynomial K}
    (hS : SparseOnSLevel a b k f) {p : ℕ × ℕ}
    (hp : p ∈ sProjectedSupport f) :
    ∃! u : Exponent, u ∈ f.support ∧ sCoordinates u = p := by
  rcases mem_sProjectedSupport_iff.mp hp with ⟨u, hu, hup⟩
  refine ⟨u, ⟨hu, hup⟩, ?_⟩
  intro v hv
  exact (sCoordinates_injective_on_level
    (S := (↑f.support : Set Exponent)) (fun x hx => hS x hx))
      hv.1 hu (hv.2.trans hup.symm)

end HC4.Toric
