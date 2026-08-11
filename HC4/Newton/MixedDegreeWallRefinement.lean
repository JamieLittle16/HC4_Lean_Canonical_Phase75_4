import HC4.Newton.MixedDegreeFirstWallCompetition
import HC4.Newton.RankOneRepairProgress
import HC4.Newton.TerminalTwoZeroSupport
import HC4.Polynomial.WeightedInitial
import HC4.Polynomial.MaximalHessianInitial
import HC4.Valuation.NonlinearDegreeBoundPreservation

/-!
# Ordinary-degree refinement inside a scalar Smith wall

This module constructs the literal two-stage object needed by the tied
mixed-degree branch: first restrict to one scalar Smith level, then retain
one ordinary source degree.  It proves only the finite-support facts that
are unconditional.  Preservation of collision and Hessian geometry is
intentionally left as the next bridge.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

theorem ordinaryIntegerWeight_eq_ordinaryDegree4
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d =
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum_fintype, HC4.Polynomial.ordinaryDegree4,
    Fin.sum_univ_four]

/-- Ordinary-degree component of an arbitrary concrete Smith subface. -/
noncomputable def smithSubfaceDegreeComponent
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm (fun _ : Fin 4 => (1 : ℤ)) D
    (smithSubfacePolynomial (1 : Fin 4) 2 3 T F)

theorem coeff_smithSubfaceDegreeComponent
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (smithSubfaceDegreeComponent T F D) =
      if smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D
      then MvPolynomial.coeff d F else 0 := by
  classical
  unfold smithSubfaceDegreeComponent
  rw [HC4.Polynomial.coeff_initialForm,
    coeff_smithSubfacePolynomial,
    ordinaryIntegerWeight_eq_ordinaryDegree4]
  norm_cast
  by_cases hT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T <;>
    by_cases hD : HC4.Polynomial.ordinaryDegree4 d = D <;>
    simp [hT, hD]

theorem smithSubfaceDegreeComponent_isHomogeneous
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ) :
    (smithSubfaceDegreeComponent T F D).IsHomogeneous D := by
  intro d hd
  rw [coeff_smithSubfaceDegreeComponent] at hd
  split at hd
  · have hw : Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
      (congrFun Finsupp.degree_eq_weight_one d).symm
    exact hw.trans ((HC4.Valuation.finsuppDegree_eq_ordinaryDegree4 d).trans
      ‹smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
        HC4.Polynomial.ordinaryDegree4 d = D›.2)
  · exact (hd rfl).elim

theorem smithProjectedSupport_smithSubfaceDegreeComponent_subset
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ) :
    smithProjectedSupport (1 : Fin 4) 2 3
        (smithSubfaceDegreeComponent T F D) ⊆ T := by
  intro e he
  rcases smithProjectedSupport_realised (1 : Fin 4) 2 3
      (smithSubfaceDegreeComponent T F D) e he with
    ⟨d, hd, hde⟩
  rw [coeff_smithSubfaceDegreeComponent] at hd
  split at hd
  · simpa [hde] using
      (show smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
        HC4.Polynomial.ordinaryDegree4 d = D from ‹_›).1
  · exact (hd rfl).elim

theorem smithSubfaceDegreeComponent_ne_zero_of_mem
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T) :
    smithSubfaceDegreeComponent T F
        (HC4.Polynomial.ordinaryDegree4 d) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff d P) hzero
  change MvPolynomial.coeff d
      (smithSubfaceDegreeComponent T F
        (HC4.Polynomial.ordinaryDegree4 d)) = 0 at hcoeff
  rw [coeff_smithSubfaceDegreeComponent] at hcoeff
  simp [hT] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- A nonzero Smith subface has a maximal ordinary degree whose component
is nonzero and bounds the full subface support. -/
theorem exists_maximalDegree_nonzero_smithSubfaceComponent
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty) :
    ∃ D : ℕ,
      smithSubfaceDegreeComponent T F D ≠ 0 ∧
      ∀ d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D := by
  rcases Finset.exists_max_image
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support
      HC4.Polynomial.ordinaryDegree4 hW with ⟨d, hd, hmax⟩
  let D := HC4.Polynomial.ordinaryDegree4 d
  have hdF : d ∈ F.support := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_smithSubfacePolynomial] at hcoeff
    split at hcoeff
    · exact MvPolynomial.mem_support_iff.mpr hcoeff
    · exact (hcoeff rfl).elim
  have hdT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_smithSubfacePolynomial] at hcoeff
    split at hcoeff
    · exact ‹smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T›
    · exact (hcoeff rfl).elim
  exact ⟨D, smithSubfaceDegreeComponent_ne_zero_of_mem T F d hdF hdT,
    fun q hq => hmax q hq⟩

/-- A nonzero Smith subface also has a *minimal* ordinary degree whose
component is nonzero and which bounds the full subface support from below.

This is the extremum used by the adaptive packet exposure: refining the
quadratic Smith face by minimal degree gives a nonnegative integral source
weight, whereas selecting maximal degree would require a negative
longitudinal source weight. -/
theorem exists_minimalDegree_nonzero_smithSubfaceComponent
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty) :
    ∃ D : ℕ,
      smithSubfaceDegreeComponent T F D ≠ 0 ∧
      ∀ d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support,
        D ≤ HC4.Polynomial.ordinaryDegree4 d := by
  rcases Finset.exists_min_image
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support
      HC4.Polynomial.ordinaryDegree4 hW with ⟨d, hd, hmin⟩
  let D := HC4.Polynomial.ordinaryDegree4 d
  have hdF : d ∈ F.support := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_smithSubfacePolynomial] at hcoeff
    split at hcoeff
    · exact MvPolynomial.mem_support_iff.mpr hcoeff
    · exact (hcoeff rfl).elim
  have hdT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [coeff_smithSubfacePolynomial] at hcoeff
    split at hcoeff
    · exact ‹smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T›
    · exact (hcoeff rfl).elim
  exact ⟨D, smithSubfaceDegreeComponent_ne_zero_of_mem T F d hdF hdT,
    fun q hq => hmin q hq⟩

/-- On a quadratic Smith subface, ordinary homogeneity determines the
forgotten longitudinal exponent exactly: every monomial in degree `D` has
`x₀`-exponent `D-2`. -/
theorem quadraticSmithSubfaceDegreeComponent_longitudinalExponent
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    {d : Fin 4 →₀ ℕ}
    (hd : MvPolynomial.coeff d
        (smithSubfaceDegreeComponent T F D) ≠ 0) :
    d 0 = D - 2 := by
  rw [coeff_smithSubfaceDegreeComponent] at hd
  split at hd
  · rcases (show
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D from ‹_›) with
      ⟨hdT, hdegree⟩
    have hp := hquad _ hdT
    simp only [smithSupportExponentOf] at hp
    simp [HC4.Polynomial.ordinaryDegree4] at hdegree
    rcases hp with hp | hp | hp <;> omega
  · exact (hd rfl).elim

/-- Provenance of a homogeneous packet as the first longitudinal graded
piece of an actual mixed quadratic Smith subface.  This record intentionally
does not assert that the complete subface equals the packet. -/
structure IsMinimalLongitudinalSmithPacket
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (Q : MvPolynomial (Fin 4) K) : Prop where
  packet_eq : Q = smithSubfaceDegreeComponent T F D
  packet_ne_zero : Q ≠ 0
  packet_homogeneous : Q.IsHomogeneous D
  minimalDegree :
    ∀ d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support,
      D ≤ HC4.Polynomial.ordinaryDegree4 d
  longitudinalExponent :
    ∀ d, MvPolynomial.coeff d Q ≠ 0 → d 0 = D - 2

/-- Weight retaining only the distinguished longitudinal exponent. -/
def longitudinalIntegerWeight (i : Fin 4) : ℤ :=
  if i = 0 then 1 else 0

theorem longitudinalIntegerWeight_eq
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight longitudinalIntegerWeight d = (d 0 : ℤ) := by
  rw [Finsupp.weight_apply]
  simp [longitudinalIntegerWeight, Finsupp.sum_fintype,
    Fin.sum_univ_four]

/-- On a quadratic Smith subface, the minimal ordinary-degree component is
exactly the lowest `x₀`-adic initial form of the complete mixed subface. -/
theorem IsMinimalLongitudinalSmithPacket.eq_longitudinalInitialForm
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hD : 2 ≤ D)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    Q = HC4.Polynomial.initialForm longitudinalIntegerWeight (D - 2)
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) := by
  classical
  rw [hpacket.packet_eq]
  apply MvPolynomial.ext
  intro d
  rw [coeff_smithSubfaceDegreeComponent,
    HC4.Polynomial.coeff_initialForm,
    longitudinalIntegerWeight_eq,
    coeff_smithSubfacePolynomial]
  by_cases hT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T
  · have hp := hquad _ hT
    simp only [smithSupportExponentOf] at hp
    have hdegree :
        HC4.Polynomial.ordinaryDegree4 d = d 0 + 2 := by
      simp [HC4.Polynomial.ordinaryDegree4]
      rcases hp with hp | hp | hp <;> omega
    have hcast :
        ((d 0 : ℤ) = (D : ℤ) - 2) ↔ d 0 = D - 2 := by
      omega
    by_cases hdeg : HC4.Polynomial.ordinaryDegree4 d = D
    · have hx : d 0 = D - 2 := by omega
      have hzx : ((D - 2 : ℕ) : ℤ) = (D : ℤ) - 2 := by omega
      simp [hT, hdeg, hx, hzx]
    · have hx : d 0 ≠ D - 2 := by
        intro hx
        apply hdeg
        omega
      simp [hT, hdeg, hcast, hx]
  · simp [hT]

/-- Entrywise Hessian provenance of the minimal packet.  After the
coordinate-dependent derivative shift, its Hessian is exactly the lowest
longitudinal initial form of the complete mixed quadratic subface Hessian. -/
theorem IsMinimalLongitudinalSmithPacket.hessian_eq_longitudinalInitialForm
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hD : 2 ≤ D)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (i j : Fin 4) :
    HC4.Polynomial.hessian Q i j =
      HC4.Polynomial.initialForm longitudinalIntegerWeight
        ((D : ℤ) - 2 - longitudinalIntegerWeight i -
          longitudinalIntegerWeight j)
        (HC4.Polynomial.hessian
          (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j) := by
  rw [hpacket.eq_longitudinalInitialForm hD hquad]
  exact HC4.Polynomial.hessian_initialForm_entry
    longitudinalIntegerWeight (D - 2)
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j

/-- Minimal ordinary degree on a quadratic Smith subface is equivalently a
lower bound on every longitudinal exponent of the complete subface. -/
theorem IsMinimalLongitudinalSmithPacket.longitudinalSupportLowerBound
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support) :
    D - 2 ≤ d 0 := by
  have hmin := hpacket.minimalDegree d hd
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_smithSubfacePolynomial] at hcoeff
  split at hcoeff
  · have hp := hquad _ ‹smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T›
    simp only [smithSupportExponentOf] at hp
    have hdegree : HC4.Polynomial.ordinaryDegree4 d = d 0 + 2 := by
      simp [HC4.Polynomial.ordinaryDegree4]
      rcases hp with hp | hp | hp <;> omega
    omega
  · exact (hcoeff rfl).elim

/-- After two derivatives, the longitudinal lower bound shifts by precisely
the weights of the differentiated coordinates. -/
theorem IsMinimalLongitudinalSmithPacket.hessian_longitudinalWeight_lowerBound
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (i j : Fin 4)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈
      (HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j).support) :
    (D : ℤ) - 2 - longitudinalIntegerWeight i -
        longitudinalIntegerWeight j ≤ (d 0 : ℤ) := by
  let W := smithSubfacePolynomial (1 : Fin 4) 2 3 T F
  have hne := MvPolynomial.mem_support_iff.mp hd
  change MvPolynomial.coeff d
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i W)) ≠ 0 at hne
  rw [coeff_pderiv_backport, coeff_pderiv_backport] at hne
  have hcoeff :
      MvPolynomial.coeff
        ((d + Finsupp.single j 1) + Finsupp.single i 1) W ≠ 0 := by
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  have hsupport :
      ((d + Finsupp.single j 1) + Finsupp.single i 1) ∈ W.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hlower := hpacket.longitudinalSupportLowerBound hquad hsupport
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalIntegerWeight, Finsupp.single_apply] at hlower ⊢ <;>
    omega

/-- Every nonzero quadratic Smith subface has a canonical minimal
longitudinal packet. -/
theorem exists_minimalLongitudinalSmithPacket
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      IsMinimalLongitudinalSmithPacket T F D Q := by
  rcases exists_minimalDegree_nonzero_smithSubfaceComponent T F hW with
    ⟨D, hne, hmin⟩
  refine ⟨D, smithSubfaceDegreeComponent T F D, ?_⟩
  refine
    { packet_eq := rfl
      packet_ne_zero := hne
      packet_homogeneous := smithSubfaceDegreeComponent_isHomogeneous T F D
      minimalDegree := hmin
      longitudinalExponent := ?_ }
  intro d hd
  exact quadraticSmithSubfaceDegreeComponent_longitudinalExponent
    T F D hquad hd

theorem hessianDeterminant_smithSubfaceDegreeComponent_eq_zero_of_maximal
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hmax :
      ∀ d ∈ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hzero :
      HC4.Polynomial.hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) = 0) :
    HC4.Polynomial.hessianDeterminant
        (smithSubfaceDegreeComponent T F D) = 0 := by
  let W := smithSubfacePolynomial (1 : Fin 4) 2 3 T F
  have hweight : HC4.Polynomial.IsWeightLE
      (fun _ : Fin 4 => (1 : ℤ)) D W := by
    intro d hd
    rw [ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast hmax d hd
  exact HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
    (fun _ : Fin 4 => (1 : ℤ)) D W hweight hzero

/-- A quadratic Smith subface contains no pure-longitudinal or
transverse-linear projected exponent.  Consequently every first derivative
of each ordinary-degree component vanishes on the entire distinguished
axis. -/
theorem quadraticSmithSubfaceDegreeComponent_gradient_axis_zero
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∀ x : K, ∀ i : Fin 4,
      mvGradientComponentAt
        (Fin.cons x (fun _ : Fin 3 => (0 : K)))
        (smithSubfaceDegreeComponent T F D) i = 0 := by
  let G := smithSubfaceDegreeComponent T F D
  have hsubset := smithProjectedSupport_smithSubfaceDegreeComponent_subset
    T F D
  have hnot (e : SmithSupportExponent)
      (hbad :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e ∨
        IsWLinearSmithPattern e) :
      e ∉ smithProjectedSupport (1 : Fin 4) 2 3 G := by
    intro he
    have heT := hsubset he
    rcases hquad e heT with hyy | hyz | hzz <;>
      rcases hbad with hpure | hfirst | hsecond | hw <;>
      simp [IsPureLongitudinalSmithPattern,
        IsLowNegativeFirstSmithPattern,
        IsLowNegativeSecondSmithPattern,
        IsWLinearSmithPattern] at * <;> omega
  have hpure : longitudinalCoefficientPolynomial 0 0 0 G = 0 := by
    by_contra hne
    exact hnot ⟨0, 0, 0⟩ (Or.inl ⟨rfl, rfl, rfl⟩)
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G ⟨0, 0, 0⟩).mp hne)
  have hpureAt : longitudinalCoefficientPolynomialAt 0 G = 0 := by
    simpa [longitudinalCoefficientPolynomial,
      smithTransverseExponent] using hpure
  have hfirst : longitudinalCoefficientPolynomial 0 1 0 G = 0 := by
    by_contra hne
    exact hnot ⟨0, 1, 0⟩ (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G ⟨0, 1, 0⟩).mp hne)
  have hsecond : longitudinalCoefficientPolynomial 1 0 0 G = 0 := by
    by_contra hne
    exact hnot ⟨1, 0, 0⟩
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G ⟨1, 0, 0⟩).mp hne)
  have hw : longitudinalCoefficientPolynomial 0 0 1 G = 0 := by
    by_contra hne
    exact hnot ⟨0, 0, 1⟩
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
      ((longitudinalCoefficientPolynomial_ne_zero_iff_mem_projectedSupport
        G ⟨0, 0, 1⟩).mp hne)
  intro x i
  change mvGradientComponentAt
    (Fin.cons x (fun _ : Fin 3 => (0 : K))) G i = 0
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold mvGradientComponentAt
    rw [eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
    rw [longitudinalAxisRestriction_eq_coefficient_zero, hpureAt]
    simp
  · unfold mvGradientComponentAt
    rw [eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single]
    fin_cases j
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hsecond
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hfirst
    · simpa [longitudinalCoefficientPolynomial,
        smithTransverseExponent] using congrArg (Polynomial.eval x) hw

theorem quadraticSmithSubfaceDegreeComponent_exactAxisCollision
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    HasExactGradientCollision
      (smithSubfaceDegreeComponent T F D)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  intro i
  have hzeroPoint : (fun _ : Fin 4 => (0 : K)) =
      Fin.cons 0 (fun _ : Fin 3 => (0 : K)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  have haxisPoint : coordinateAxisPoint (K := K) (0 : Fin 4) =
      Fin.cons 1 (fun _ : Fin 3 => (0 : K)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp [coordinateAxisPoint]
  rw [hzeroPoint, haxisPoint]
  rw [quadraticSmithSubfaceDegreeComponent_gradient_axis_zero
      T F D hquad 0 i,
    quadraticSmithSubfaceDegreeComponent_gradient_axis_zero
      T F D hquad 1 i]

/-- Every quadratic target exponent has zero `w` exponent, so each degree
component is independent of source coordinate `3`; its four-dimensional
Hessian determinant therefore vanishes structurally. -/
theorem quadraticSmithSubfaceDegreeComponent_hessianDeterminant_eq_zero
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    HC4.Polynomial.hessianDeterminant
      (smithSubfaceDegreeComponent T F D) = 0 := by
  let Q := smithSubfaceDegreeComponent T F D
  have hsupp :
      ∀ m : Fin 4 →₀ ℕ, MvPolynomial.coeff m Q ≠ 0 → m 3 = 0 := by
    intro m hm
    have hmSupport : m ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm
    have heQ := smithSupportExponentOf_mem_projectedSupport Q m hmSupport
    have heT := smithProjectedSupport_smithSubfaceDegreeComponent_subset
      T F D heQ
    have hpattern := hquad _ heT
    simp [smithSupportExponentOf] at hpattern
    rcases hpattern with hyy | hyz | hzz <;> omega
  have hderiv : MvPolynomial.pderiv (3 : Fin 4)
      (smithSubfaceDegreeComponent T F D) = 0 :=
    pderiv_eq_zero_of_all_supported_exponents_zero 3 Q hsupp
  unfold HC4.Polynomial.hessianDeterminant
  apply Matrix.det_eq_zero_of_row_eq_zero (3 : Fin 4)
  intro j
  simp [HC4.Polynomial.hessian_apply, hderiv]

theorem quadraticSmithSubfaceDegreeComponent_degree_two_le_of_ne_zero
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hne : smithSubfaceDegreeComponent T F D ≠ 0) :
    2 ≤ D := by
  let Q := smithSubfaceDegreeComponent T F D
  have hsupport : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    apply MvPolynomial.ext
    intro d
    have hdnot : d ∉ Q.support := by simp [hempty]
    exact MvPolynomial.notMem_support_iff.mp hdnot
  rcases hsupport with ⟨d, hd⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  change MvPolynomial.coeff d
      (smithSubfaceDegreeComponent T F D) ≠ 0 at hcoeff
  rw [coeff_smithSubfaceDegreeComponent] at hcoeff
  split at hcoeff
  · have hdata :
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D := ‹_›
    have hpattern := hquad _ hdata.1
    simp [smithSupportExponentOf] at hpattern
    simp [HC4.Polynomial.ordinaryDegree4] at hdata
    rcases hpattern with hyy | hyz | hzz <;> omega
  · exact (hcoeff rfl).elim

/-- Legitimate homogeneous replacement for a mixed-degree quadratic Smith
subface.  The only geometric input not supplied by finite support is that
the complete quadratic subface polynomial has zero Hessian determinant. -/
theorem symmetricQuadraticSubface_exists_homogeneousCollisionFibre
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      Q = smithSubfaceDegreeComponent T F D ∧
      Q ≠ 0 ∧
      2 ≤ D ∧
      Q.IsHomogeneous D ∧
      HasExactGradientCollision Q
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
      HC4.Polynomial.hessianDeterminant Q = 0 := by
  rcases exists_minimalDegree_nonzero_smithSubfaceComponent T F hW with
    ⟨D, hne, _hmin⟩
  refine ⟨D, smithSubfaceDegreeComponent T F D, rfl, hne, ?_,
    smithSubfaceDegreeComponent_isHomogeneous T F D,
    quadraticSmithSubfaceDegreeComponent_exactAxisCollision T F D hquad,
    quadraticSmithSubfaceDegreeComponent_hessianDeterminant_eq_zero
      T F D hquad⟩
  exact quadraticSmithSubfaceDegreeComponent_degree_two_le_of_ne_zero
    T F D hquad hne

/-- Direct handoff from the output shape of the symmetric Smith refinement:
a nonempty quadratic subface of the actual projected support contains a
nonzero homogeneous degree-`D ≥ 2` exact collision fibre with zero
four-dimensional Hessian determinant. -/
theorem nonemptyQuadraticProjectedSubface_exists_homogeneousCollisionFibre
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hne : T.Nonempty)
    (hsub : T ⊆ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      Q = smithSubfaceDegreeComponent T F D ∧
      Q ≠ 0 ∧
      2 ≤ D ∧
      Q.IsHomogeneous D ∧
      HasExactGradientCollision Q
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
      HC4.Polynomial.hessianDeterminant Q = 0 := by
  have hreal : IsSmithSubfaceRealisedInPolynomial
      (1 : Fin 4) 2 3 T F :=
    smithSubfaceRealised_of_subset_projectedSupport 1 2 3 T F hsub
  have hWne : smithSubfacePolynomial (1 : Fin 4) 2 3 T F ≠ 0 :=
    smithSubfacePolynomial_ne_zero_of_nonempty_realised
      1 2 3 T F hne hreal
  have hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hWne
    apply MvPolynomial.ext
    intro d
    have hdnot : d ∉ (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support := by
      simp [hempty]
    exact MvPolynomial.notMem_support_iff.mp hdnot
  exact symmetricQuadraticSubface_exists_homogeneousCollisionFibre
    T F hW hquad

/-- Provenance-preserving version of the quadratic subface extraction.  The
output packet is not merely homogeneous: it is certified as the minimal
longitudinal graded packet of the stated subface of the stated ambient
polynomial. -/
theorem nonemptyQuadraticProjectedSubface_exists_minimalLongitudinalPacket
    (T : Finset SmithSupportExponent)
    (F : MvPolynomial (Fin 4) K)
    (hne : T.Nonempty)
    (hsub : T ⊆ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      IsMinimalLongitudinalSmithPacket T F D Q ∧
      2 ≤ D ∧
      HasExactGradientCollision Q
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
      HC4.Polynomial.hessianDeterminant Q = 0 ∧
      HasRankOnePersistentPacketSupport (0 : Fin 4) 1 2 D Q := by
  have hreal : IsSmithSubfaceRealisedInPolynomial
      (1 : Fin 4) 2 3 T F :=
    smithSubfaceRealised_of_subset_projectedSupport 1 2 3 T F hsub
  have hWne : smithSubfacePolynomial (1 : Fin 4) 2 3 T F ≠ 0 :=
    smithSubfacePolynomial_ne_zero_of_nonempty_realised
      1 2 3 T F hne hreal
  have hW : (smithSubfacePolynomial (1 : Fin 4) 2 3 T F).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hWne
    exact MvPolynomial.support_eq_empty.mp hempty
  rcases exists_minimalDegree_nonzero_smithSubfaceComponent T F hW with
    ⟨D, hQne, hmin⟩
  let Q := smithSubfaceDegreeComponent T F D
  have hprov : IsMinimalLongitudinalSmithPacket T F D Q :=
    { packet_eq := rfl
      packet_ne_zero := hQne
      packet_homogeneous := smithSubfaceDegreeComponent_isHomogeneous T F D
      minimalDegree := hmin
      longitudinalExponent := by
        intro d hd
        exact quadraticSmithSubfaceDegreeComponent_longitudinalExponent
          T F D hquad hd }
  have hD : 2 ≤ D :=
    quadraticSmithSubfaceDegreeComponent_degree_two_le_of_ne_zero
      T F D hquad hQne
  have hsupported : IsSupportedOnSmithSubface (1 : Fin 4) 2 3 T Q := by
    intro d hd
    rw [coeff_smithSubfaceDegreeComponent] at hd
    split at hd
    · exact (show
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
          HC4.Polynomial.ordinaryDegree4 d = D from ‹_›).1
    · exact (hd rfl).elim
  have hpersistent : HasRankOnePersistentPacketSupport
      (0 : Fin 4) 1 2 D Q :=
    rankOnePersistentPacketSupport_of_smithQuadraticSubface
      (0 : Fin 4) 1 2 3
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by intro t; fin_cases t <;> simp)
      hprov.packet_homogeneous T hsupported hquad
  exact ⟨D, Q, hprov, hD,
    quadraticSmithSubfaceDegreeComponent_exactAxisCollision T F D hquad,
    quadraticSmithSubfaceDegreeComponent_hessianDeterminant_eq_zero T F D hquad,
    hpersistent⟩

/-- Complete mixed-degree first-wall handoff under the existing symmetric
pole-minimality hypotheses: either an old blocker survives with its
residual data, or the wall contains a legitimate nonzero homogeneous
collision fibre ready for the fixed-degree machinery. -/
theorem minimalSmithLevel_blockerOutcome_or_homogeneousCollisionFibre
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport (1 : Fin 4) 2 3 F) level base)
    (hmin :
      ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
        Q ≠ 0 ∧
        2 ≤ D ∧
        Q.IsHomogeneous D ∧
        HasExactGradientCollision Q
          (fun _ : Fin 4 => (0 : K))
          (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
        HC4.Polynomial.hessianDeterminant Q = 0 ∧
        HasRankOnePersistentPacketSupport
          (0 : Fin 4) 1 2 D Q := by
  rcases minimalSmithLevel_blockerOutcome_or_symmetricQuadraticRefinement
      F base level hcoll hzero hvalue hpole hmin hattain with
    hblocker | ⟨hTnonempty, hquad⟩
  · exact Or.inl hblocker
  · let T := smithSymmetricBalancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 F) level base
    have hsub : T ⊆ smithProjectedSupport (1 : Fin 4) 2 3 F := by
      intro e he
      exact (mem_smithSymmetricBalancedSubface.mp he).1
    rcases nonemptyQuadraticProjectedSubface_exists_homogeneousCollisionFibre
        T F hTnonempty hsub hquad with
      ⟨D, Q, hQeq, hQ, hD, hhom, hQcoll, hQhess⟩
    have hQsupported :
        IsSupportedOnSmithSubface (1 : Fin 4) 2 3 T Q := by
      intro d hd
      rw [hQeq, coeff_smithSubfaceDegreeComponent] at hd
      split at hd
      · exact (show
          smithSupportExponentOf (1 : Fin 4) 2 3 d ∈ T ∧
            HC4.Polynomial.ordinaryDegree4 d = D from ‹_›).1
      · exact (hd rfl).elim
    have hpacket :
        HasRankOnePersistentPacketSupport
          (0 : Fin 4) 1 2 D Q :=
      rankOnePersistentPacketSupport_of_smithQuadraticSubface
        (0 : Fin 4) 1 2 3
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by intro t; fin_cases t <;> simp)
        hhom T hQsupported hquad
    exact Or.inr ⟨D, Q, hQ, hD, hhom, hQcoll, hQhess, hpacket⟩

/-- The homogeneous branch of the adaptive wall theorem enters the
already-green fixed-degree rank-one classifier without reconstructing a
parameter family or assuming that the original mixed-degree family was
homogeneous. -/
theorem minimalSmithLevel_blockerOutcome_or_fixedDegreeRepair
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (hzero :
      ∀ i : Fin 4,
        MvPolynomial.eval
          (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
          (MvPolynomial.pderiv i F) = 0)
    (hvalue :
      MvPolynomial.eval
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) F = 0)
    (hpole :
      IsSymmetricSmithPoleMinimal
        (smithProjectedSupport (1 : Fin 4) 2 3 F) level base)
    (hmin :
      ∀ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        level ≤ base e)
    (hattain :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level)
    (complexity : ℕ) :
    (∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F,
        base e = level ∧
        (IsPureLongitudinalSmithPattern e ∨
         IsLowNegativeFirstSmithPattern e ∨
         IsLowNegativeSecondSmithPattern e ∨
         IsWLinearSmithPattern e) ∧
        MixedDegreeSmithExponentOutcome F e) ∨
      ∃ D : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
        Q ≠ 0 ∧
        2 ≤ D ∧
        Q.IsHomogeneous D ∧
        HasExactGradientCollision Q
          (fun _ : Fin 4 => (0 : K))
          (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
        HC4.Polynomial.hessianDeterminant Q = 0 ∧
        HasSmithCanonicalRepairOutcome
          (0 : Fin 4) 1 2 D Q complexity := by
  rcases minimalSmithLevel_blockerOutcome_or_homogeneousCollisionFibre
      F base level hcoll hzero hvalue hpole hmin hattain with
    hblocker | ⟨D, Q, hQ, hD, hhom, hQcoll, hQhess, hpacket⟩
  · exact Or.inl hblocker
  · refine Or.inr ⟨D, Q, hQ, hD, hhom, hQcoll, hQhess, ?_⟩
    rcases rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        (by decide) (by decide) (by decide)
        hpacket hQ with hrigid | hrepair
    · exact Or.inl hrigid
    · exact Or.inr
        ⟨hrepair.1, hrepair.2,
          repairState_measure_lt_of_progress hrepair.2⟩

/-- The projected Smith exponents lying on one scalar wall. -/
noncomputable def smithScalarLevel
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ) : Finset SmithSupportExponent :=
  (smithProjectedSupport (1 : Fin 4) 2 3 F).filter
    (fun e => base e = level)

/-- Literal restriction of `F` to one scalar Smith wall. -/
noncomputable def smithScalarLevelPolynomial
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ) : MvPolynomial (Fin 4) K :=
  smithSubfacePolynomial (1 : Fin 4) 2 3
    (smithScalarLevel F base level) F

/-- Ordinary-degree `D` inside a fixed scalar Smith wall. -/
noncomputable def smithScalarLevelDegreeComponent
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (D : ℕ) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm (fun _ : Fin 4 => (1 : ℤ)) D
    (smithScalarLevelPolynomial F base level)

/-- Exact coefficient formula for the two-stage refinement. -/
theorem coeff_smithScalarLevelDegreeComponent
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (D : ℕ)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (smithScalarLevelDegreeComponent F base level D) =
      if base (smithSupportExponentOf (1 : Fin 4) 2 3 d) = level ∧
          HC4.Polynomial.ordinaryDegree4 d = D
      then MvPolynomial.coeff d F
      else 0 := by
  classical
  unfold smithScalarLevelDegreeComponent
  rw [HC4.Polynomial.coeff_initialForm]
  unfold smithScalarLevelPolynomial
  rw [coeff_smithSubfacePolynomial]
  simp only [smithScalarLevel, Finset.mem_filter]
  have hweight :
      Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d =
        (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
    exact ordinaryIntegerWeight_eq_ordinaryDegree4 d
  rw [hweight]
  norm_cast
  by_cases hcoeff : MvPolynomial.coeff d F = 0
  · simp [hcoeff]
  · have hd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hproj := smithSupportExponentOf_mem_projectedSupport F d hd
    by_cases hlevel :
        base (smithSupportExponentOf (1 : Fin 4) 2 3 d) = level
    · by_cases hdegree : HC4.Polynomial.ordinaryDegree4 d = D
      · simp [hproj, hlevel, hdegree]
      · simp [hlevel, hdegree]
    · simp [hproj, hlevel]

/-- Every degree component selected inside a scalar Smith wall is genuinely
ordinary homogeneous. -/
theorem smithScalarLevelDegreeComponent_isHomogeneous
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (D : ℕ) :
    (smithScalarLevelDegreeComponent F base level D).IsHomogeneous D := by
  intro d hd
  rw [coeff_smithScalarLevelDegreeComponent] at hd
  split at hd
  · have hw : Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
      (congrFun Finsupp.degree_eq_weight_one d).symm
    exact hw.trans ((HC4.Valuation.finsuppDegree_eq_ordinaryDegree4 d).trans
      ‹base (smithSupportExponentOf (1 : Fin 4) 2 3 d) = level ∧
        HC4.Polynomial.ordinaryDegree4 d = D›.2)
  · exact (hd rfl).elim

/-- An actual source monomial on the chosen Smith level survives in its
own ordinary-degree component. -/
theorem smithScalarLevelDegreeComponent_ne_zero_of_mem
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hlevel : base (smithSupportExponentOf (1 : Fin 4) 2 3 d) = level) :
    smithScalarLevelDegreeComponent F base level
        (HC4.Polynomial.ordinaryDegree4 d) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff d P) hzero
  change MvPolynomial.coeff d
      (smithScalarLevelDegreeComponent F base level
        (HC4.Polynomial.ordinaryDegree4 d)) = 0 at hcoeff
  rw [coeff_smithScalarLevelDegreeComponent] at hcoeff
  simp [hlevel] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- A tied mixed-degree wall contains two distinct nonzero homogeneous
degree components. -/
theorem tiedMixedDegreeWall_has_two_nonzeroHomogeneousComponents
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (d₀ d₁ : Fin 4 →₀ ℕ)
    (hd₀ : d₀ ∈ F.support)
    (hd₁ : d₁ ∈ F.support)
    (hlevel₀ : base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) = level)
    (hlevel₁ : base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) = level)
    (hdegree : HC4.Polynomial.ordinaryDegree4 d₀ ≠
      HC4.Polynomial.ordinaryDegree4 d₁) :
    let D₀ := HC4.Polynomial.ordinaryDegree4 d₀
    let D₁ := HC4.Polynomial.ordinaryDegree4 d₁
    D₀ ≠ D₁ ∧
      smithScalarLevelDegreeComponent F base level D₀ ≠ 0 ∧
      smithScalarLevelDegreeComponent F base level D₁ ≠ 0 ∧
      (smithScalarLevelDegreeComponent F base level D₀).IsHomogeneous D₀ ∧
      (smithScalarLevelDegreeComponent F base level D₁).IsHomogeneous D₁ := by
  dsimp
  exact ⟨hdegree,
    smithScalarLevelDegreeComponent_ne_zero_of_mem
      F base level d₀ hd₀ hlevel₀,
    smithScalarLevelDegreeComponent_ne_zero_of_mem
      F base level d₁ hd₁ hlevel₁,
    smithScalarLevelDegreeComponent_isHomogeneous F base level _,
    smithScalarLevelDegreeComponent_isHomogeneous F base level _⟩

/-- The Hessian determinant of a maximal ordinary-degree component is the
maximal determinant component of the whole scalar-wall polynomial.  In
particular, a zero Hessian determinant descends to that extremal homogeneous
component without any componentwise-collision assumption. -/
theorem hessianDeterminant_smithScalarLevelDegreeComponent_eq_zero_of_maximal
    (F : MvPolynomial (Fin 4) K)
    (base : SmithSupportExponent → ℤ)
    (level : ℤ)
    (D : ℕ)
    (hmax :
      ∀ d ∈ (smithScalarLevelPolynomial F base level).support,
        HC4.Polynomial.ordinaryDegree4 d ≤ D)
    (hzero :
      HC4.Polynomial.hessianDeterminant
        (smithScalarLevelPolynomial F base level) = 0) :
    HC4.Polynomial.hessianDeterminant
        (smithScalarLevelDegreeComponent F base level D) = 0 := by
  let W := smithScalarLevelPolynomial F base level
  have hweight : HC4.Polynomial.IsWeightLE
      (fun _ : Fin 4 => (1 : ℤ)) D W := by
    intro d hd
    rw [ordinaryIntegerWeight_eq_ordinaryDegree4]
    exact_mod_cast hmax d hd
  exact HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
    (fun _ : Fin 4 => (1 : ℤ)) D W hweight hzero

end

end HC4.Newton
