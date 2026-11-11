import ChallengeSpec

/-! Variation written for the independent review (not part of the submission).

The Wilson lattice of the public statement has one period for all four directions.
This file restates the lattice definitions with a separate period in each direction
(the setting of Note 4, reading 1: some directions kept compact), proves that the
isotropic case is the public one, and states the compactified target as a proposition.

Nothing here proves a compactified theorem. The file gives the statement a precise
form and checks that it extends the public one. -/
set_option autoImplicit false
noncomputable section
namespace ReviewAniso
open YangMills MeasureTheory TopologicalSpace Filter Set
open scoped Topology BigOperators Distributions Matrix.Norms.Frobenius

/-- Sites of a periodic lattice with its own period in each direction. -/
abbrev SiteA (l : Axis → ℕ+) := (i : Axis) → ZMod (l i).val
abbrev ConfigurationA (g : GaugeGroup) (l : Axis → ℕ+) := (SiteA l × Axis) → g.image

def plaquetteA {g : GaugeGroup} {l : Axis → ℕ+} (U : ConfigurationA g l) (x : SiteA l)
    (i j : Axis) : g.image :=
  U (x,i) * (U (x + Pi.single i 1,j) *
    ((U (x + Pi.single j 1,i))⁻¹ * (U (x,j))⁻¹))

def wilsonEnergyA {g : GaugeGroup} {l : Axis → ℕ+} (U : ConfigurationA g l) : ℝ :=
  ∑ p : SiteA l × Directions,
    (1 - ((plaquetteA U p.1 p.2.val.1 p.2.val.2).val.val.trace).re / ((g.n+1 : ℕ) : ℝ))

def wilsonLawA (g : GaugeGroup) (l : Axis → ℕ+) (β : ℝ) (haar : Measure g.image) :
    Measure (ConfigurationA g l) :=
  let prior : Measure (ConfigurationA g l) := Measure.pi fun _ => haar
  let density := fun U : ConfigurationA g l => Real.exp (-β * wilsonEnergyA U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)

/-- A Wilson family on tori whose periods may differ from direction to direction. -/
structure WilsonFamilyA (g : GaugeGroup) where
  period : ℕ → Axis → ℕ+
  denominator : ℕ → ℕ+
  denominatorStrict : StrictMono fun N => (denominator N).val
  beta : ℕ → ℕ → ℝ
  haar : Measure g.image
  probability : IsProbabilityMeasure haar
  invariantHaar : haar.IsHaarMeasure
  Token : Type
  insertion (N p : ℕ) : Token → SiteA (fun i => period p i * denominator N) →
    ConfigurationA g (fun i => period p i * denominator N) → ℂ

namespace WilsonFamilyA
variable {g : GaugeGroup} (C : WilsonFamilyA g)

abbrev side (N p : ℕ) : Axis → ℕ+ := fun i => C.period p i * C.denominator N

def mesh (N : ℕ) := ((C.denominator N).val : ℝ)⁻¹

def place (N p : ℕ) (y : SiteA (C.side N p)) : Spacetime :=
  WithLp.toLp 2 fun i => C.mesh N * (ZMod.valMinAbs (y i) : ℝ)

def finiteMoment (N p : ℕ) {n : ℕ} (labels : Fin n → C.Token)
    (x : Fin n → SiteA (C.side N p)) : ℂ :=
  ∫ U, ∏ i, C.insertion N p (labels i) (x i) U
    ∂wilsonLawA g (C.side N p) (C.beta N p) C.haar

/-- The test function fits inside the box, direction by direction. -/
def suitable (p : ℕ) {n : ℕ} (t : WilsonFamily.SeparatedTest n) : Prop :=
  tsupport t ⊆ {x : Points n | ∀ i a, -((C.period p a).val / (2:ℝ)) < x i a ∧
    x i a < (C.period p a).val / (2:ℝ)}

def smear (N p : ℕ) {n : ℕ} (v : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n) : ℂ :=
  (C.mesh N : ℂ) ^ (4*n) * ∑ x : Fin n → SiteA (C.side N p),
    t (WithLp.toLp 2 fun i => C.place N p (x i)) * C.finiteMoment N p v x

/-- Full mesh limit at each suitable fixed geometry, then the limit along the indicated
sequence of geometries. -/
def ConvergesA (volumeOrder : ℕ → ℕ)
    (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop :=
  ∀ n (v : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (volumeOrder k) t) ∧ ∃ row : ℕ → ℂ,
    (∀ p, C.suitable p t → Tendsto (fun N => C.smear N p v t) atTop (𝓝 (row p))) ∧
    Tendsto (fun k => row (volumeOrder k)) atTop (𝓝 (∫ x, t x * unselected v x))

end WilsonFamilyA

/-- The regularity conditions of the public statement, on anisotropic tori. -/
structure WilsonRegularityA {g : GaugeGroup} (C : WilsonFamilyA g) : Prop where
  running : ∃ slope : ℝ, 0 < slope ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ p, |C.beta N p / Real.log (C.mesh N)⁻¹ - slope| < ε
  continuous (N p v x) : Continuous (C.insertion N p v x)
  invariant (N p v x) (t : SiteA (C.side N p) → g.image) (U) :
    C.insertion N p v x (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) =
      C.insertion N p v x U
  localSupport (v : C.Token) : ∃ stencil : Finset (Axis → ℤ), ∀ N p (x : SiteA (C.side N p)),
    let sites := stencil.image fun z => (fun i => (z i : ZMod (C.side N p i).val)) + x
    ∀ U V, (∀ e, e.1 ∈ sites → e.1 + Pi.single e.2 1 ∈ sites → U e = V e) →
      C.insertion N p v x U = C.insertion N p v x V

/-! ## The isotropic case is the public one -/

/-- A family of the public statement, read as an anisotropic family with equal periods. -/
def ofIsotropic {g : GaugeGroup} (C : WilsonFamily g) : WilsonFamilyA g where
  period := fun p _ => C.period p
  denominator := C.denominator
  denominatorStrict := C.denominatorStrict
  beta := C.beta
  haar := C.haar
  probability := C.probability
  invariantHaar := C.invariantHaar
  Token := C.Token
  insertion := C.insertion

theorem converges_iff {g : GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ)
    (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) :
    (ofIsotropic C).ConvergesA order u ↔ C.Converges order u := Iff.rfl

theorem regular_of_isotropic {g : GaugeGroup} (C : WilsonFamily g) (h : WilsonRegularity C) :
    WilsonRegularityA (ofIsotropic C) :=
  ⟨h.running, h.continuous, h.invariant, h.localSupport⟩

/-! ## The compactified target -/

/-- The Wilson-origin clause on tori whose directions in `K` keep a fixed circumference
`Lc` while the others grow. This is the lattice part of the Kaluza–Klein reading of
Note 4. It is a statement, offered without proof for `K ≠ ∅`. Like the clause `wilson`
of the public statement it has content only together with further clauses on the limit
(reconstruction along a non-compact direction, non-triviality), which are left open. -/
def CompactifiedWilsonLimit (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) : Prop :=
  ∃ C : WilsonFamilyA g, WilsonRegularityA C ∧
    (∀ p i, i ∈ K → C.period p i = Lc) ∧
    (∀ i, i ∉ K → StrictMono fun p => (C.period p i).val) ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
      ∃ unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ,
        C.ConvergesA (p ∘ q) unselected

/-- With no compact direction the target follows from the public theorem. -/
theorem compactified_empty (h : JointExistence) (g : GaugeGroup) (hg : g.IsSimple) (Lc : ℕ+) :
    CompactifiedWilsonLimit g ∅ Lc := by
  obtain ⟨C, hreg, hC⟩ := h g hg
  refine ⟨ofIsotropic C, regular_of_isotropic C hreg, ?_, ?_, ?_⟩
  · intro p i hi
    exact absurd hi (Finset.notMem_empty i)
  · intro i _
    exact C.periodStrict
  · intro p hp
    obtain ⟨q, hq, T, hT⟩ := hC p hp
    exact ⟨q, hq, fun v => T.correlation none (T.project ∘ v), (converges_iff C _ _).mpr hT.wilson⟩

end ReviewAniso

/-! ===== Verifier additions (copy only; original file untouched) ===== -/
namespace ReviewVerify
open YangMills ReviewAniso MeasureTheory Filter Set TopologicalSpace
open scoped Topology

/-- U(k+1) is compact (Mathlib only: closed and inside the box of entries of norm ≤ 1). -/
theorem isCompact_unitary (k : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin (k + 1)) ℂ : Submonoid _) :
      Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) =>
      Set.pi Set.univ fun _ : Fin (k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hbox
    (isClosed_unitary : IsClosed (unitary (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
      Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))) ?_
  intro U hU i _ j _
  simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hU i j

instance imageCompact (g : GaugeGroup) : CompactSpace g.image := by
  haveI : CompactSpace (UnitaryRepresentation g.n) :=
    isCompact_iff_compactSpace.mp (isCompact_unitary g.n)
  exact isCompact_iff_compactSpace.mp g.imageClosed.isCompact

/-- A Haar probability measure on the image of an arbitrary gauge group. -/
def haarP (g : GaugeGroup) : Measure g.image := Measure.haarMeasure (⊤ : PositiveCompacts g.image)

instance (g : GaugeGroup) : IsProbabilityMeasure (haarP g) :=
  ⟨by unfold haarP; simpa using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts g.image))⟩

instance (g : GaugeGroup) : (haarP g).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

variable {g : GaugeGroup}

theorem re_trace_le (u : g.image) :
    |((u.val.val).trace).re| ≤ ((g.n + 1 : ℕ) : ℝ) := by
  have hu : u.val.val ∈ Matrix.unitaryGroup (Fin (g.n + 1)) ℂ := u.val.property
  calc |((u.val.val).trace).re| ≤ ‖(u.val.val).trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i, u.val.val i i‖ := rfl
    _ ≤ ∑ i, ‖u.val.val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (g.n + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hu i i
    _ = ((g.n + 1 : ℕ) : ℝ) := by simp

theorem cost_bounds (u : g.image) :
    0 ≤ 1 - ((u.val.val).trace).re / ((g.n + 1 : ℕ) : ℝ) ∧
    1 - ((u.val.val).trace).re / ((g.n + 1 : ℕ) : ℝ) ≤ 2 := by
  have h := re_trace_le u
  have hpos : (0 : ℝ) < ((g.n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_le] at h
  constructor
  · rw [sub_nonneg, div_le_one hpos]; exact h.2
  · have : -1 ≤ ((u.val.val).trace).re / ((g.n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hpos]; linarith [h.1]
    linarith

theorem energyA_bounds {l : Axis → ℕ+} (U : ConfigurationA g l) :
    0 ≤ wilsonEnergyA U ∧ wilsonEnergyA U ≤ 2 * (Fintype.card (SiteA l × Directions) : ℝ) := by
  unfold wilsonEnergyA
  constructor
  · exact Finset.sum_nonneg fun p _ => (cost_bounds _).1
  · calc _ ≤ ∑ _p : SiteA l × Directions, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (cost_bounds _).2
      _ = _ := by simp [mul_comm]

theorem energyA_continuous {l : Axis → ℕ+} : Continuous (wilsonEnergyA (g := g) (l := l)) := by
  unfold wilsonEnergyA plaquetteA
  fun_prop

theorem wilsonLawA_isProbability (l : Axis → ℕ+) (β : ℝ) (haar : Measure g.image)
    [IsProbabilityMeasure haar] : IsProbabilityMeasure (wilsonLawA g l β haar) := by
  let prior : Measure (ConfigurationA g l) := Measure.pi fun _ => haar
  let ρ := fun U : ConfigurationA g l => Real.exp (-β * wilsonEnergyA U)
  haveI : SecondCountableTopology (Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (g.n + 1) → Fin (g.n + 1) → ℂ))
  haveI : SecondCountableTopology (UnitaryRepresentation g.n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology g.image := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (ConfigurationA g l) := Pi.opensMeasurableSpace
  have hmeas : Measurable ρ :=
    (Real.continuous_exp.comp (continuous_const.mul energyA_continuous)).measurable
  let B' := |β| * (2 * (Fintype.card (SiteA l × Directions) : ℝ))
  have hbound : ∀ U, ‖ρ U‖ ≤ Real.exp B' := by
    intro U
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    obtain ⟨h0, h1⟩ := energyA_bounds U
    calc -β * wilsonEnergyA U ≤ |β| * wilsonEnergyA U := by
          have := neg_le_abs β; nlinarith
      _ ≤ B' := mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
  have hint : Integrable ρ prior :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Eventually.of_forall hbound)
  have hlow : ∀ U, Real.exp (-B') ≤ ρ U := by
    intro U
    apply Real.exp_le_exp.mpr
    obtain ⟨h0, h1⟩ := energyA_bounds U
    have : β * wilsonEnergyA U ≤ |β| * (2 * (Fintype.card (SiteA l × Directions) : ℝ)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self β) h0).trans
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg β))
    simp only [B']; linarith
  have hZpos : 0 < ∫ V, ρ V ∂prior := by
    have hmono := integral_mono (integrable_const (Real.exp (-B'))) hint hlow
    rw [integral_const, probReal_univ, one_smul] at hmono
    exact lt_of_lt_of_le (Real.exp_pos _) hmono
  constructor
  change (prior.withDensity fun U => ENNReal.ofReal (ρ U / ∫ V, ρ V ∂prior)) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
      (Eventually.of_forall fun U => div_nonneg (Real.exp_pos _).le hZpos.le),
    integral_div, div_self hZpos.ne', ENNReal.ofReal_one]

theorem points_zero_eq (x y : Points 0) : x = y := PiLp.ext fun i => i.elim0

theorem volume_points_zero : (volume : Measure (Points 0)).real univ = 1 := by
  let b := stdOrthonormalBasis ℝ (Points 0)
  have h1 := b.volume_parallelepiped
  have h2 : parallelepiped b = univ :=
    eq_univ_of_forall fun x => by
      rw [points_zero_eq x 0, mem_parallelepiped_iff]
      exact ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩
  rw [h2] at h1
  simp [Measure.real, h1]

/-- The degenerate witness: no tokens at all, `β = log(1/a)`, unit circumference growth
in the non-compact directions, fixed circumference `Lc` in the directions of `K`. -/
def trivialFamily (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) : WilsonFamilyA g where
  period p i := if i ∈ K then Lc else ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  denominatorStrict := fun a b h => by simpa using h
  beta N _ := Real.log ((N + 2 : ℕ) : ℝ)
  haar := haarP g
  probability := inferInstance
  invariantHaar := inferInstance
  Token := Empty
  insertion _ _ v := v.elim

theorem trivial_regular (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) :
    WilsonRegularityA (trivialFamily g K Lc) where
  running := by
    refine ⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩
    have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N + 2 by omega))
    simp only [trivialFamily, WilsonFamilyA.mesh, inv_inv, PNat.mk_coe]
    rw [div_self hpos.ne', sub_self, abs_zero]
    exact hε
  continuous _ _ v := v.elim
  invariant _ _ v := v.elim
  localSupport v := v.elim

theorem trivial_converges (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) (order : ℕ → ℕ) :
    (trivialFamily g K Lc).ConvergesA order (fun _ _ => 1) := by
  intro n v t
  cases n with
  | succ n => exact (v 0).elim
  | zero =>
    have hsmear : ∀ N p, (trivialFamily g K Lc).smear N p v t = t 0 := by
      intro N p
      haveI : IsProbabilityMeasure (trivialFamily g K Lc).haar := (trivialFamily g K Lc).probability
      haveI := wilsonLawA_isProbability ((trivialFamily g K Lc).side N p)
        ((trivialFamily g K Lc).beta N p) (trivialFamily g K Lc).haar
      simp only [WilsonFamilyA.smear, WilsonFamilyA.finiteMoment, Finset.univ_eq_empty,
        Finset.prod_empty, mul_zero, pow_zero, one_mul, integral_const, Fintype.sum_unique]
      rw [probReal_univ, one_smul, mul_one]
      congr 1
      exact points_zero_eq _ _
    refine ⟨Eventually.of_forall fun k => ?_, fun _ => t 0, fun p _ => ?_, ?_⟩
    · intro x _ i
      exact i.elim0
    · simp only [hsmear]; exact tendsto_const_nhds
    · haveI : Unique (Points 0) := ⟨⟨0⟩, fun x => points_zero_eq x 0⟩
      rw [integral_unique, volume_points_zero, one_smul, mul_one]
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => t 0) atTop (𝓝 (t 0))) using 2
      exact congrArg t (points_zero_eq _ _)

/-- **Vacuity.** `CompactifiedWilsonLimit` holds for every gauge group (simple or not), every
set of compact directions and every circumference. -/
theorem compactified_trivial (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) :
    CompactifiedWilsonLimit g K Lc := by
  refine ⟨trivialFamily g K Lc, trivial_regular g K Lc, ?_, ?_, ?_⟩
  · intro p i hi
    simp [trivialFamily, hi]
  · intro i hi a b hab
    simpa [trivialFamily, hi] using hab
  · intro p _
    exact ⟨id, strictMono_id, fun _ _ => 1, trivial_converges g K Lc _⟩

/-- **Obstruction.** With one compact direction, `ConvergesA` fails for every family that has
at least one token: a test function supported outside the fixed box is never `suitable`, and
`ConvergesA` requires eventual suitability of every test function as a conjunct. -/
theorem no_token_of_compact (C : WilsonFamilyA g) (i : Axis) (Lc : ℕ+)
    (hK : ∀ p, C.period p i = Lc) (v : C.Token) (order : ℕ → ℕ)
    (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : ¬ C.ConvergesA order u := by
  intro h
  let c : Points 1 := WithLp.toLp 2 fun _ => WithLp.toLp 2 fun _ => ((Lc : ℕ) : ℝ)
  let b : ContDiffBump c := ⟨1, 2, one_pos, one_lt_two⟩
  let t : WilsonFamily.SeparatedTest 1 :=
    ⟨fun y => ((b y : ℝ) : ℂ), (Complex.ofRealCLM.contDiff).comp b.contDiff,
      b.hasCompactSupport.comp_left Complex.ofReal_zero,
      fun y _ => show Function.Injective y.ofLp from Function.injective_of_subsingleton _⟩
  obtain ⟨hev, -⟩ := h 1 (fun _ => v) t
  obtain ⟨k, hk⟩ := hev.exists
  have hc : c ∈ tsupport t := by
    apply subset_tsupport
    have h1 : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    show ((b c : ℝ) : ℂ) ≠ 0
    rw [h1]; simp
  have := (hk hc 0 i).2
  rw [hK] at this
  have hL : (0 : ℝ) < ((Lc : ℕ) : ℝ) := by exact_mod_cast Lc.pos
  simp [c] at this
  linarith

/-- Consequence: for `K ≠ ∅` every witness of `CompactifiedWilsonLimit` has an empty token type. -/
theorem compactified_forces_empty (g : GaugeGroup) (K : Finset Axis) (hK : K.Nonempty) (Lc : ℕ+)
    (C : WilsonFamilyA g) (hper : ∀ p i, i ∈ K → C.period p i = Lc)
    (hconv : ∃ order : ℕ → ℕ, ∃ u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ,
      C.ConvergesA order u) : IsEmpty C.Token := by
  obtain ⟨i, hi⟩ := hK
  obtain ⟨order, u, h⟩ := hconv
  exact ⟨fun v => no_token_of_compact C i Lc (fun p => hper p i hi) v order u h⟩

end ReviewVerify

#print axioms ReviewVerify.compactified_trivial
#print axioms ReviewVerify.no_token_of_compact
#print axioms ReviewVerify.compactified_forces_empty
#print axioms ReviewAniso.regular_of_isotropic
#print axioms ReviewAniso.converges_iff
#print axioms ReviewAniso.compactified_empty
