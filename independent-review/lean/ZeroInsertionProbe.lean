import Challenge

/-! Review probe E (not part of the submission). Imports only the reference
statement (Mathlib-only closure).

Claim: if every lattice insertion of a Wilson family is identically zero, then
no hierarchy over that family satisfies `Hierarchy.Properties`.  So the public
statement cannot be met with gauge-field-blind (zero) lattice observables even
though `WilsonRegularity` alone allows them (Probe B in SpecProbes.lean). -/

set_option autoImplicit false
noncomputable section
namespace ReviewProbeE
open YangMills MeasureTheory Filter Set
open scoped Topology ENNReal

variable {g : GaugeGroup}

/-- Entries bound gives |Re tr u| ≤ n+1 for every matrix of the group. -/
theorem re_trace_le (u : g.image) :
    |((u.val.val).trace).re| ≤ ((g.n + 1 : ℕ) : ℝ) := by
  have hu : u.val.val ∈ Matrix.unitaryGroup (Fin (g.n + 1)) ℂ := u.val.property
  calc |((u.val.val).trace).re| ≤ ‖(u.val.val).trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i, u.val.val i i‖ := rfl
    _ ≤ ∑ i, ‖u.val.val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (g.n + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hu i i
    _ = ((g.n + 1 : ℕ) : ℝ) := by simp

theorem plaquetteCost_bounds {l : ℕ+} (U : Configuration g l) (x : Site l) (i j : Axis) :
    0 ≤ 1 - ((plaquette U x i j).val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) ∧
    1 - ((plaquette U x i j).val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) ≤ 2 := by
  have h := re_trace_le (plaquette U x i j)
  have hpos : (0 : ℝ) < ((g.n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_le] at h
  constructor
  · rw [sub_nonneg, div_le_one hpos]; exact h.2
  · have : -1 ≤ ((plaquette U x i j).val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hpos]; linarith [h.1]
    linarith

theorem wilsonEnergy_bounds {l : ℕ+} (U : Configuration g l) :
    0 ≤ wilsonEnergy U ∧ wilsonEnergy U ≤ 2 * (Fintype.card (Site l × Directions) : ℝ) := by
  unfold wilsonEnergy
  constructor
  · exact Finset.sum_nonneg fun p _ => (plaquetteCost_bounds U p.1 p.2.val.1 p.2.val.2).1
  · calc _ ≤ ∑ _p : Site l × Directions, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (plaquetteCost_bounds U p.1 p.2.val.1 p.2.val.2).2
      _ = _ := by simp [mul_comm]

theorem wilsonEnergy_continuous {l : ℕ+} : Continuous (wilsonEnergy (g := g) (l := l)) := by
  unfold wilsonEnergy plaquette
  fun_prop

theorem wilsonLaw_isProbability (l : ℕ+) (β : ℝ) (haar : Measure g.image)
    [IsProbabilityMeasure haar] : IsProbabilityMeasure (wilsonLaw g l β haar) := by
  let prior : Measure (Configuration g l) := Measure.pi fun _ => haar
  let ρ := fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)
  haveI : SecondCountableTopology (Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (g.n + 1) → Fin (g.n + 1) → ℂ))
  haveI : SecondCountableTopology (UnitaryRepresentation g.n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology g.image := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace g.image := inferInstance
  haveI : OpensMeasurableSpace (Configuration g l) := Pi.opensMeasurableSpace
  have hmeas : Measurable ρ :=
    (Real.continuous_exp.comp (continuous_const.mul wilsonEnergy_continuous)).measurable
  let B' := |β| * (2 * (Fintype.card (Site l × Directions) : ℝ))
  let B := Real.exp B'
  have hbound : ∀ U, ‖ρ U‖ ≤ B := by
    intro U
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    obtain ⟨h0, h1⟩ := wilsonEnergy_bounds U
    calc -β * wilsonEnergy U ≤ |β| * wilsonEnergy U := by
          have := neg_le_abs β; nlinarith
      _ ≤ B' :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
  have hint : Integrable ρ prior :=
    Integrable.of_bound hmeas.aestronglyMeasurable B (Eventually.of_forall hbound)
  have hlow : ∀ U, Real.exp (-B') ≤ ρ U := by
    intro U
    apply Real.exp_le_exp.mpr
    obtain ⟨h0, h1⟩ := wilsonEnergy_bounds U
    have : β * wilsonEnergy U ≤ |β| * (2 * (Fintype.card (Site l × Directions) : ℝ)) :=
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

/-- Probe D, repeated here so that this file is self-contained. -/
theorem empty_cluster {C : WilsonFamily g} (T : Hierarchy C)
    (h : T.OperatorProductExpansion) (s : Option T.Character) (o : Spacetime) :
    T.grouped s (Empty.elim : Empty → T.Tag) Empty.elim (Empty.elim : Empty → T.Tag) Empty.elim =
      ∑ j : Fin (0 + 1), ∑ i : T.Channel j.val,
        T.coefficient (Empty.elim : Empty → T.Tag) j.val i Empty.elim o *
          T.grouped s (fun _ : Unit => (⟨j.val, T.actor j.val i⟩ : T.Tag)) (fun _ => o)
            (Empty.elim : Empty → T.Tag) Empty.elim := by
  have hrem := h.remainder (Empty.elim : Empty → T.Tag) (Empty.elim : Empty → T.Tag)
    0 1 1 (1/2) le_rfl one_pos one_pos (by norm_num) 0
  have hw : T.weight (Empty.elim : Empty → T.Tag) = 0 := by
    simp [Hierarchy.weight]
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖T.grouped s (Empty.elim : Empty → T.Tag) Empty.elim (Empty.elim : Empty → T.Tag) Empty.elim -
        ∑ j : Fin (0 + 1), ∑ i : T.Channel j.val,
          T.coefficient (Empty.elim : Empty → T.Tag) j.val i Empty.elim o *
            T.grouped s (fun _ : Unit => (⟨j.val, T.actor j.val i⟩ : T.Tag)) (fun _ => o)
              (Empty.elim : Empty → T.Tag) Empty.elim‖ ≤ r ^ ((1 : ℝ) / 2) := by
    filter_upwards [hrem] with r hr
    have hx : Hierarchy.Within r 0 1 (Empty.elim : Empty → Spacetime) o :=
      ⟨fun i => i.elim, fun i => i.elim⟩
    have hy : Hierarchy.Clear o (Empty.elim : Empty → Spacetime) 1 :=
      ⟨fun i => i.elim, fun i => i.elim⟩
    have := hr Empty.elim o Empty.elim hx hy s
    rw [hw] at this
    convert this using 2
    norm_num
  have hlim : Filter.Tendsto (fun r : ℝ => r ^ ((1 : ℝ) / 2)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hle := ge_of_tendsto hlim hev
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

theorem separated_one_univ (x : Points 1) : x ∈ WilsonFamily.separated 1 :=
  show Function.Injective x.ofLp from Function.injective_of_subsingleton _

theorem points_zero_eq (x y : Points 0) : x = y := PiLp.ext fun i => i.elim0

/-- (A) With zero insertions, every one-point function of the lattice limit vanishes. -/
theorem one_point_zero (C : WilsonFamily g) (hz : ∀ N p v x U, C.insertion N p v x U = 0)
    {order : ℕ → ℕ} (T : Hierarchy C) (hT : T.Properties order) (a : T.Tag) (x : Points 1) :
    T.correlation none (fun _ : Fin 1 => a) x = 0 := by
  obtain ⟨v, hv⟩ := hT.reconstruction.represents a
  let u : Points 1 → ℂ := T.correlation none (T.project ∘ fun _ : Fin 1 => v)
  have hu_eq : u = T.correlation none (fun _ : Fin 1 => a) := by
    simp only [u]; congr 1; funext i; simp [hv]
  have hcont : Continuous u := by
    have h := hT.reconstruction.smooth none (T.project ∘ fun _ : Fin 1 => v)
    have huniv : (WilsonFamily.separated 1 : Set (Points 1)) = univ :=
      eq_univ_of_forall separated_one_univ
    rw [huniv] at h
    exact (contDiffOn_univ.mp h).continuous
  have hint : ∀ t : WilsonFamily.SeparatedTest 1, ∫ y, t y * u y = 0 := by
    intro t
    obtain ⟨hev, row, hrow, hlim⟩ := hT.wilson 1 (fun _ => v) t
    have hsmear : ∀ N p, C.smear N p (fun _ => v) t = 0 := by
      intro N p
      simp [WilsonFamily.smear, WilsonFamily.finiteMoment, hz]
    have hrow0 : ∀ p, C.suitable p t → row p = 0 := fun p hp =>
      tendsto_nhds_unique (hrow p hp) (by simp only [hsmear]; exact tendsto_const_nhds)
    have hk : (fun k => row (order k)) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [hev] with k hk using hrow0 _ hk
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hk.symm)
  have hae : ∀ᵐ y ∂(volume : Measure (Points 1)), u y = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hcont.locallyIntegrable)
    intro φ hφ hφs
    let t : WilsonFamily.SeparatedTest 1 :=
      ⟨fun y => (φ y : ℂ), (Complex.ofRealCLM.contDiff).comp hφ,
        hφs.comp_left Complex.ofReal_zero, fun y _ => separated_one_univ y⟩
    have := hint t
    simpa [t, Complex.real_smul] using this
  have hzero : u = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (volume : Measure (Points 1)) hcont continuous_const).mp hae
  rw [← hu_eq, hzero]

/-- (B) The zero-point function of the lattice limit is nonzero (the Wilson measure
is a probability measure). -/
theorem zero_point_ne (C : WilsonFamily g) {order : ℕ → ℕ} (T : Hierarchy C)
    (hT : T.Properties order) (f : Fin 0 → T.Tag) (x : Points 0) :
    T.correlation none f x ≠ 0 := by
  intro h0
  let v : Fin 0 → C.Token := Fin.elim0
  let u : Points 0 → ℂ := T.correlation none (T.project ∘ v)
  have hf : f = T.project ∘ v := funext fun i => i.elim0
  have hu0 : ∀ y, u y = 0 := by
    intro y; rw [points_zero_eq y x]; simp only [u, ← hf]; exact h0
  let t : WilsonFamily.SeparatedTest 0 :=
    ⟨fun _ => (1 : ℂ), contDiff_const,
      (Set.Subsingleton.isCompact fun a _ b _ => points_zero_eq a b),
      fun y _ => show Function.Injective y.ofLp from Function.injective_of_subsingleton _⟩
  obtain ⟨hev, row, hrow, hlim⟩ := hT.wilson 0 v t
  haveI := C.probability
  have hsmear : ∀ N p, C.smear N p v t = 1 := by
    intro N p
    haveI := wilsonLaw_isProbability (C.period p * C.denominator N) (C.beta N p) C.haar
    simp [WilsonFamily.smear, WilsonFamily.finiteMoment, t]
  have hrow1 : ∀ p, C.suitable p t → row p = 1 := fun p hp =>
    tendsto_nhds_unique (hrow p hp) (by simp only [hsmear]; exact tendsto_const_nhds)
  have hk : (fun k => row (order k)) =ᶠ[atTop] fun _ => 1 := by
    filter_upwards [hev] with k hk using hrow1 _ hk
  have hone : ∫ y, t y * u y = 1 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hk.symm)
  simp [hu0] at hone

theorem correlation_zero_of_card {C : WilsonFamily g} {order : ℕ → ℕ} (T : Hierarchy C)
    (hT : T.Properties order) (n : ℕ) (hn : n = 0) (f : Fin n → T.Tag) (x : Points n) :
    T.correlation none f x ≠ 0 := by
  subst hn; exact zero_point_ne C T hT f x

theorem correlation_one_of_card (C : WilsonFamily g) (hz : ∀ N p v x U, C.insertion N p v x U = 0)
    {order : ℕ → ℕ} (T : Hierarchy C) (hT : T.Properties order) (n : ℕ) (hn : n = 1)
    (f : Fin n → T.Tag) (a : T.Tag) (hf : ∀ i, f i = a) (x : Points n) :
    T.correlation none f x = 0 := by
  subst hn
  have : f = fun _ => a := funext hf
  rw [this]; exact one_point_zero C hz T hT a x

/-- Probe E. Zero lattice insertions cannot support any hierarchy with the public
`Properties`: the OPE in the unselected phase (Probe D) forces the normalized
zero-point function to be a combination of one-point functions, all of which vanish. -/
theorem no_hierarchy_of_zero_insertions (C : WilsonFamily g)
    (hz : ∀ N p v x U, C.insertion N p v x U = 0) {order : ℕ → ℕ} (T : Hierarchy C)
    (hT : T.Properties order) : False := by
  have hD := empty_cluster T hT.ope none 0
  have hR : (∑ j : Fin (0 + 1), ∑ i : T.Channel j.val,
      T.coefficient (Empty.elim : Empty → T.Tag) j.val i Empty.elim 0 *
        T.grouped none (fun _ : Unit => (⟨j.val, T.actor j.val i⟩ : T.Tag)) (fun _ => 0)
          (Empty.elim : Empty → T.Tag) Empty.elim) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro i _
    have h1 : T.grouped none (fun _ : Unit => (⟨j.val, T.actor j.val i⟩ : T.Tag)) (fun _ => 0)
        (Empty.elim : Empty → T.Tag) Empty.elim = 0 := by
      unfold Hierarchy.grouped
      apply correlation_one_of_card C hz T hT _ (by simp) _ ⟨j.val, T.actor j.val i⟩
      intro k
      simp only [Function.comp_apply]
      generalize (Fintype.equivFin (Unit ⊕ Empty)).symm k = e
      rcases e with u | e
      · rfl
      · exact e.elim
    rw [h1, mul_zero]
  rw [hR] at hD
  revert hD
  unfold Hierarchy.grouped
  exact correlation_zero_of_card T hT _ (by simp) _ _

end ReviewProbeE

#print axioms ReviewProbeE.wilsonLaw_isProbability
#print axioms ReviewProbeE.one_point_zero
#print axioms ReviewProbeE.zero_point_ne
#print axioms ReviewProbeE.no_hierarchy_of_zero_insertions
