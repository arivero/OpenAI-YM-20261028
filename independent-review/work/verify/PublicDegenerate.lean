import ChallengeSpec
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
end ReviewProbeE

namespace ReviewVerify2
open YangMills MeasureTheory Filter Set TopologicalSpace
open scoped Topology

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

def haarP (g : GaugeGroup) : Measure g.image := Measure.haarMeasure (⊤ : PositiveCompacts g.image)
instance (g : GaugeGroup) : IsProbabilityMeasure (haarP g) :=
  ⟨by unfold haarP; simpa using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts g.image))⟩
instance (g : GaugeGroup) : (haarP g).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

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

/-- A public Wilson family with no tokens. -/
def trivialPublic (g : GaugeGroup) : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict := fun a b h => by simpa using h
  denominatorStrict := fun a b h => by simpa using h
  beta N _ := Real.log ((N + 2 : ℕ) : ℝ)
  haar := haarP g
  probability := inferInstance
  invariantHaar := inferInstance
  Token := Empty
  insertion _ _ v := v.elim

/-- For every gauge group (simple or not) and every volume order, the public pair
`WilsonRegularity ∧ Converges` is met by a family with no observables. -/
theorem public_wilson_degenerate (g : GaugeGroup) (order : ℕ → ℕ) :
    WilsonRegularity (trivialPublic g) ∧ (trivialPublic g).Converges order (fun _ _ => 1) := by
  refine ⟨⟨?_, fun _ _ v => v.elim, fun _ _ v => v.elim, fun v => v.elim⟩, ?_⟩
  · refine ⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩
    have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N + 2 by omega))
    simp only [trivialPublic, WilsonFamily.mesh, inv_inv, PNat.mk_coe]
    rw [div_self hpos.ne', sub_self, abs_zero]
    exact hε
  · intro n v t
    cases n with
    | succ n => exact (v 0).elim
    | zero =>
      have hsmear : ∀ N p, (trivialPublic g).smear N p v t = t 0 := by
        intro N p
        haveI : IsProbabilityMeasure (trivialPublic g).haar := (trivialPublic g).probability
        haveI := ReviewProbeE.wilsonLaw_isProbability ((trivialPublic g).period p * (trivialPublic g).denominator N)
          ((trivialPublic g).beta N p) (trivialPublic g).haar
        simp only [WilsonFamily.smear, WilsonFamily.finiteMoment, Finset.univ_eq_empty,
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

end ReviewVerify2
#print axioms ReviewVerify2.public_wilson_degenerate
