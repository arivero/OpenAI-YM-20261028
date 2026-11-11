import PublicWilson

/-!
One-shot dimension probe for the independent review; not part of the submission.

VariationAnisotropic changes periods while retaining Fin 4, so it cannot
express the dimension changes considered here. We extend the definitions of
PublicWilson, preserving its D=4 case definitionally, and prove the empty-action
D=1 endpoint. No continuum construction in D=2 or D=3 is provided here.
-/
set_option autoImplicit false
noncomputable section
namespace ReviewDimension
open YangMills MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

abbrev Axis (D : ℕ) := Fin D
abbrev Site (D : ℕ) (l : ℕ+) := Axis D → ZMod l.val
abbrev Directions (D : ℕ) := {p : Axis D × Axis D // p.1 < p.2}
abbrev Configuration (D : ℕ) (g : GaugeGroup) (l : ℕ+) :=
  (Site D l × Axis D) → g.image

def plaquette {D : ℕ} {g : GaugeGroup} {l : ℕ+}
    (U : Configuration D g l) (x : Site D l) (i j : Axis D) : g.image :=
  U (x,i) * (U (x + Pi.single i 1,j) *
    ((U (x + Pi.single j 1,i))⁻¹ * (U (x,j))⁻¹))

def wilsonEnergy (D : ℕ) {g : GaugeGroup} {l : ℕ+}
    (U : Configuration D g l) : ℝ :=
  ∑ p : Site D l × Directions D,
    (1 - ((plaquette U p.1 p.2.val.1 p.2.val.2).val.val.trace).re /
      ((g.n+1 : ℕ) : ℝ))

def wilsonLaw (D : ℕ) (g : GaugeGroup) (l : ℕ+) (β : ℝ)
    (haar : Measure g.image) : Measure (Configuration D g l) :=
  let prior : Measure (Configuration D g l) := Measure.pi fun _ => haar
  let density := fun U : Configuration D g l => Real.exp (-β * wilsonEnergy D U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)

theorem site_card (D : ℕ) (l : ℕ+) : Fintype.card (Site D l) = l.val ^ D := by
  simp [Site, Axis, ZMod.card]

theorem directions_four : Fintype.card (Directions 4) = 6 := by decide
theorem directions_three : Fintype.card (Directions 3) = 3 := by decide
theorem directions_two : Fintype.card (Directions 2) = 1 := by decide
theorem directions_one : Fintype.card (Directions 1) = 0 := by decide

theorem energy_four {g : GaugeGroup} {l : ℕ+} (U : Configuration 4 g l) :
    wilsonEnergy 4 U = YangMills.wilsonEnergy U := rfl

theorem law_four (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    wilsonLaw 4 g l β haar = YangMills.wilsonLaw g l β haar := rfl

instance : IsEmpty (Directions 1) := ⟨fun p =>
  (ne_of_lt p.property) (Subsingleton.elim _ _)⟩

theorem energy_one {g : GaugeGroup} {l : ℕ+} (U : Configuration 1 g l) :
    wilsonEnergy 1 U = 0 := by
  simp [wilsonEnergy]

/-- With normalized Haar input, the D=1 Wilson law is exactly the product
prior at every lattice size and every real beta. Global circle holonomy is
not removed by this statement. -/
theorem law_one (g : GaugeGroup) (l : ℕ+) (β : ℝ)
    (haar : Measure g.image) [IsProbabilityMeasure haar] :
    wilsonLaw 1 g l β haar = Measure.pi (fun _ : Site 1 l × Axis 1 => haar) := by
  simp [wilsonLaw, energy_one]

theorem law_one_beta_independent (g : GaugeGroup) (l : ℕ+) (β γ : ℝ)
    (haar : Measure g.image) [IsProbabilityMeasure haar] :
    wilsonLaw 1 g l β haar = wilsonLaw 1 g l γ haar := by
  rw [law_one, law_one]

/-- Trace of the physical Maxwell tensor with its fixed 1/4 coefficient.
The q's represent its diagonal quadratic contractions. This algebraic
identity does not assume or construct a quantum field. -/
theorem stress_trace (D : ℕ) (q : Fin D → ℝ) :
    (∑ a, (q a - (1/4 : ℝ) * ∑ b, q b)) =
      (1 - (D : ℝ)/4) * ∑ b, q b := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem stress_trace_four (q : Fin 4 → ℝ) :
    (∑ a, (q a - (1/4 : ℝ) * ∑ b, q b)) = 0 := by
  rw [stress_trace]
  norm_num

theorem stress_trace_three (q : Fin 3 → ℝ) :
    (∑ a, (q a - (1/4 : ℝ) * ∑ b, q b)) = (1/4 : ℝ) * ∑ b, q b := by
  rw [stress_trace]
  norm_num

theorem stress_trace_two (q : Fin 2 → ℝ) :
    (∑ a, (q a - (1/4 : ℝ) * ∑ b, q b)) = (1/2 : ℝ) * ∑ b, q b := by
  rw [stress_trace]
  norm_num

#print axioms energy_four
#print axioms law_four
#print axioms energy_one
#print axioms law_one
#print axioms law_one_beta_independent
#print axioms site_card
#print axioms directions_four
#print axioms directions_three
#print axioms directions_two
#print axioms directions_one
#print axioms stress_trace
#print axioms stress_trace_four
#print axioms stress_trace_three
#print axioms stress_trace_two
end ReviewDimension
