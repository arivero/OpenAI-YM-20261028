import Challenge
import Lean

/-! Review probes written for this verification (not part of the submission).
They import only the public specification (Mathlib-only import closure) and
show which clauses of `YangMills.JointExistence` carry no information about
the construction by themselves. -/

set_option autoImplicit false
noncomputable section
namespace ReviewProbe
open YangMills Filter
open scoped Topology

/-- Probe A. `TraceTest.amplitudePositive` is a fact about the gauge group alone:
it holds for every simple group, independently of any hierarchy. -/
theorem amplitude_positive_of_simple (g : GaugeGroup) (hg : g.IsSimple) :
    0 < 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 := by
  obtain ⟨⟨X, hX, Y, _, hXY⟩, -⟩ := hg
  have hne : g.lieAlgebra ≠ ⊥ := by
    intro h
    rw [h] at hX
    have hX0 : X = 0 := (Submodule.mem_bot ℝ).mp hX
    exact hXY (by simp [hX0])
  have hpos : 1 ≤ Module.finrank ℝ g.lieAlgebra := Submodule.one_le_finrank_iff.mpr hne
  have hr : (0 : ℝ) < Module.finrank ℝ g.lieAlgebra := by exact_mod_cast hpos
  positivity

/-- The same family with every insertion replaced by a constant that ignores the
link configuration. -/
def constInsertions {g : GaugeGroup} (C : WilsonFamily g) (κ : C.Token → ℂ) : WilsonFamily g :=
  { C with insertion := fun _ _ v _ _ => κ v }

/-- Probe B. `WilsonRegularity` constrains `beta` and requires continuity, gauge
invariance and locality of insertions; constant (gauge-field-blind) insertions
satisfy all of it.  Any link between the continuum objects and the Wilson
measure must therefore come from `Hierarchy.Properties`. -/
theorem regular_constInsertions {g : GaugeGroup} (C : WilsonFamily g) (hC : WilsonRegularity C)
    (κ : C.Token → ℂ) : WilsonRegularity (constInsertions C κ) where
  running := hC.running
  continuous _ _ _ _ := continuous_const
  invariant _ _ _ _ _ _ := rfl
  localSupport _ := ⟨∅, fun _ _ _ => by intro _ U V _; rfl⟩

/-- Probe C. The slope in `WilsonRegularity.running` is only required to be
positive; the statement does not fix it to the asymptotic-freedom value. -/
example {g : GaugeGroup} (C : WilsonFamily g) (hC : WilsonRegularity C) :
    ∃ slope : ℝ, 0 < slope := by
  obtain ⟨s, hs, -⟩ := hC.running
  exact ⟨s, hs⟩

/-- Probe D. The OPE clause applied to the EMPTY cluster with no spectators forces an
exact identity, in every phase `s`, including `s = none` (the unselected lattice limit):
the zero-point function equals the degree-0 part of the expansion of "nothing" at `o`,
with the same coefficients in every phase.  This is what couples the lattice limit to
the selected phase (see VERIFICATION.md §4.2). -/
theorem empty_cluster {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
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

end ReviewProbe

#print axioms ReviewProbe.amplitude_positive_of_simple
#print axioms ReviewProbe.regular_constInsertions
#print axioms ReviewProbe.empty_cluster

/-! Statement-closure census: every constant reachable from the type of
`YangMills.JointExistence` (types of all constants, values of definitions),
grouped by owning module root. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let k := env.checked.get
  let some root := k.find? `YangMills.JointExistence | throwError "missing JointExistence"
  let mut todo : Array Name := root.getUsedConstantsAsSet.toArray.push `YangMills.JointExistence
  let mut seen : NameSet := {}
  let mut byRoot : Std.HashMap Name Nat := {}
  let mut project : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := k.find? n | throwError "missing {n}"
    let mod := match env.getModuleIdxFor? n with
      | some i => env.header.modules[i.toNat]!.module
      | none => `current
    byRoot := byRoot.insert mod.getRoot (byRoot.getD mod.getRoot 0 + 1)
    if [`PublicTheory, `PublicWilson, `ChallengeSpec].contains mod then project := project.push n
    -- follow the type always, and the value of definitions (not proofs of theorems)
    let mut next := ci.type.getUsedConstantsAsSet
    match ci with
    | .defnInfo d => next := next.union d.value.getUsedConstantsAsSet
    | .inductInfo i => for c in i.ctors ++ i.all do next := next.insert c
    | .ctorInfo c => next := next.insert c.induct
    | _ => pure ()
    todo := todo ++ next.toArray
  logInfo m!"STATEMENT_CLOSURE constants={seen.size} byModuleRoot={byRoot.toList}"
  logInfo m!"STATEMENT_CLOSURE projectConstants={project.size}"
  let axs ← collectAxioms `YangMills.jointExistence
  logInfo m!"REFERENCE_THEOREM_AXIOMS (expected to contain sorryAx) {axs}"
