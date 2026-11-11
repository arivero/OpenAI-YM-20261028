import ConcreteSU2
import Lean
import Lean.Replay

/-! Independent kernel replay written for this review (not part of the submission).
Collects every project declaration reachable from `YangMills.jointExistence`
(types, values, inductive companions), imports a base environment consisting only
of the non-project modules (Lean core, Batteries, Mathlib, ...), and replays the
collected declarations into that base with `Lean.Environment.replay` (kernel check).
-/

namespace ReviewReplay
open Lean Elab Command

def projectModule (m : Name) : Bool :=
  (`YM).isPrefixOf m || [`PublicTheory, `PublicWilson, `ChallengeSpec, `ContactSpec,
    `PublicView, `WilsonBridge, `HierarchyBridge, `TraceBridge, `ContactBridge,
    `Construction, `Solution, `ConcreteSU2].contains m

end ReviewReplay

open Lean Elab Command ReviewReplay in
run_cmd do
  let env := (← getEnv).setExporting false
  let k := env.checked.get
  let owner (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.modules[i.toNat]!.module
    | none => `current
  let roots : Array Name := #[`YangMills.jointExistence, `YangMills.su2Theory]
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut project : Std.HashMap Name ConstantInfo := {}
  let mut external : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := k.find? n | throwError "missing {n}"
    unless projectModule (owner n) do
      external := external.insert n
      continue
    project := project.insert n ci
    let mut next := ci.getUsedConstantsAsSet
    match ci with
    | .inductInfo i => for c in i.ctors ++ i.all do next := next.insert c
    | .ctorInfo c => next := next.insert c.induct
    | .recInfo r => for c in r.all do next := next.insert c
    | _ => pure ()
    todo := todo ++ next.toArray
  let mut bad : Array Name := #[]
  for (n, ci) in project.toList do
    if ci.isUnsafe || ci.isPartial || ci matches .axiomInfo _ then bad := bad.push n
  unless bad.isEmpty do throwError "unsafe/partial/axiom project dependencies: {bad}"
  let externals := env.header.modules.filterMap fun m =>
    if projectModule m.module then none else some ({module := m.module} : Import)
  let base ← liftIO <| importModules externals {}
  for n in external do
    unless (base.checked.get.find? n).isSome do throwError "external dependency missing from base: {n}"
  for (n, _) in project.toList do
    if (base.checked.get.find? n).isSome then throwError "project name already in base: {n}"
  logInfo m!"OWN_REPLAY_START projectDecls={project.size} externalRefs={external.size} baseModules={externals.size}"
  let t0 ← IO.monoMsNow
  let checked ← liftIO <| base.replay project
  let t1 ← IO.monoMsNow
  for r in roots do
    let some (.thmInfo v) := checked.checked.get.find? r | throwError "root {r} not in replayed env"
    let some (.thmInfo s) := project[r]? | throwError "root {r} not collected"
    unless v.type == s.type && v.value == s.value do throwError "replayed {r} differs"
  logInfo m!"OWN_REPLAY_PASS projectDecls={project.size} seconds={(t1 - t0) / 1000}"
