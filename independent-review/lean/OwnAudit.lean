import ConcreteSU2
import Lean

/-! Independent audit written for this review (not part of the submission).
Run from the submission root with `lake env lean <this file>` after the build.
Writes TSV summaries to /path/to/ym-release/review/work/audit/. -/

set_option autoImplicit false

#check @YangMills.jointExistence
#check @YangMills.su2Theory
#print axioms YangMills.jointExistence
#print axioms YangMills.constructed
#print axioms YangMills.su2Theory
#print axioms YangMills.su2Simple
#print axioms YM.Nonperturbative.existence

namespace ReviewAudit
open Lean Elab Command

def projectModule (m : Name) : Bool :=
  (`YM).isPrefixOf m || [`PublicTheory, `PublicWilson, `ChallengeSpec, `Challenge, `ContactSpec,
    `PublicView, `WilsonBridge, `HierarchyBridge, `TraceBridge, `ContactBridge,
    `Construction, `Solution, `ConcreteSU2].contains m

def ownerOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.modules[i.toNat]!.module
  | none => `current

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- All constants referenced by a declaration (type and value), plus the
companion constants of inductive types. -/
def refs (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo i => for c in i.ctors ++ i.all do s := s.insert c
  | .ctorInfo c => s := s.insert c.induct
  | .recInfo r => for c in r.all do s := s.insert c
  | _ => pure ()
  return s

/-- Project declarations reachable from `roots` through types and values. -/
def reach (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let k := env.checked.get
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    unless projectModule (ownerOf env n) do continue
    out := out.insert n
    if let some ci := k.find? n then
      todo := todo ++ (refs ci).toArray
  return out

def topDir (m : Name) : String :=
  match m.components with
  | `YM :: d :: _ :: _ => s!"YM.{d}"
  | c :: _ => toString c
  | [] => "?"

end ReviewAudit

open Lean Elab Command ReviewAudit in
run_cmd do
  let env := (← getEnv).setExporting false
  let k := env.checked.get
  let outDir : System.FilePath := "/path/to/ym-release/review/work/audit"
  IO.FS.createDirAll outDir
  -- 1. the endpoint is a theorem whose type is literally the public proposition
  let some sol := k.find? `YangMills.jointExistence | throwError "missing solution theorem"
  unless sol matches .thmInfo _ do throwError "jointExistence is not a theorem"
  unless sol.type == .const `YangMills.JointExistence [] do throwError "unexpected type {sol.type}"
  logInfo m!"ENDPOINT YangMills.jointExistence : {sol.type} (theorem, owner {ownerOf env `YangMills.jointExistence})"
  -- 2. statement closure is identical to the separately loaded reference environment
  let reference ← liftIO <| importModules #[{module := `Challenge}] {}
  let rk := reference.checked.get
  for m in reference.header.modules do
    if (`YM).isPrefixOf m.module then throwError "YM module in reference closure: {m.module}"
  let mut todo : Array Name := #[`YangMills.JointExistence]
  let mut seen : NameSet := {}
  let mut nPublic : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := k.find? n | throwError "missing {n}"
    let some ri := rk.find? n | throwError "statement constant {n} absent from reference environment"
    unless ci.type == ri.type && ci.levelParams == ri.levelParams &&
        ci.value? (allowOpaque := true) == ri.value? (allowOpaque := true) && kindOf ci == kindOf ri do
      throwError "statement constant {n} differs between solution and reference"
    unless ownerOf env n == ownerOf reference n do throwError "owner differs for {n}"
    if projectModule (ownerOf env n) then nPublic := nPublic + 1
    if (`YM).isPrefixOf (ownerOf env n) then throwError "statement depends on YM module: {n}"
    let mut next := ci.type.getUsedConstantsAsSet
    match ci with
    | .defnInfo d => next := next.union d.value.getUsedConstantsAsSet
    | .inductInfo i => for c in i.ctors ++ i.all do next := next.insert c
    | .ctorInfo c => next := next.insert c.induct
    | .recInfo r => for c in r.all do next := next.insert c
    | _ => pure ()
    todo := todo ++ next.toArray
  logInfo m!"STATEMENT_MATCH constants={seen.size} publicSpecConstants={nPublic} (all identical to reference; no YM owner)"
  -- 3. inventory of every imported project declaration
  let mut total : Nat := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut bad : Array String := #[]
  let mut all : Array (Name × Name × String) := #[]
  for (n, ci) in k.constants.toList do
    let m := ownerOf env n
    unless projectModule m do continue
    total := total + 1
    kinds := kinds.insert (kindOf ci) (kinds.getD (kindOf ci) 0 + 1)
    all := all.push (n, m, kindOf ci)
    if ci matches .axiomInfo _ then bad := bad.push s!"AXIOM {n} in {m}"
    if ci.isUnsafe then bad := bad.push s!"UNSAFE {n} in {m}"
    if ci.isPartial then bad := bad.push s!"PARTIAL {n} in {m}"
    if ci matches .opaqueInfo _ then bad := bad.push s!"OPAQUE {n} in {m}"
    if (refs ci).contains `sorryAx then bad := bad.push s!"SORRYAX {n} in {m}"
  logInfo m!"INVENTORY projectDeclarations={total} kinds={kinds.toList}"
  let unsafeRec := bad.filter (fun s => (s.splitOn "._unsafe_rec ").length > 1)
  let other := bad.filter (fun s => (s.splitOn "._unsafe_rec ").length == 1)
  logInfo m!"INVENTORY flagged={bad.size} compilerUnsafeRecHelpers={unsafeRec.size} otherFlagged={other.size}: {other.toList.take 40}"
  -- 4. axioms of the advertised endpoints
  let headlines : List Name := [`YangMills.jointExistence, `YangMills.constructed, `YangMills.su2Simple,
    `YangMills.su2Theory, `YM.Nonperturbative.existence, `YM.Nonperturbative.continuum,
    `YM.Nonperturbative.continuum_with_position_tests, `YM.Contacts.Solstice.celestial,
    `YM.Pert.Position.finite_leading, `YM.Pert.Position.normalized_four, `YM.Pert.Parity.parityEndpoint,
    `YM.Pert.Parity.low_read, `YM.Pert.Asymptotics.comparison, `YM.SharpGram.habitat,
    `YM.SharpGram.inletFirst, `YM.SharpGram.outletFirst, `YM.Independent.Core.point]
  for h in headlines do
    let axs ← collectAxioms h
    logInfo m!"AXIOMS {h} {axs}"
  -- 5. reachability: from the public endpoint alone and from all 17 endpoints
  let r1 := reach env #[`YangMills.jointExistence]
  let r17 := reach env headlines.toArray
  logInfo m!"REACH fromJointExistence={r1.size} from17={r17.size} of projectDeclarations={total}"
  -- declarations generated by the `vintage` metaprogram (YM/UVExtension/Orchard/Barrel.lean)
  let vint := all.filter (fun (n, _, _) => n.getRoot == `Vintage)
  let vintReached := vint.filter (fun (n, _, _) => r1.contains n)
  logInfo m!"VINTAGE generated={vint.size} reachedFromJointExistence={vintReached.size}"
  let recReached := all.filter (fun (n, _, _) => (r17.contains n) && (toString n).endsWith "._unsafe_rec")
  logInfo m!"UNSAFE_REC reachedFrom17={recReached.size}"
  let h ← IO.FS.Handle.mk (outDir / "declarations.tsv") .write
  h.putStrLn "declaration\tmodule\ttopdir\tkind\tinternal\treached_from_jointExistence\treached_from_17"
  let mut dirStats : Std.HashMap String (Nat × Nat × Nat) := {}
  for (n, m, kd) in all do
    let a := r1.contains n
    let b := r17.contains n
    h.putStrLn s!"{n}\t{m}\t{topDir m}\t{kd}\t{n.isInternalDetail}\t{a}\t{b}"
    let (t, x, y) := dirStats.getD (topDir m) (0, 0, 0)
    dirStats := dirStats.insert (topDir m) (t + 1, x + (if a then 1 else 0), y + (if b then 1 else 0))
  let d ← IO.FS.Handle.mk (outDir / "by-topdir.tsv") .write
  d.putStrLn "topdir\tdeclarations\treached_from_jointExistence\treached_from_17"
  for (dir, (t, x, y)) in dirStats.toList do
    d.putStrLn s!"{dir}\t{t}\t{x}\t{y}"
  logInfo "OWN_AUDIT_DONE"
