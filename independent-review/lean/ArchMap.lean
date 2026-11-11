import ConcreteSU2
import Lean
import Lean.DeclarationRange

/-! Architecture map written for this review (not part of the submission).
1. Top-down proof tree from `YangMills.constructed` (direct value dependencies,
   project theorems/defs only, internal names skipped), depth ≤ 4.
2. Directory-level dependency edges among declarations reachable from
   `YangMills.jointExistence`.
Writes /path/to/ym-release/review/work/audit/{proof-tree.txt,dir-edges.tsv}. -/

namespace ReviewArch
open Lean Elab Command

def projectModule (m : Name) : Bool :=
  (`YM).isPrefixOf m || [`PublicTheory, `PublicWilson, `ChallengeSpec, `ContactSpec,
    `PublicView, `WilsonBridge, `HierarchyBridge, `TraceBridge, `ContactBridge,
    `Construction, `Solution, `ConcreteSU2].contains m

def ownerOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.modules[i.toNat]!.module
  | none => `current

def topDir (m : Name) : String :=
  match m.components with
  | `YM :: d :: _ :: _ => s!"YM.{d}"
  | c :: _ => toString c
  | [] => "?"

def refs (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo i => for c in i.ctors ++ i.all do s := s.insert c
  | .ctorInfo c => s := s.insert c.induct
  | .recInfo r => for c in r.all do s := s.insert c
  | _ => pure ()
  return s

/-- Strip auxiliary suffixes so that `foo._proof_1`, `foo.match_2` map to `foo`. -/
def visible (n : Name) : Name := Id.run do
  let mut m := n
  while m.isInternalDetail || (match m with | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s == "eq_1" || s == "eq_def" | _ => false) do
    match m with
    | .str p _ => m := p
    | .num p _ => m := p
    | .anonymous => break
  return m

end ReviewArch

open Lean Elab Command ReviewArch in
run_cmd do
  let env := (← getEnv).setExporting false
  let k := env.checked.get
  let outDir : System.FilePath := "/path/to/ym-release/review/work/audit"
  IO.FS.createDirAll outDir
  -- reachable set from the public endpoint
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`YangMills.jointExistence]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    unless projectModule (ownerOf env n) do continue
    if let some ci := k.find? n then todo := todo ++ (refs ci).toArray
  -- directory-level edges
  let mut edges : Std.HashMap (String × String) Nat := {}
  for n in seen do
    unless projectModule (ownerOf env n) do continue
    let some ci := k.find? n | continue
    let a := topDir (ownerOf env n)
    for c in refs ci do
      unless projectModule (ownerOf env c) do continue
      let b := topDir (ownerOf env c)
      if a != b then edges := edges.insert (a, b) (edges.getD (a, b) 0 + 1)
  let h ← IO.FS.Handle.mk (outDir / "dir-edges.tsv") .write
  h.putStrLn "from_dir\tto_dir\treferences"
  for ((a, b), c) in edges.toList do h.putStrLn s!"{a}\t{b}\t{c}"
  -- top-down proof tree from YangMills.constructed
  let t ← IO.FS.Handle.mk (outDir / "proof-tree.txt") .write
  let mut printed : NameSet := {}
  let mut frontier : Array (Name × Nat) := #[(`YangMills.constructed, 0)]
  let mut lines : Array String := #[]
  while !frontier.isEmpty do
    let (n, d) := frontier[0]!
    frontier := frontier.extract 1 frontier.size
    if printed.contains n then continue
    printed := printed.insert n
    let some ci := k.find? n | continue
    let m := ownerOf env n
    let line := (← findDeclarationRangesCore? n).map (fun r => toString r.selectionRange.pos.line) |>.getD "?"
    let kind := match ci with | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | _ => "other"
    lines := lines.push s!"{"".pushn ' ' (2*d)}{n}  [{kind}] {m}:{line}"
    if d < 5 then
      let deps := match ci with
        | .thmInfo v => v.value.getUsedConstantsAsSet
        | .defnInfo v => v.value.getUsedConstantsAsSet
        | _ => {}
      let mut kids : NameSet := {}
      for c in deps do
        let v := visible c
        unless projectModule (ownerOf env v) do continue
        if v == n then continue
        match k.find? v with
        | some (.thmInfo _) => kids := kids.insert v
        | _ => pure ()
      for c in kids do frontier := frontier.push (c, d + 1)
  for l in lines do t.putStrLn l
  logInfo m!"ARCH reached={seen.size} dirEdges={edges.size} treeNodes={lines.size}"
