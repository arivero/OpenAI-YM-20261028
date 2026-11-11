# Verification report: OpenAI Lean formalization of 4D pure Yang–Mills existence (submission of 28 Oct 2026)

**Independent review by the fork owner (arivero).** This report was written by a Claude Opus subagent that ran the build and the audit under the direction of Claude Fable 5.2 in Claude Code; "I" and "this review" refer to that agent's work. It is separate from OpenAI's submission and from the Yang–Mills group's assessment, and carries no endorsement from either. Passages marked "Editor's note" were added by Claude Fable 5.2 after first-hand checks of the cited sources. Paths of the form `/path/to/ym-release/…` refer to the local working directory that held both clones and this review; `review/…` is this directory.

Run date 2026-11-11, Linux x86_64, 16 cores, 30 GB RAM. Every result below comes from a command this review ran, unless the text marks it as a quotation from a repository file or from the committee's records. Logs: `/path/to/ym-release/review/logs/`. Scripts: `review/scripts/`. Review-authored Lean files: `review/lean/` (outside both clones).

Repositories examined:

* `OpenAI-YM-20261028` at commit `3456e5e` (one commit, branch `main`): 9,508 tracked files, 9,477 `.lean` files, 987,586 lines of Lean.
* `YM` (committee) at commit `55ba9fc`: `docs/assessment-1.pdf` (35 pages, read in full) and `submissions/openai-20261028/` (submission copy, 43 review modules in `checks/`, Comparator configurations and controls in `verification/`, evidence, provenance).

## 0. Verdict

| Question | Verdict | Evidence |
|---|---|---|
| Builds from source with the pinned toolchain? | Yes. `lake build WilsonReference WilsonConstruction` exit 0 in 2 h 45 min 32 s; 9,470 project modules; 2,453 warnings (same as the committee), the only `sorry` being `Challenge.lean:6` | §1, `logs/02-build.log` |
| Mathlib rebuilt from source? | No. `lake exe cache get` fetched and unpacked 8,639 cache files for rev `81a5d25`; the build compiled only project modules (`Built Mathlib.*`: 0 lines) | §1, `logs/01-cache-get.log` |
| README verification commands reproduce the shipped logs? | Yes, in every mathematical field. VerifyJoint (exit 0, 11.3 min) prints the same 21 result lines; Usage (exit 0 after pinning the toolchain in the scratch directory) prints the same summary, `module-usage.tsv` byte-identical, `declaration-usage.tsv` off in three line numbers; CompactCheck (exit 0) prints the same two lines. Two shipped records predate the final sources (`PublicTheory.lean` hash, `PiDensity.lean` line shift) | §2 |
| Axioms clean (this review's own `#print axioms`)? | Yes. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `jointExistence`, `constructed`, `su2Theory`, `su2Simple`, `existence` and all 17 endpoints; no project axiom, no `sorryAx`; my reference-vs-solution comparison of the 7,122-constant statement closure finds no difference and no `YM` constant | §3.1, `logs/31-own-audit.log` |
| Escape hatches in the source? | None that affect proofs: one `sorry` (`Challenge.lean:6`, the reference placeholder); no `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `unsafe` or `debug.*` options; the only partial/opaque constants are two helpers of the one metaprogram (`vintage`, which adds declarations through the kernel) and 302 compiler `._unsafe_rec` helpers, none reached | §3.2 |
| Solution independent of the placeholder? | Yes: `Challenge` is outside the import closure of `Solution`; the statement closure in the solution environment is identical to the separately loaded reference | §3.1, `logs/11-import-graph.log` |
| Kernel replay of what the theorem depends on? | Yes, twice: the submission's VerifyJoint replays 100,168 reachable project declarations (pass); my own `OwnReplay.lean` replays 93,999 declarations reachable from `jointExistence` and `su2Theory` into a Mathlib-only base (pass, 564 s). Both use the Lean 4.32.0 kernel; Comparator adds the Lean 4.34.0 kernel (§6.3) | §2, §3.1 |
| Statement non-vacuous? | Yes, as far as I can determine: the hypothesis is satisfiable (SU(2)); trivial Hilbert spaces, finite free-field descriptions and zero lattice insertions are excluded (the last one machine-checked, Probe E); the OPE clause over the unselected phase forces the lattice limit itself to carry the r⁻⁸log⁻²(1/r) law (formal for zero insertions; in general it uses one standard, unformalized Wightman-theory step). A generalized-free-field selected phase remains possible. | §4.2 |
| Faithful to "existence of 4D pure Yang–Mills"? | Partially. Faithful: genuine Wilson LGT with Haar measure and log-running β, ℝ⁴, Wightman W0–W3 (proper orthochronous Poincaré, spectrum condition, unique vacuum, locality) for a phase of the lattice limit. Weaker than the physics claim: one phase of a subsequential infinite-volume limit; uniqueness and universality open; in the public statement the observables need not be curvature polynomials, the slope and Θ's normalization are unspecified, and non-Gaussianity is unproved. The detailed theorem and the committee's combined target add the Yang–Mills identification on internal definitions. | §4.3–4.5 |
| Mass gap addressed? | No. Spectral content is the spectrum condition and vacuum uniqueness only; README, code, assessment and committee checks all say so. The detailed theorem's infrared bounds are power laws (spectral weight O(u²) below energy u, e^{−sH} − P₀ = O(s⁻²) on word states), compatible with a massless spectrum. The "positive lattice probe" is a nonzero dimensionful correlation, and the lgt strong-coupling mass-gap files are provenance snapshots (small-β lattice results, unused). | §4.6 |
| Committee copy identical to the OpenAI repo? | Yes, byte for byte (9,508 files; `SOURCES.sha256` verifies in both) | §6.1 |
| Committee runner stages run here | `integrity` (twice), `tools`, `controls`, `comparator --target submission`, `review`, `comparator --target acceptance`, `comparator --target ope`: every `result.json` says `passed`. Comparator printed "Lean default kernel accepts the solution / Your solution is okay!" for `YangMills.jointExistence` (1,078 s), `YMReview.Acceptance.combined_acceptance` (1,161 s) and `YMReview.OPE.constructed` (1,083 s), in the unsandboxed development mode (`fake-landrun.sh`, no external kernel) that the committee also used | §6.3 |

---

## 1. Build (task 1)

| Step | Result |
|---|---|
| Toolchain | `elan toolchain install leanprover/lean4:v4.32.0`: exit 0, 58 s; `Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)`, the same commit as the shipped `joint-check.log` |
| Dependencies | all 9 packages checked out at the manifest revisions with clean trees (`mathlib 81a5d257c8e410db227a6665ed08f64fea08e997`, `batteries 023ce7d…`, `aesop a7dbf0c…`, `Qq 38d591e…`, `proofwidgets 6e311e2…`, `importGraph 7e9612b…`, `LeanSearchClient c5d5b8f…`, `plausible e12c191…`, `Cli 88679d0…`) |
| `lake exe cache get` | exit 0, wall 2:19; built the 26-job `cache` executable, then "Attempting to download 8639 file(s) from leanprover-community/mathlib4 cache" … "Decompressed 8639 file(s)"; 8,275 Mathlib `.olean` files present afterwards |
| `lake build WilsonReference WilsonConstruction` | **exit 0**, "Build completed successfully (18126 jobs).", wall **2:45:32** (9,933 s), 108,078 s user CPU (1207 % average utilization), started 05:19:07, ended 08:04:40; 9,470 project modules compiled (13 top-level files + 9,457 `YM.*`), the same count the committee reports; 2,453 warning lines in 1,063 files, again identical to the committee's count; the only `sorry` warning is `Challenge.lean:5:8: declaration uses sorry`; no `error` lines |

Mathlib was not rebuilt: every `Built …` line in the build log names a project module (`YM.*` or a top-level file); the first project job appears at `[8654/10713]`, after the cached dependency jobs.

Memory: Lake ran up to 16 `lean` processes; the 60-second sampler (`logs/02-build.mem.log`, 166 samples) recorded at most 18.7 GB used and at least 12.2 GB available system-wide; the largest single `lean` process reached 14.1 GB RSS. Parallelism dropped to 1–6 processes for the last ~45 minutes: the longest import chain ending at `Solution` is 518 modules long, and its tail (`YM.FullVolume.Reel.*`, `YM.RG17.*`, `YM.R2I.*`, the bridges) builds serially. Slowest modules: `YM.MultipleContact.Bunch.Guard` 226 s, `YM.Planned.PRIMARY_INTEGRAL_295.Lumos` 179 s, `YM.FullVolume.Luna.Eaves` 165 s. No process was killed and no OOM appeared in the log (`dmesg` is not readable for this user; `journalctl -k` shows no entries).

Tail of the build log:

```
✔ [18122/18126] Built Construction (3.8s)
✔ [18123/18126] Built YM.Examples.SU2 (6.1s)
✔ [18124/18126] Built Solution (3.7s)
✔ [18125/18126] Built ConcreteSU2 (3.4s)
Build completed successfully (18126 jobs).
	Command being timed: "lake build WilsonReference WilsonConstruction"
	User time (seconds): 108078.45
	Percent of CPU this job got: 1207%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:45:32
	Maximum resident set size (kbytes): 13165148
END 2026-11-11T08:04:40+01:00 EXIT=0 WALL_SECONDS=9933
```

Disk: the finished `.lake` tree (dependencies plus build) occupies 48 GB, close to the committee's "about 52 GiB"; free space on `/` went from 107 GB to 53 GB, including the Comparator tools (0.6 GB), the separate Lean 4.34.0 toolchain (2.9 GB) and the Mathlib cache (0.4 GB).

Warning mix (top kinds): 797 unused section variables, 331 unused simp arguments, 171 + 49 unused variable names, 50 `<;>` style notes, 44 unreachable tactics.


## 2. README verification commands, rerun, compared with the shipped logs

I read the three scripts before running them. `VerifyJoint.lean` (107 lines) is a sound design: it rejects implementation modules in the reference closure (lines 21-24), requires the endpoint type and universe parameters to equal the reference's (lines 25-30), collects axioms of every endpoint and every external boundary constant (lines 35-52), compares each reachable public-spec declaration with the reference copy (lines 55-59), rejects unsafe, partial and axiom project dependencies (lines 60-61), and replays all reachable project declarations into an environment imported from the external modules only (lines 65-93), checking that the replayed endpoint terms equal the submitted ones (lines 94-98). Weak points, none of them exploitable as far as I can see: it trusts the headline list it reads from `verification/joint-headlines.txt`, and its notion of "project module" is a hand-written list (lines 12-15). My own audit (§3.1) uses independent code for the same questions. `verification/Usage.lean` writes `verification/declaration-usage.tsv` and `verification/module-usage.tsv` relative to the current directory (lines 51, 60), which is why I ran it from a scratch directory. `verification/CompactCheck.lean` imports only `ChallengeSpec` and derives compact-set forms of the two OPE bounds.

| Command | Exit, wall time | Output compared with the shipped log |
|---|---|---|
| `lake env lean -j1 -DmaxHeartbeats=0 -DmaxRecDepth=4096 VerifyJoint.lean` | 0, 677 s (max RSS 27 GB, shared pages included) | The 21 result lines (`TYPE_MATCH`, 17 `ENDPOINT_AXIOMS … [propext, Classical.choice, Quot.sound]`, `REPLAY_START project=100168 external=14364`, `REPLAY_PASS project=100168 external=14364 endpoints=17 duplicateAliases=0`, `Entering kernel replay …`) are identical to those in `verification/joint-check.log`. The shipped log's other lines (`PUBLIC BUILD …`, `Checking …`, `PASS …`, `COMPILE_PASS`) come from a wrapper script absent from the distribution. |
| `lake env lean -j1 -DmaxHeartbeats=0 verification/Usage.lean` | first attempt exit 1 in 5 s; rerun exit 0, 27 s | The first attempt ran from a scratch directory without a `lean-toolchain` file, so elan picked the default Lean 4.35.0 and reported `failed to read file '…/ConcreteSU2.olean', incompatible header`; with the clone's `lean-toolchain` copied into the scratch directory the rerun printed `USAGE_PASS headlines=17 project=250319 used=100168 outside=150151 modules=9469 modulesWithNoUsedDeclaration=2946`, identical to `verification/usage.log`. The regenerated `module-usage.tsv` is byte-identical to the shipped one; the regenerated `declaration-usage.tsv` (sha256 `9dc9a62a163d…`) differs from the shipped one (`1f16d6cbf7cd…`) in exactly three source-line fields, all in `YM/Work/F05/PiDensity.lean` (17→19, 43→45, 51→53): the shipped table was generated before two more lines were added above `lprodFin`, where the attribution comment now sits (`PiDensity.lean:14-17`). The committee recorded the same hash change (`evidence/historical/submission-comparator/result.json`, `preexisting_manifest_differences`). |
| `lake env lean -j1 verification/CompactCheck.lean` | 0, 7 s | `COMPACT_ESTIMATE YangMills.CompactCheck.compactCoefficient [propext, Classical.choice, Quot.sound]` and the same for `compactRemainder`, identical to `verification/compact-check.log`; that log's extra `COMPACT_CHECK_PASS` line comes from a wrapper (the file prints no such line). |

Two shipped records do not match the distributed sources: `joint-check.log`'s `SOURCE_SHA256` for `PublicTheory.lean` (§6.1) and `declaration-usage.tsv`'s three line numbers. Both point to edits made after OpenAI's last recorded run (a `PublicTheory.lean` revision and an attribution comment); my reruns on the distributed sources give the same results as the shipped logs in every mathematical field.

The README's other claims I could test directly: "The 17 audited theorems reach 100,168 of 250,319 imported project declarations" — my own traversal (§3.1) gives exactly 100,168 of 250,319; "The only placeholder in the new files is the reference theorem in Challenge.lean" — confirmed (§3.2); "The standalone Comparator executable was not run" (by OpenAI) — the committee and this review ran it (§6.3).

## 3. Axiom and escape-hatch audit (task 2)

### 3.1 This review's own axiom and statement check

`review/lean/OwnAudit.lean` lives outside the clone, imports `ConcreteSU2` (hence `Solution`), and was run with `lake env lean` from the clone root (log `logs/31-own-audit.log`). It does five things, written without reference to `Verify*.lean`:

1. `#print axioms` for the public theorem, the detailed theorem, the SU(2) theorems and `YM.Nonperturbative.existence`, plus `collectAxioms` for all 17 endpoints listed in `verification/joint-headlines.txt`.
2. Checks that `YangMills.jointExistence` is a `theorem` whose type is literally the constant `YangMills.JointExistence`.
3. Loads the reference module `Challenge` into a separate environment with `importModules` and walks the statement closure of `YangMills.JointExistence` (types of all constants, values of definitions, inductive companions), requiring every constant to exist in the reference with identical type, universe parameters, value and kind, and the same owning module; it fails if any constant is owned by a `YM.*` module.
4. Inventories every project declaration (kind, axioms, `unsafe`, `partial`, `opaque`, direct `sorryAx` references).
5. Computes reachability from the endpoints (§5.4).

Output, verbatim (one repeated block elided):

```
YangMills.jointExistence : YangMills.JointExistence
YangMills.su2Theory : ∃ C,
  YangMills.WilsonRegularity C ∧ ∀ (p : ℕ → ℕ), StrictMono p → ∃ q, StrictMono q ∧ ∃ T, T.Properties (p ∘ q)
'YangMills.jointExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.constructed' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.su2Theory' depends on axioms: [propext, Classical.choice, Quot.sound]
'YangMills.su2Simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'YM.Nonperturbative.existence' depends on axioms: [propext, Classical.choice, Quot.sound]
ENDPOINT YangMills.jointExistence : YangMills.JointExistence (theorem, owner Solution)
STATEMENT_MATCH constants=7122 publicSpecConstants=180 (all identical to reference; no YM owner)
INVENTORY projectDeclarations=250319 kinds=[(inductive, 4176), (opaque, 2), (ctor, 4319),
 (def, 101848), (theorem, 135798), (rec, 4176)]
INVENTORY flagged=304 compilerUnsafeRecHelpers=302 otherFlagged=2:
 [OPAQUE _private.YM.UVExtension.Orchard.Barrel.0.Aging.ferment in YM.UVExtension.Orchard.Barrel,
  OPAQUE _private.YM.UVExtension.Orchard.Barrel.0.Aging.store in YM.UVExtension.Orchard.Barrel]
AXIOMS YangMills.jointExistence [propext, Classical.choice, Quot.sound]
… (same three axioms for all 17 endpoints of verification/joint-headlines.txt)
REACH fromJointExistence=93969 from17=100168 of projectDeclarations=250319
VINTAGE generated=208 reachedFromJointExistence=0
UNSAFE_REC reachedFrom17=0
OWN_AUDIT_DONE
TIME wall=72.99 s maxrss=20235364 KB
```

Reading: every endpoint depends only on `propext`, `Classical.choice`, `Quot.sound`; the statement closure (7,122 constants, 180 of them from `PublicTheory`/`PublicWilson`/`ChallengeSpec`, the rest from Lean core, Batteries and Mathlib) is identical in the solution and reference environments and contains no `YM` constant; among all 250,319 project declarations there is no axiom and no direct `sorryAx`; the only `unsafe`/`partial`/`opaque` constants are 302 compiler-generated `._unsafe_rec` helpers, none reached by any endpoint, and the two `partial def` helpers of the `vintage` metaprogram (compiled to opaque constants); none of the 208 declarations generated by `vintage` is reached from `YangMills.jointExistence`.

Control: the same `#print axioms` machinery reports `[propext, sorryAx, Classical.choice, Quot.sound]` for the reference theorem in `Challenge` (`logs/30-spec-probes.log`), so a placeholder would have been detected.

Independent kernel replay (`review/lean/OwnReplay.lean`, log `logs/33-own-replay.log`): collects every project declaration reachable from `YangMills.jointExistence` and `YangMills.su2Theory`, imports a base environment made only of the non-project modules (Lean core, Batteries, Mathlib, …), checks that every external reference exists there, and replays the collected declarations with `Lean.Environment.replay`, then compares the replayed endpoint terms with the submitted ones. The kernel accepted all 93,999 declarations (93,969 reachable from the public theorem plus 30 more for the SU(2) corollary) on top of 10,910 external modules:

```
OWN_REPLAY_START projectDecls=93999 externalRefs=14112 baseModules=10910
OWN_REPLAY_PASS projectDecls=93999 seconds=564
TIME wall=588.71 s maxrss=20995552 KB
END 2026-11-11T08:29:32+01:00 EXIT=0 WALL_SECONDS=589
```

### 3.2 Source scan for escape hatches

`review/scripts/lean_scan.py` strips nested block comments, line comments and string contents from all 9,477 tracked `.lean` files and then matches tokens; raw counts (comments included) are given for comparison. Full hit lists: `review/work/scan/*.txt`; log `logs/10-escape-hatch-scan.log`.

| Pattern | Code hits | Raw | Significant hits |
|---|---|---|---|
| `sorry` | 1 | 1 | `Challenge.lean:6` (the reference placeholder) |
| `sorryAx` | 1 | 1 | `verification/Inventory.lean:16`, a name in the inventory checker |
| `admit` | 4 | 15 | all four are structure field names (e.g. `YM/RG08/Mason/Faith.lean:13: admit : P x m`); no `admit` tactic |
| `axiom` declarations | 0 | 0 | the word `axiom` occurs 13 times, all inside comments |
| `native_decide`, `decide +native`, `Lean.ofReduceBool/ofReduceNat`, `Lean.trustCompiler` | 0 | 0 | — |
| `unsafe` | 0 | 2 (comments) | — |
| `implemented_by`, `extern`, `@[csimp]`, `@[export]` | 0 | 0 | — |
| `opaque` | 0 | 19 (comments) | — |
| `partial` | 2 | 78 | `YM/UVExtension/Orchard/Barrel.lean:36,43`, helpers of the `vintage` metaprogram (below) |
| `set_option debug.*` | 0 | 0 | no `debug.skipKernelTC` or similar |
| other `set_option` | 14,255 | | `autoImplicit` 9,426; `quotPrecheck false` 1,377; `maxHeartbeats` 946; linter options; `warningAsError false` 596; `backward.isDefEq.respectTransparency false` 64; `backward.privateInPublic true` 1 (`YM/OPE/Levy/Panel.lean:20`); `backward.defeqAttrib.useBackward true` 1 (`YM/Next/STATIONARY/OneLoop/WilsonVertices.lean:15`). All are elaboration/linter options; none disables kernel checking. |
| `elab` | 1 | 1 | `YM/UVExtension/Orchard/Barrel.lean:66` — `elab "vintage" i:ident : command` |
| `macro` | 1 | 2 | `YM/Examples/SU2.lean:37` — `local macro "entry" : tactic` (a local `simp` bundle) |
| `syntax`, `declare_syntax_cat` | 0 | 0 | no keyword or `theorem` overrides |
| `initialize` | 1 | 2 | `Barrel.lean:42` — `initialize registerTraceClass` for the trace class `aging` |
| `run_cmd` / `#eval` | 7 | 7 | only in `Verify.lean`, `VerifyJoint.lean`, `verification/{CompactCheck,Comparator,Inventory,Usage}.lean` |
| `import Lean*` | 21 | 21 | verification files and `Barrel.lean`; the rest are `Mathlib.Tactic*` imports |
| file/process I/O (`IO.FS`, `IO.Process`, `System.FilePath`, `IO.println`) | — | — | only `Verify.lean`, `VerifyJoint.lean`, `verification/Inventory.lean`, `verification/Usage.lean` |
| global notation | 1 | | `infixl:70 " ⌾ "` (`YM/RG08/Billet/Fable.lean:12`), a new symbol |
| `local notation` | 19,470 in 2,507 files | | file-local abbreviations for local terms (`local notation "L" => …`); 58 files bind the letter `π` locally (e.g. `YM/FullVolume/Florid/Gild.lean:36: local notation "π"=> Lyre.spicesF …`). File-local notation cannot reach the public files, which import only Mathlib. |
| `attribute [...]` | 151 | | simp/instance attributes; no `register_*_attr` |
| `instance (priority := …)` | 1 | | `YM/Extra/ITERATION_NO_LOSS/Sums.lean:16`, a `Nonempty` instance |
| declarations in Mathlib namespaces | 2 | | `_root_.Filter.Tendsto.matrix_product`, `_root_.Filter.Tendsto.matrix_mul` (`YM/FullVolume/Train/{Flour,Tugs}.lean`), new lemma names |
| redefinitions of standard names | 0 at root | | `abbrev Matrix …` inside `YM.Climb`/`YM.Dash` namespaces (`YM/Climb/Cells.lean:17`, `YM/Dash/Scope.lean:122`); `YangMills.HilbertSpace` is the public spec's own bundled structure. A clash with an existing constant would be an import error. |

**The one metaprogram, `vintage`** (`YM/UVExtension/Orchard/Barrel.lean`, 71 lines). It copies the type and proof term of a named `YM` theorem or definition, renames constants to `Vintage.*` variants where such variants exist, and submits the result with `Lean.addDecl` (`Barrel.lean:55`), which sends it to the kernel; it refuses unsafe definitions (`Barrel.lean:63`). It is invoked 23 times in 6 files under `YM/UVExtension/Orchard/` (`Apple`, `Muesli`, `Pours`, `Shears`, `Tarts`, `Vanilla`). It cannot bypass the kernel, and my axiom audit and the replays cover anything it produces. My inventory (§3.1) finds 208 generated `Vintage.*` declarations; none is reachable from `YangMills.jointExistence`.

The README's admission is accurate: the only placeholder in the source is `Challenge.lean:6`, and `Challenge` lies outside the import closure of `Solution` (the import graph puts it among the 10 tracked modules outside that closure).


## 4. Statement fidelity (task 3)

### 4.1 What `YangMills.JointExistence` asserts, in plain mathematics

Source: `ChallengeSpec.lean:186-188`, unfolding `PublicWilson.lean` and `PublicTheory.lean`.

```lean
-- ChallengeSpec.lean:186
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q)
```

**Gauge group.** A `GaugeGroup` (`PublicTheory.lean:25-33`) is an integer n, a closed subgroup G ⊂ U(n+1), and a real subspace 𝔤 ⊂ M_{n+1}(ℂ) with X ∈ 𝔤 ⇔ e^{tX} ∈ G for all t ∈ ℝ. The last field forces 𝔤 to be the Lie algebra of G. `IsSimple` (`PublicTheory.lean:39-45`) says 𝔤 has two non-commuting elements and its only real ideals are 0 and 𝔤. This covers every compact group with simple Lie algebra in a faithful unitary representation, including disconnected ones (for example O(3)).

**Quantifiers.** For every such G:

∃ a Wilson family C = (L_p, D_N, β_{N,p}, h, 𝒯, I) (`PublicWilson.lean:35-46`) consisting of strictly increasing physical periods L_p ∈ ℕ₊, strictly increasing inverse spacings D_N ∈ ℕ₊ (mesh a_N = 1/D_N), real couplings β_{N,p}, a Haar probability measure h on G, an arbitrary type 𝒯 of tokens, and insertions I_{N,p}(v, x; U) ∈ ℂ for v ∈ 𝒯, x in the torus Λ_{N,p} = (ℤ/L_pD_N ℤ)⁴ and link configurations U,

such that (`WilsonRegularity`, `ChallengeSpec.lean:12-22`)

* (R1) ∃ b* > 0 with sup_p |β_{N,p} / log D_N − b*| → 0 as N → ∞;
* (R2) every I_{N,p}(v, x; ·) is continuous;
* (R3) every I_{N,p}(v, x; ·) is invariant under lattice gauge transformations U_{y,μ} ↦ t(y) U_{y,μ} t(y+e_μ)⁻¹;
* (R4) every token v has a finite stencil S_v ⊂ ℤ⁴, independent of N, p, x, such that I_{N,p}(v, x; U) depends only on links with both ends in x + S_v;

and for every strictly increasing p: ℕ → ℕ there exist a strictly increasing q: ℕ → ℕ and a hierarchy T with `Properties (p ∘ q)`.

The finite-volume measure is the Wilson measure (`PublicWilson.lean:25-33`):

  dμ_{N,p}(U) = Z⁻¹ exp(−β_{N,p} Σ_{x∈Λ, μ<ν} [1 − Re tr U_{x,μν}/(n+1)]) Π_links dh(U_ℓ).

A hierarchy T (`ChallengeSpec.lean:24-48`) bundles: a complex Hilbert space H, a complex vector space V of field labels and Wightman data on them (domain D, vacuum Ω, fields φ: V × 𝒮(ℝ⁴) → End(D), a conjugate-linear label adjoint, translations, an energy–momentum projection-valued measure, a Poincaré action); finite-dimensional normed spaces F_d, d ∈ ℕ ("fields of degree d") with injective linear maps ι_d: F_d → V; a map π: 𝒯 → ⊔_d F_d; a compact metric space X of "characters" (phases) with a Borel measure ν and a selected point ξ*; Euclidean correlations S^s(a_1…a_n; x_1…x_n) ∈ ℂ for s ∈ {mix} ⊔ X (Lean `none` / `some ξ`); an analytic-continuation function F(a; z, x⃗) of complex times z and real spatial points x⃗; OPE data (finite channel sets per degree, actor fields, coefficient functions); and one element Θ ∈ F_4 (`centeredTrace`).

`Properties` (`ChallengeSpec.lean:177-181`) has four conjuncts.

**(P1) Wilson origin** (`PublicWilson.lean:85-90`). For every n, tokens v_1…v_n and every smooth compactly supported test function t on the separated set {x ∈ (ℝ⁴)ⁿ : x_i ≠ x_j}: (a) supp t lies inside the box (−L/2, L/2)^{4n} for all large volume indices along p∘q; (b) there are numbers row_p such that, for every p whose box contains supp t,

  a_N^{4n} Σ_{x ∈ Λ_{N,p}^n} t(a_N x) E_{μ_{N,p}}[Π_i I_{N,p}(v_i, x_i; U)] → row_p as N → ∞ (along all N),

and (c) row_{p(q(k))} → ∫ t(x) S^mix(π v; x) dx as k → ∞.

**(P2) Reconstruction** (`ChallengeSpec.lean:117-143`).
* The Wightman data satisfy W0–W3 (`PublicTheory.lean:270-319`, details in §4.4).
* Faithfulness: every nonzero label has a nonzero smeared field; ι_d injective; ι jointly onto V; π onto ⊔_d F_d; some field acts as a nonzero operator.
* ν is a probability measure charging every nonempty open set.
* For every s: S^s is symmetric under simultaneous permutation of labels and points, and C^∞ on separated configurations; ξ ↦ S^ξ(a; x) is continuous.
* Mixture: S^mix(a; x) = ∫_X S^ξ(a; x) dν(ξ) at separated x.
* Analyticity: z ↦ F(a; z, x⃗) is holomorphic on Im z_1 < … < Im z_n.
* Root: F(a; iτ, x⃗) = S^{ξ*}(a; (x⃗, τ)) whenever τ_1 < … < τ_n.
* Boundary: for h_1 < … < h_n and Schwartz tests f_i, ∫ F(a; t + i r h, x⃗) Π f_i(x_i) dx → ⟨Ω, φ(ι a_1, f_1)⋯φ(ι a_n, f_n) Ω⟩ as r ↓ 0.

**(P3) OPE** (`ChallengeSpec.lean:70-80`). For every finite cluster a of tags with total degree w and constants M ≥ 0, η, c, ε > 0, D ∈ ℕ: (i) |c(a, j, i; x, o)| ≤ r^{j−w−ε} for all small r, uniformly for |x_k − o| ≤ Mr, |x_k − x_l| ≥ ηr; (ii) for all small r, uniformly over such x, o, over spectators y with |y_l − o| ≥ c and |y_l − y_m| ≥ c, and over **all** s ∈ {mix} ⊔ X,

  |S^s(a(x) b(y)) − Σ_{j≤D} Σ_{i} c(a, j, i; x, o) S^s(O_{j,i}(o) b(y))| ≤ r^{D+1−w−ε}.

**(P4) Trace test** (`ChallengeSpec.lean:168-175`). ⟨Ω, φ(ιΘ, f) Ω⟩ = 0 for all f; 3 dim_ℝ 𝔤 / π⁴ > 0; with G_Θ(r) := S^{ξ*}(Θ, Θ; (0,0,0,−r/2), (0,0,0,r/2)),

  r⁸ log²(1/r) · G_Θ(r) → 3 dim_ℝ 𝔤 / π⁴ as r ↓ 0;

and for every finite list of coefficients c_k and finite families of "modes" (mass m ≥ 0, power E^q, continuous homogeneous numerator h(p)), G_Θ is not eventually equal (as r ↓ 0) to Σ_k c_k Π_m ∫_{ℝ³} E^q h(p) e^{−rE} / (2E) d³p, E = √(m² + |p|²).

### 4.2 Can the statement be satisfied trivially?

I checked the degenerate witnesses one at a time. Four findings are machine-checked probes written for this review: Probes A, B, D in `review/lean/SpecProbes.lean` (log `logs/30-spec-probes.log`) and Probe E in `review/lean/ZeroInsertionProbe.lean` (log `logs/34-zero-insertion-probe.log`). Both files import only the reference statement `Challenge` (Mathlib-only closure), and every probe depends only on `propext`, `Classical.choice`, `Quot.sound`.

| Degenerate witness | Status in the public statement | Evidence |
|---|---|---|
| H one-dimensional, all fields zero | Excluded. P4 gives a centered field Θ with a nonzero two-point function, so φ(Θ,f)Ω ≠ 0 for some f and dim H ≥ 2. The clause `acts` alone would be met by the identity field, which is how the bridge proves it (`HierarchyBridge.lean:85-88`). | `ChallengeSpec.lean:121, 168-175` |
| Unsatisfiable hypothesis (no simple g) | Excluded. SU(2) is shown simple (`YangMills.su2Simple`, `ConcreteSU2.lean:12`; SU(2) defined as det = 1 in U(2), `YM/Next/FOUNDATIONS/SU2.lean:36-46`). | own `#print axioms` (§3) |
| Free fields / finite Wick polynomials of free fields with finitely many masses | Excluded for the Θ two-point function by `excludes`; it follows from the r⁻⁸ log⁻² law because every finite Wick profile has an expansion Σ a r^α (log r)^k + O(1) with k ≥ 0. | `ChallengeSpec.lean:175`, `TraceBridge.lean:41-44`, `YM/TraceExtension/Wick/Refute.lean:75-80` |
| Generalized free field (continuous Källén–Lehmann weight tuned to r⁻⁸ log⁻²) | Allowed by P2–P4. The code itself says so. | `YM/TraceExtension/Wick/Refute.lean:4-8`: "No claim against a continuous-mass generalized free field."; README.md:26 |
| Lattice insertions that ignore the gauge field | WilsonRegularity alone allows them (Probe B: constant insertions satisfy it). The full statement excludes the all-zero choice (Probe E: no hierarchy over a zero-insertion family satisfies `Properties`). Other gauge-blind choices are excluded by the argument below, whose first step is Probe D. | Probe B `ReviewProbe.regular_constInsertions`; Probe D `ReviewProbe.empty_cluster`; Probe E `ReviewProbeE.no_hierarchy_of_zero_insertions` |
| Coefficient 3 dim 𝔤/π⁴ | Carries no information inside the public statement: Θ is an arbitrary element of F_4, so rescaling Θ by λ rescales the limit by λ². `amplitudePositive` is a fact about g alone (machine-checked: Probe A). | Probe A `ReviewProbe.amplitude_positive_of_simple` |
| Slope b* = 2b₀ = 11C_A/(24π²) | The public statement only asks for some b* > 0; the value 2b₀ appears in the bridge proof. | `ChallengeSpec.lean:13`; `HierarchyBridge.lean:18` |

The two lattice-side probes, verbatim statements:

```lean
-- review/lean/SpecProbes.lean (Probe B): gauge-blind insertions pass WilsonRegularity
theorem regular_constInsertions {g : GaugeGroup} (C : WilsonFamily g) (hC : WilsonRegularity C)
    (κ : C.Token → ℂ) : WilsonRegularity (constInsertions C κ)
-- review/lean/ZeroInsertionProbe.lean (Probe E): ... but zero insertions cannot satisfy Properties
theorem no_hierarchy_of_zero_insertions (C : WilsonFamily g)
    (hz : ∀ N p v x U, C.insertion N p v x U = 0) {order : ℕ → ℕ} (T : Hierarchy C)
    (hT : T.Properties order) : False
```

**The OPE ties the lattice limit to the selected phase.** The natural "cheap" witness keeps the Wilson measure but uses gauge-blind insertions, so that S^mix is explicit, and puts all the physics into a selected phase built from some Wightman model. This fails because (P3)(ii) quantifies over every s, including s = mix, with one coefficient system:

1. Empty cluster (I = J = ∅, D = 0): the bound r^{1−ε} tends to 0 while the left side does not depend on r, so S^s(∅) = Σ_i c(∅,0,i;o) S^s(O_{0,i}(o)) exactly, for every s and o. This step is machine-checked (Probe D, `ReviewProbe.empty_cluster`). P1 at n = 0 gives S^mix(∅) = 1 (the Wilson measure is a probability measure); `root` + `boundary` at n = 0 give S^{ξ*}(∅) = ⟨Ω,Ω⟩ = 1. With zero insertions all one-point functions of S^mix vanish, contradiction. So the token of some degree-0 field must have a nonzero lattice limit.
2. Cluster (Θ,Θ) at timePair r with o = 0, D = 0: |S^s(ΘΘ) − Σ_i c((Θ,Θ),0,i;x,0) S^s(O_{0,i}(0))| ≤ r^{−7−ε} for s = mix and s = ξ*.
3. If F_0 is one-dimensional, items 1–2 give |S^mix(ΘΘ)(timePair r) − G_Θ(r)| ≤ 2r^{−7−ε}, so the lattice limit of the token representing Θ obeys the same law r⁸ log²(1/r) S^mix(ΘΘ) → 3 dim 𝔤/π⁴.
4. F_0 is one-dimensional in any witness: in the selected Wightman theory a degree-0 field χ with ⟨χ⟩ = 0 has a two-point function bounded by C r^{−ε} (OPE coefficient bound with w = 0), while a nonzero Wightman field in 4D has a two-point function at least ~ c/r² at short distance (Källén–Lehmann positivity); hence χΩ = 0, χ = 0 by the separating property of the vacuum, and faithfulness plus injectivity of ι_0 leave dim F_0 ≤ 1.

Item 1 is formal (Probe D). For zero insertions the whole contradiction is formal (Probe E): `wilsonLaw` is a probability measure (`ReviewProbeE.wilsonLaw_isProbability`), so the lattice zero-point function is nonzero (`zero_point_ne`); every lattice one-point function vanishes (`one_point_zero`, via the fundamental lemma of the calculus of variations and continuity from `smooth`); Probe D at s = none then equates that nonzero zero-point function with a sum of vanishing terms. For general gauge-blind or otherwise trivial insertions, items 2–3 are short consequences of the Lean definitions that I checked by hand; item 4 is a standard Wightman-theory argument that I did not formalize. For the actual construction the committee proved, by a different route (reflection positivity in every phase, continuity in the character, full support), that the mixed lattice-limit Θ two-point function is nonzero at some separation (`checks/TwoPointPhysicalObservable.lean:81-127`), which corroborates item 3. Conclusion: any witness of `JointExistence` must contain local, gauge-invariant lattice observables in the genuine Wilson measure with log-running β whose ordered continuum limit has a two-point function with the asymptotic-freedom law r⁻⁸/log²(1/r). I see no way to produce that without controlling the continuum limit of 4D lattice Yang–Mills. I did not prove that every witness must be Yang–Mills; the public statement leaves the identity of the observables, the slope value and the normalization of Θ open (next subsection).

### 4.3 How the continuum object is tied to Wilson lattice gauge theory

What the public statement pins down:

* The finite-volume measure is the standard Wilson action with product Haar measure on the periodic 4D torus, one plaquette per positively oriented face, β multiplying Σ(1 − Re tr U_□/(n+1)) (`PublicWilson.lean:20-33`). `haar` must be a Haar probability measure (`PublicWilson.lean:41-43`), which on a compact group is unique.
* β_{N,p}/log(1/a_N) → b* > 0 uniformly in p (`ChallengeSpec.lean:13-14`). In the construction this is an input property of the chosen RG trajectory: `YM.Pert.Asymptotics.zeroUp_bound` derives it from `hc.wilson.running`, a field of `C.Makes` (`YM/Pert/Asymptotics/RawAxis.lean:15-17`), with b* = 2b₀, b₀ = 11 C_A/(48π²) (`RawAxis.lean:13`, `HierarchyBridge.lean:18`).
* The mesh limit is taken along the full sequence N → ∞ at every fixed volume that contains the test support, then the volume limit along the extracted subsequence (`PublicWilson.lean:83-90`).
* S^mix is the barycenter of the phases (`ChallengeSpec.lean:133-134`) and shares OPE coefficients with every phase (§4.2).

What it leaves open:

* The insertions are arbitrary local, gauge-invariant, continuous functions with N- and p-dependent coefficients (`ChallengeSpec.lean:15-22`); nothing says they are renormalized curvature polynomials. That identification lives in the detailed theorem through `C.Makes.sections`, whose field `projects` matches the Taylor expansion of each lattice polynomial on parallel transports of polynomial connections with the classical gauge-invariant label (`YM/Source/Local.lean:85-89, 140-147`; `YM/Source/Construction.lean:44-62`).
* The tokens are an arbitrary type; the field spaces F_d are abstract; "degree" is just the index d.
* The value of b*, the spacing sequence (a_N is chosen by the construction; no universality), and the normalization of Θ.
* No Wilson loops, no gauge-variant fields, no statement about S^mix beyond the phase average and the OPE.

The committee reached the same conclusion about the public target: "OpenAI subsequently informed us that its original public Comparator target YangMills.jointExistence omitted some of the connections to the lattice construction established by its proof" (assessment-1.pdf, p. 14, §9). They base their acceptance on a stronger combined target that retains `C.Makes` and `Spec.Final` (`YM/submissions/openai-20261028/checks/AcceptanceSpec.lean:34-176`).

Assessment: the public link is strong enough to force genuine continuum control of 4D Wilson LGT (§4.2) and too weak by itself to identify the field content with Yang–Mills. The detailed theorem `YangMills.constructed` supplies the identification, using internal definitions (`YM.Family`, `YM.Table`, `YM.Spec.Final`, ~1M lines) that a reader has to trust or audit.

### 4.4 Wightman axioms as formalized (selected phase ξ* only)

| Axiom | Lean | Faithfulness notes |
|---|---|---|
| Hilbert space | `HilbertSpace` (`PublicTheory.lean:79-83`): complete complex inner-product space | The definition omits separability. |
| W1 domain, temperedness, cyclicity | `DomainAxioms` (`PublicTheory.lean:127-133`): ‖Ω‖ = 1, D dense, D = span of all field words on Ω, f ↦ φ(v,f)ψ continuous from 𝒮(ℝ⁴) to H | Strong form of cyclicity (D equals the polynomial domain). |
| W1 adjoint | `AdjointAxiom` (`PublicTheory.lean:136-141`): ⟨φ(v,f)ψ,χ⟩ = ⟨ψ, φ(v*, f̄)χ⟩ | Standard. |
| W0 spectrum | `W0` (`PublicTheory.lean:270-278`): projection-valued E on ℝ⁴ with ⟨ψ,U(a)ψ⟩ = ∫ e^{i⟨p,a⟩} dμ_ψ(p) and E(V̄₊ᶜ) = 0, V̄₊ = {‖p_space‖ ≤ p_time} | Euclidean pairing ⟨p,a⟩ flips the sign of spatial momentum relative to the Minkowski convention; V̄₊ is invariant under that flip, so the spectrum condition is the standard one. Sign of time component is consistent with analyticity in Im z₁ < … < Im z_n. |
| W0 vacuum uniqueness | `uniqueVacuum` (`PublicTheory.lean:276-278`): translation-invariant vectors are multiples of Ω | Holds for the selected phase only. |
| W2 covariance | `PoincareAction` + `W2` (`PublicTheory.lean:209-307`): unitary strongly continuous action of a group homeomorphic to SO⁺(1,3) ⋉ ℝ⁴ with the affine composition law; fields transform with f ↦ f(Λ⁻¹(x−a)) and a label representation ρ(g) | Proper orthochronous Poincaré group, without the double cover (adequate for gauge-invariant bosonic fields). ρ must be a group representation on V; the definition places no finite-dimensionality, continuity or Λ-only condition on it (the construction's ρ depends only on Λ, `PublicView.lean:56-57`). |
| W3 locality | `LocalCommutativity` (`PublicTheory.lean:149-156`): commutation when every point of supp f minus every point of supp g is spacelike | Bosonic commutation for all label pairs. |
| Dimension | `Axis := Fin 4`, time = last coordinate (`PublicTheory.lean:51-57`) | 4D. |
| Gauge group | closed subgroups of U(n+1) with simple real Lie algebra | Matches "any compact simple gauge group". |

OS side: the public statement contains no Osterwalder–Schrader axioms as such. It asserts permutation symmetry and smoothness of all phases and the mixture, holomorphic continuation of the selected phase in the time variables, equality with the Euclidean correlations at ordered imaginary times, and Wightman boundary values on product tests. Reflection positivity, Euclidean covariance and clustering enter the proof, and the committee proved the DMY OS axioms E0–E4 plus E0′ for the scalar centered-trace family of the selected phase (assessment §10; `checks/CompleteOS.lean`). Junk-value caveat: the `boundary` and `wilson` limits use Bochner integrals, which return 0 on non-integrable integrands; for `wilson` the integrand is integrable by `smooth`, and for `boundary` a non-integrable continuation would force the corresponding Wightman function to vanish, so this caveat cannot manufacture a false claim of a nonzero moment.

### 4.5 The non-freeness test

What is proved (public statement): a degree-4 field Θ with zero vacuum expectation whose Euclidean two-point function along the time axis satisfies r⁸ log²(1/r) G_Θ(r) → 3 dim_ℝ 𝔤/π⁴, and G_Θ is not eventually equal to any finite combination of products of free mass-shell kernels. The coefficient matches the leading perturbative prediction. My own check: with canonically normalized fields, ⟨F^a_{μν}F^a_{μν}(x) F^b_{ρσ}F^b_{ρσ}(0)⟩_free = 48 dim 𝔤/(π⁴|x|⁸) (from ⟨F_{μν}F_{ρσ}⟩ = (I_{μρ}I_{νσ} − I_{μσ}I_{νρ})/(π²x⁴) and Σ(…)² = 24), and Θ = (β(g)/2g)F² with β(g)/(2g) ≈ −b₀g²/2 ≈ −1/(4 log(1/|x|)) at one loop, so ⟨ΘΘ⟩ ≈ (48/16) dim 𝔤/(π⁴x⁸log²(1/|x|)) = 3 dim 𝔤/(π⁴x⁸log²); b₀ cancels. The committee's worked example does the same computation (`docs/examples/LeadingTrace-20261028.lean:162-233`) and notes that the check "does not independently test the factor 11 C_g/(48π²)". The detailed theorem identifies Θ with the centered trace of the Ward-normalized stress tensor (`YM/Nonperturbative/HeadlineSpec.lean:87-91`) and adds exclusions against Wick-polynomial Wightman two-point functions and Maxwell Fock realizations (`HeadlineSpec.lean:96-120`).

Strength: the inverse-square logarithm is the fingerprint of logarithmic running, so the test rules out every free theory with finitely many particle species and polynomial composites, which is a real non-triviality statement for a lattice-derived object.

What it leaves open: (i) generalized free fields with a continuous spectral weight ρ(s) ~ s²/log²s reproduce the same two-point law (the submission says so, `Refute.lean:4-8`); (ii) no connected 3- or 4-point function is shown nonzero, so Gaussianity of the selected phase remains open; (iii) in the public statement the coefficient depends on an unfixed normalization of Θ.

*Editor's note on (ii).* Item (ii) holds for the public statement. The detailed theorem and the group's combined target contain more: the translation Ward identity holds for every central field, every spectator list and every phase (`TranslationWard.translation`, `YM/submissions/openai-20261028/checks/AcceptanceSpec.lean:84-95`). Taking Θ as central field and as single spectator in the selected phase gives −Σ_a ∫ ∂_aχ(y) ⟨T_{ab}(y) Θ(x₀) Θ(x₁)⟩ dy = ∂_b ⟨Θ(x₀) Θ(x₁)⟩. The right side is nonzero at some configuration, because the trace law makes ⟨ΘΘ⟩ unbounded as the points approach. The constant ⟨T_{ab}⟩ integrates to zero against ∂χ and ⟨Θ⟩ = 0, so the truncated three-point function ⟨T; Θ; Θ⟩ is nonzero. The fields T and Θ therefore form a non-Gaussian family. This deduction combines two machine-checked clauses and is itself unformalized. A description of all fields as composites of Gaussian fields with a continuum of masses remains unexcluded, as the group says (assessment §7.3).

### 4.6 Spectrum and mass gap

**What the public theorem says.** Its spectral content is two clauses of W0 for the selected phase ξ*: the energy–momentum measure lives in the closed forward cone, and translation-invariant vectors are multiples of Ω.

```lean
-- PublicTheory.lean:270-278
structure W0 (theory : WightmanTheory H Labels) : Prop where
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state
```

Neither `JointExistence` nor `YangMills.constructed` contains any bound of the form σ(P²) ∩ (0, Δ²) = ∅ on Ω^⊥; a joint spectrum filling the closed forward cone, massless continuum included, is consistent with everything proved.

The detailed theorem does carry two quantitative infrared bounds, inside `EveryPhase.Completed` (`YM/EveryPhase/Extension.lean:51-70`, retained by `YangMills.constructed` through `Independent.Core.reconstruction`):

```lean
-- YM/EveryPhase/Extension.lean:57-63
  light (A : SumOfWords S) (h : finite A) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i u, u∈Ioc (0:ℝ) 1 →
    (νletter L i A).real (lowE u) ≤ M*u^2
  heat (A : SumOfWords S) (h : finite A) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ s ≥ (1:ℝ≥0),
    let x := stands (L.actors i).operators A
    let P := (L.actors i).momentum.region zeroE
    let r := inner ℂ x ((bHeat (L.J i) s-P) x)
    0 ≤ r ∧ r ≤ ↑(M*(s:ℝ)⁻¹^2)
```

with `lowE u := time ⁻¹' Ioc 0 u` (`YM/EveryPhase/Light.lean:132`) and `zeroE` the zero-energy set (`YM/EveryPhase/Projection.lean:30`). In words: for every finite word state, uniformly over phases, the spectral weight at energies in (0, u] is O(u²), and ⟨x, (e^{−sH} − P₀)x⟩ = O(s⁻²) for s ≥ 1. Both are power laws of the kind a massless spectrum produces (a free massless field gives exactly this u² behaviour); a gap Δ would make the first quantity vanish for u < Δ and the second decay like e^{−Δs}.

**Scope statements, verbatim.**

* README.md:26 — "The Wightman spectrum condition and uniqueness of the vacuum are the spectral conclusions in the public challenge. A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope."
* `YM/TraceExtension/Wick/Refute.lean:4-8` — "… No claim against a continuous-mass generalized free field."
* `YM/Fields/Spectrum.lean` module doc — "Uniqueness and forwardum for ANY subword covariant domain … No gap."
* assessment-1.pdf p. 1 — "It does not prove that the infinite-volume limit is unique or that there is a mass gap."; p. 3, §2 item 4 — "The construction provides no evidence for or against a mass gap in the theory."; p. 13, open question 3 — "Establish a uniform mass gap, giving exponential decay of corresponding correlations and a spectral gap in the Osterwalder–Schrader Hamiltonian."
* `YM/submissions/openai-20261028/docs/checks.md:21` — "The combined theorem does not assert uniqueness of the large-volume limit, a mass gap, confinement, or all-orders perturbative matching. … Neither a unique phase nor a unique thermodynamic limit is inferred."; same file, A5 row: the scale calibration and positive probe "do not establish a nonzero intrinsic continuum reference mass."
* `checks/AcceptanceSpec.lean:18-20` — "IR uniqueness, intrinsic scale setting, two-loop/all-orders matching, SD1--SD4, contact/dilation Ward identities and improvement uniqueness are not clauses."

**The "positive lattice probe" (`TwoPointScale.MassLimit`, committee check A5).** Definition (`checks/TwoPointPhysicalObservable.lean:133-137`):

```lean
def MassLimit : Prop :=
  ∃ (t : Test 2) (M : ℝ), 0 < M ∧
    (Order.mk Sequence.full o.per).limits (fun p => suitable C.S p t)
      (fun N p => NonzeroScale.massMagnitude 8
        (Order.smears C N p (Trace.unlabel (center F)) t)) M
```

with `massMagnitude D z = ‖z‖^(1/D)` (`checks/NonzeroPhysicalObservable.lean:19`). It says: there is one fixed separated two-point test t such that the eighth root of the smeared lattice ⟨ΘΘ⟩ correlation converges, full UV limit then the chosen IR subsequence, to a number M > 0 (assessment eq. (23)). The proof (`TwoPointPhysicalObservable.lean:44-127`) uses reflection positivity in every phase (each phase value is ≥ 0), continuity in the character, full support of ν and the barycenter identity to move strict positivity from the selected phase to the mixed lattice limit. M has mass dimension one only through the engineering grades 4 + 4 and the convention that t is a joint density; t, M and the centering depend on the witness F. The file states the limit of its meaning: "The physical interpretation as a mass uses dimension-four trace fields and a joint smearing density; no intrinsic scale or spectral gap is asserted" (lines 129-132); the worked example adds "It is also not a spectral mass, a mass gap, or a convergence rate" (`docs/examples/LatticeAndScale-20261028.lean:148`). A dimensionful nonzero correlation is evidence of a scale in the theory (dimensional transmutation); a mass gap needs decay of every connected correlation, or equivalently a spectral gap of the Hamiltonian, uniformly in the limit.

**The imported `lgt` strong-coupling files.** `provenance/lgt/LGT/MassGap/StrongCoupling.lean` and `YMMeasure.lean` are source snapshots of `mrdouglasny/lgt` at `b8793cc`. The committee's own record gives their scope: "Selected exact LGT declarations, with explicit original section context and Mathlib import; not a full build of lgt or its mass-gap results" (`evidence/historical/lgt-correspondence/provenance.json`, field `scope`). The check that uses lgt, `checks/LGTWilsonBridge.lean`, imports `checks/ImportedLGTData.lean`, which imports only Mathlib and re-states the lattice, Haar and `ymMeasure` definitions plus the Borel/topology instances on `GaugeConnection` (those instances sit in `StrongCoupling.lean:66-80`, which is why that file is snapshotted). No check imports `LGT.MassGap` (grep over `checks/` and `docs/`). The lgt mass-gap theorems themselves, `ym_mass_gap_strong_coupling` and `ym_mass_gap_exponential_decay` (`StrongCoupling.lean:1587, 2049`), assume `β < 1 / (4 * n * maxNeighbors d)`: they are strong-coupling statements about one finite lattice, the regime opposite to the continuum limit, where β_{N,p} ~ 2b₀ log(1/a_N) → ∞. They play no role in the October theorem or in the combined acceptance target.

**Phases and non-uniqueness.** The infinite-volume limit is subsequential: `∀ p, ∃ q` in `JointExistence`, compactness in assessment §5. Its correlations S^mix are decomposed as S^mix = ∫ S^ξ dν(ξ) over the Gelfand spectrum X of the commutative ground-state compression algebra (assessment §6.1). The public theorem reconstructs one phase ξ* with a unique vacuum; the detailed theorem reconstructs every phase. Clustering of S^mix, equality of phases, and independence of the limit from the subsequence are open (assessment §5, §6.2, §8 item 1). These facts bear on a mass gap in two ways. First, a gap statement needs a definite theory, and the theorem leaves open which subsequential limit and which phase one means. Second, the OS clustering that the committee verifies for the selected trace family (`checks/CompleteOS.lean`, E4) is qualitative: "Neither statement specifies an exponential rate, proves a mass gap, or makes the infrared extraction unique" (`docs/examples/OSAxioms-20261028.lean:131-132`). A mass gap corresponds to exponential clustering with a uniform rate, which nothing in either repository proves.

**Comparison with the Millennium problem.** The Clay statement (quoted from my knowledge of the official Clay description; no file in these repositories contains it): prove that for any compact simple gauge group G a non-trivial quantum Yang–Mills theory exists on ℝ⁴ *and* has a mass gap Δ > 0, existence including axiomatic properties at least as strong as Wightman/OS. The committee's paraphrase of the four Jaffe–Witten requirements (assessment p. 3, §1): (1) a nontrivial theory satisfying QFT axioms; (2) Yang–Mills local fields; (3) the predicted short-distance behaviour (asymptotic freedom, stress tensor, OPE); (4) σ(H) ⊂ {0} ∪ [Δ, ∞), Δ > 0.

| Requirement | Public theorem `jointExistence` | Detailed theorem and committee checks |
|---|---|---|
| (1) QFT axioms, any compact simple G, non-trivial | Wightman W0–W3 for one selected phase ξ* of one subsequential infinite-volume limit; non-trivial through the Θ two-point law; non-Gaussianity unproved; uniqueness of S^mix open | every phase reconstructs (`Construction.lean:27`); DMY OS axioms E0–E4, E0′ for the scalar trace family (A1) |
| (2) Yang–Mills local fields | absent (abstract F_d, arbitrary local insertions) | `C.Makes.sections` Taylor matching; operator content ≅ free Maxwell shell sector (A2) |
| (3) AF, stress tensor, OPE | log-running β (slope unspecified), r⁻⁸log⁻² trace law, OPE with phase-independent coefficients | slope 2b₀; log(1/r) g_W(r)² → 1/(2b₀) (assessment Thm 7.2); Ward-normalized stress tensor (A6); leading law only: the group's two-loop criterion `KernelUVAsymptoticallyFree` (`provenance/af/YangMills/Core/ShortDistance.lean:113`) lies outside the claims; no perturbative OPE matching |
| (4) mass gap Δ > 0 | not addressed | not addressed |

The submission addresses a weakened form of the existence half and none of the mass-gap half. The weakening: existence is subsequential in the volume, the Wightman theory is one component of a phase decomposition, and uniqueness and universality are open. `docs/checks.md` also notes that a later OpenAI submission of 4 November 2026, with additional perturbative-matching claims, is outside this package ("The November submission and its additional perturbative matching claims are also outside its scope"); the YM README lists it as "work in progress". This review did not examine it.


## 5. Proof architecture (task 4)

Method: import graph of all 9,477 tracked files (`review/scripts/import_graph.py`, log `logs/11-import-graph.log`); declaration-level reachability from the endpoints and directory-level dependency edges computed inside Lean on the built environment (`review/lean/OwnAudit.lean`, `review/lean/ArchMap.lean`); module docstrings; and reading the top of the call chain. Declaration and file names are largely non-descriptive (`Jewel`, `Campaign`, `Pillars`, `Bandage`, `Muse.Plato`, `Luna.Tableau`, 100 subdirectories of `YM/RG08` named `Apex`, `April`, `Arc`, …), so the stage boundaries below are my reading, checked against the assessment's description of the proof.

Import graph facts: `Challenge` has 4 project modules in its closure (itself, `ChallengeSpec`, `PublicWilson`, `PublicTheory`) and only Mathlib outside. `Solution` has 9,467 project modules (9,456 under `YM/`, 996,488 lines) in its closure; only 10 tracked modules lie outside it (`Challenge`, `ConcreteSU2`, `Verify`, `VerifyJoint`, `YM`, `YM.Examples.SU2`, `verification.*`). The longest import chain ending at `Solution` has 518 modules (the shortest import path from `Solution` to any module is at most 103 steps).

### 5.1 Top of the proof, as code

`review/lean/ArchMap.lean` walks the proof term of `YangMills.constructed` breadth-first through theorem dependencies and prints each node once with the module and line that Lean records for it (`work/audit/proof-tree.txt`, 509 nodes to depth 5). The spine, verbatim positions:

```
depth 0  YangMills.constructed                                   Construction:15
depth 1  YM.Nonperturbative.existence                            YM/Nonperturbative/Headlines:19
         bridges: YangMills.regular (HierarchyBridge:16), wilsonLimit (:44), publicOPE (:68),
                  publicReconstruction (:79), publicTrace (TraceBridge:35),
                  contactDistribution (ContactBridge:14), view_axioms (PublicView:102)
depth 2  YM.Nonperturbative.continuum_with_position_tests        YM/Nonperturbative/Continuum:28
depth 3  YM.Independent.constructionRun                          YM/Independent/ConstructionRun:14
         YM.R2IGoals.fromFunded                                  YM/R2I/Campaign/Accepted:150
         YM.Nonperturbative.contacts_on                          YM/Nonperturbative/Continuum:14
         YM.Pert.Position.four_on                                YM/Pert/Position/Four:49
depth 4  …RG05Joint.selectRunWithTreasuryPeriod_preselected_quote_orders_postnumeric
                                                                 YM/Integration/NativePreselectedPostnumericPeriodRun:99
         YM.PhysicalNext.Repeat.Legato.Run.extractible17         YM/RG17/Joint:61
         YM.PertExtension.Running.extraction                     YM/PertExtension/Running:40
         YM.EveryPhase.all_characters                            YM/EveryPhase/Extension:75
         YM.OPE.Orbits.produce                                   YM/OPE/Orbits/Kernel:67
         YM.OPE.Nesting.uniform                                  YM/OPE/Nesting/Endpoint:31
         YM.Trace.Target.assembled                               YM/TraceExtension/Endpoint:138
depth 5  YM.FullVolume.Final.jewelOf17                           YM/RG17/Joint:102
         YM.Trace.Target.Result.{law,shortDistance,exclude,…}    YM/TraceExtension/Endpoint:102-120
         YM.Trace.Target.Exclusion.{wick_polynomial,noMaxwellFock} YM/TraceExtension/Endpoint:87, 91
```

Read as mathematics: `constructionRun` selects one Wilson family and RG trajectory with all multiscale estimates "paid" (`Funded`); `fromFunded` then, for every requested extraction order, extracts the running-coupling limits (`PertExtension.Running.extraction`), builds the continuum table and the `Spec.Final` witness (`Run.extractible17`, which also assembles the Ward-identity work packages `Work.A01`–`A17` at `YM/RG17/Joint.lean:83-85`), proves every-phase reconstruction (`all_characters`), the OPE reader and nested OPE (`OPE.Orbits.produce`, `OPE.Nesting.uniform`) and the trace results (`Trace.Target.assembled`); `jewelOf17` supplies the full-volume package (uniform full-mesh convergence `PositionsUV`, unique tuned bare couplings, sampler of `Final` witnesses). The bridges then translate this into the public vocabulary.

### 5.2 Stage map

Sizes are modules and lines inside the import closure of `Solution`, grouped by top-level `YM/` directory (`review/scripts/stage_sizes.py`); "reached" counts are declarations reachable from `YangMills.jointExistence` (93,969 in total, §5.4). The directory-to-stage assignment is mine; directories cut across stage boundaries (the RG bucket imports the shared work packages 887 times, the limit stage imports RG modules 305 times), so treat the sizes as approximate.

| Stage | What it proves | Key declarations | Size | Technique |
|---|---|---|---|---|
| S0 public interface and bridges | Re-expresses the internal construction in the public vocabulary and proves the public theorem | `YangMills.jointExistence` (`Solution.lean:4`), `YangMills.constructed` (`Construction.lean:15`), `YM.Nonperturbative.existence` (`YM/Nonperturbative/Headlines.lean:19`); bridges `energy_eq`, `law_eq`, `moment_eq`, `smear_eq`, `fromWilson` (`WilsonBridge.lean:32-67`), `regular` (`HierarchyBridge.lean:16`), `view`, `view_axioms` (`PublicView.lean:30, 102`), `publicReconstruction`, `publicOPE` (`HierarchyBridge.lean:79, 68`), `publicTrace` (`TraceBridge.lean:35`), `contactDistribution` (`ContactBridge.lean:14`) | 20 modules, 1,996 lines; 766 decls, 362 reached | bookkeeping |
| S1 foundations | Compact matrix gauge groups, Lie algebra, Casimir C_A, slope 2b₀ = 11C_A/(24π²); lattice geometry and paths; the Wilson law and its symmetries; gauge-invariant labels (polynomials in radial jets with engineering grading); lattice representatives with Taylor matching (`Family`, `Makes`, `SectionData.Sound`); the abstract continuum `Table` | `YM.Gauge.slopeConstant` (`YM/Gauge/Colors.lean:184`), `YM.Family`, `YM.Family.Makes` (`YM/Source/Construction.lean:24, 44`), `YM.Source.SectionData.Sound` (`YM/Source/Local.lean:140`), `YM.Labels.read` (`YM/Labels/Polynomial.lean:35`) | 151 modules, 18,948 lines; 5,134 decls, 3,137 reached | definitions; classical lattice gauge theory |
| S2 multiscale RG (ultraviolet) | Exact multiscale representation of the Wilson measure: bare density at level N, one RG step per level down to unit spacing with coupling β̄, β following 2b₀ log(1/a) + const; bounds on all effective activities; tuning of the bare coupling | `YM.RG.History.Selected` (`YM/RG/History.lean:234`), `YM.RG.Calendar` and `Levels` (same file, small-field threshold, allowances, blocking-kernel penalty), `YM.Pert.Asymptotics.zeroUp_bound` (`YM/Pert/Asymptotics/RawAxis.lean:15`); subdirectories `Next/{SCHEDULE,FREE_KERNELS,FLUCTUATIONS,STATIONARY/OneLoop,RANK}`, `AnalyticBridge/{GAUSSIAN_FIELD_ALIGNMENT,RELATIVE_LOGDET_TRACE,LOCAL_GAUSSIAN_LAWS,COUPLING_BRANCH_TUNING}`, `AnalyticNext/{CONNECTED_ACTIVITY_BOUNDS,CUBIC_MATCH,QUARTIC_MATCH}`, `Push/{FREE_RESOLVENT,CUTOFF_PROJECTORS,LOOP_COEFFICIENT,BETA_TRANSPORT}`, `PhysicalNext/RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP`, `RG08` (100 subdirectories) | 6,882 modules, 754,590 lines; 180,196 decls, 60,889 reached | Bałaban-style block-spin RG: small/large-field splitting, polymer activities with Mayer-type expansions, Gaussian integration with covariance and log-det bounds, one-loop computation of the marginal flow, symmetric gauge fixing (assessment p. 6) |
| S2b run selection and assembly | Chooses one Wilson family (schedule, couplings, RG trajectory) with all estimates paid, then for each extraction order produces the table and the `Spec.Final` witness | `selectRunWithTreasuryPeriod_preselected_quote_orders_postnumeric` (`YM/Integration/NativePreselectedPostnumericPeriodRun.lean:99`), `YM.Independent.constructionRun` (`YM/Independent/ConstructionRun.lean:14`), `R2IGoals.fromFunded` (`YM/R2I/Campaign/Accepted.lean:150`), `Run.extractible17`, `FullVolume.Final.jewelOf17` (`YM/RG17/Joint.lean:61, 102`), `YM.Spec.Final` (`YM/Spec/Closed.lean:64`) | 63 modules, 7,064 lines; 1,209 decls, 308 reached | assembly |
| S3 limits | Full-mesh limit at fixed volume of every renormalized correlation (Cauchy in N), local bounds and equicontinuity uniform in the volume, subsequential infinite-volume limit | `YM.Extraction.Order.Ordered` (`YM/Extraction/Limits.lean:32`), `YM.FullVolume.Final.Jewel` (`YM/FullVolume/Finale/Program.lean:133`) incl. `fullMesh : PositionsUV`, `Spec.Seed` (`YM/Spec/Closed.lean:20`) | 692 modules, 59,099 lines; 24,604 decls, 7,685 reached | Arzelà–Ascoli and diagonal extraction; reflection positivity, chessboard estimates, transfer operators (assessment p. 7) |
| S4 OS structure and reconstruction | OS Hilbert spaces and heat semigroups; ground-state compression algebra; Gelfand-spectrum phase decomposition; analytic continuation; Wightman reconstruction of every phase; SNAG energy–momentum measure | `YM.EveryPhase.all_characters` (`YM/EveryPhase/Extension.lean:75`), `EveryPhase.Completed` (same file `:51`), `YM.OS.*`, `YM.Ground.*`, `YM.Boundary.Contour`, `YM.Fields.System` | 81 modules, 11,089 lines; 2,715 decls, 2,040 reached | reflection positivity, Gelfand + Riesz–Markov, OS reconstruction, SNAG theorem |
| W shared work packages | Numbered lemma packages used across stages: `Work.A*` Ward identities and rotations, `B*` OS and characters, `C*` analytic continuation and reconstruction (`C02` root, `C03`, `C26` faithfulness), `D*` extraction estimates, `E*`–`I*` kernel estimates; analysis utilities | `YM.Work.A01.answer` … `A17.answer` (used in `Run.extractible17`, `YM/RG17/Joint.lean:83-85`) | 204 modules, 33,244 lines; 4,154 decls, 3,574 reached | various |
| S5 stress tensor, Ward identities, trace | Conserved symmetric stress tensor unique up to normalization, translation Ward identity, restoration of rotation invariance, centered trace and its r⁻⁸log⁻² law, Wick and Maxwell-Fock exclusions | `YM.TraceExtension.center` (`YM/TraceExtension/WilsonTrace.lean:48`), `YM.TraceExtension.Wick.euclidean_excludes` (`YM/TraceExtension/Wick/Refute.lean:75`), `Headline.TraceExclusions` (`YM/Nonperturbative/HeadlineSpec.lean:84`) | 756 modules, 57,293 lines; 15,657 decls, 9,587 reached | Ward identities, flux decay with reflection positivity in several planes (assessment p. 9), Källén–Lehmann positivity |
| S6 OPE and contacts | Single-centre and nested OPE with remainder bounds common to all phases; contact extensions to coincident points | `YM.OPE.Orbits.produce` (`YM/OPE/Orbits/Kernel.lean:67`), `Headline.SeparatedOPE`, `NestedOPE` (`HeadlineSpec.lean:24, 128`), `YM.Nonperturbative.contacts_on` (`YM/Nonperturbative/Continuum.lean:14`) | 439 modules, 36,827 lines; 10,554 decls, 3,860 reached | OPE via orbit averaging and coefficient extraction from correlations |
| S7 perturbative comparison | Running coupling log(1/r) g_W(r)² → 1/(2b₀); scaling limit of stress-tensor correlations to dim 𝔤 free Maxwell fields along a sequence; position-space comparisons | `YM.Pert.Asymptotics.comparison` (`RawAxis.lean:36`), `YM.Pert.FirstExtension` (`YM/Pert/FirstTarget.lean:26`), `YM.Pert.Position.FourMeters` (`YM/Pert/Position/Four.lean:45`) | 179 modules, 16,338 lines; 5,302 decls, 2,527 reached | one-loop perturbation theory, free-field asymptotics |

### 5.3 What is new and what is known

My literature baseline (knowledge through mid-2026): Wilson's lattice action (1974); Osterwalder–Seiler reflection positivity for Wilson LGT (1978); OS axioms and reconstruction (1973/75); Bałaban's multiscale RG for 4D lattice YM (CMP 1983–89), which gives ultraviolet stability of effective actions on a finite torus without a continuum limit of correlation functions; Magnen–Rivasseau–Sénéor's finite-volume YM₄ with an infrared cutoff (1993); Federbush's phase-cell programme; complete constructions in 2D (Gross–King–Sengupta, Lévy, …) and partial 3D/stochastic-quantization results (Chandra–Chevyrev–Hairer–Shen and others). No construction of a 4D continuum Yang–Mills QFT satisfying Wightman or OS axioms existed. Perturbative facts: asymptotic freedom (1973), the trace anomaly Θ = (β/2g)F² (1977), the OPE (Wilson 1969; perturbatively convergent versions by Hollands–Kopper 2012 for φ⁴₄).

Formalizations of known theorems or techniques inside the submission (my classification from directory names, module docs and the assessment): Wilson measure and Haar integration; block-spin RG with small/large-field splitting, polymer activities and Mayer-type expansions, Gaussian integration and covariance/log-determinant bounds; reflection positivity, chessboard estimates, transfer operators; Arzelà–Ascoli compactness and diagonal extraction; Gelfand representation and Riesz–Markov for the phase decomposition; the SNAG theorem for the energy–momentum measure (`YM/SNAG`); its own OS reconstruction (`YM/Work/C*`, `YM/Boundary`, `YM/Fields`); Källén–Lehmann-type positivity arguments; Wick/free-field calculus for the exclusions.

Mathematically new if the formal proof is accepted, relative to that baseline: (1) convergence along the whole spacing sequence of renormalized correlations of all gauge-invariant local polynomial observables of 4D Wilson LGT at fixed volume, with asymptotic-freedom tuning of β (assessment Thm 4.1); (2) a subsequential infinite-volume limit with uniform local bounds (Thm 5.1); (3) a phase decomposition whose components reconstruct to Wightman QFTs with unique vacua (Thm 6.1); (4) restoration of full Euclidean, hence Poincaré, invariance through a Ward-normalized stress tensor; (5) the non-perturbative short-distance law r⁸log²(1/r)⟨ΘΘ⟩ → 3 dim 𝔤/π⁴ and the effective-coupling law log(1/r) g_W(r)² → 1/(2b₀); (6) a non-perturbative OPE with remainder bounds, common to all phases. The assessment calls the RG "following the general approach of Balaban but with many improvements such as a gauge fixing invariant under discrete lattice symmetries" (p. 6). Items (1)–(6) are claims whose formal proofs the kernel accepted; their mathematical meaning rests on the internal definitions discussed in §4 and on the committee's adapters.

### 5.4 The 150,151 declarations that the audited theorems do not reach

The README's figures ("The 17 audited theorems reach 100,168 of 250,319 imported project declarations. The tables flag the other 150,151", README.md:52) concern the declarations in the import closure of `ConcreteSU2` that no proof term or type of the 17 endpoint theorems refers to, transitively. I recomputed reachability inside Lean with my own traversal (types and values of every constant, plus inductive companions; `review/lean/OwnAudit.lean`, output `work/audit/declarations.tsv`):

| | Declarations | Reached from the 17 endpoints | Unreached |
|---|---|---|---|
| all project declarations (incl. generated) | 250,319 | 100,168 | 150,151 |
| source-level (heuristic: excludes `._…`, `match_`, `proof_`, equation lemmas, recursors, `brecOn`, `below`, `casesOn`, `noConfusion`, `injEq`, …) | 115,870 | 69,238 | 46,632 |
| theorems / definitions / inductives (all) | 135,798 / 101,848 / 4,176 | 74,036 / 21,292 / 2,308 | 61,762 / 80,556 / 1,868 |

From `YangMills.jointExistence` alone 93,969 declarations are reachable. These numbers reproduce the README's 100,168 and 150,151 exactly, with independent code. 2,944 of the 9,467 modules that contain declarations have no reached declaration at all (the shipped `usage.log` reports 2,946 of 9,469 modules, counting two declaration-free modules).

What the unreached material is, from that table: (1) superseded variants of pipeline stages kept in the tree: of the run-selection theorems only `RG05Joint.selectRunWithTreasuryPeriod_preselected_quote_orders_postnumeric` and its `_of_prediction` variant are reached, while `R2I.selectRun`, `ChronJoint.selectRun`, `ChronJoint.selectRunWithCustody`, `ChronJoint.selectRunWithTreasury` and `RG05Joint.selectRunWithTreasuryPeriod` are not; (2) whole sub-projects that never connect to the endpoints, by share of unreached declarations with non-internal names: `YM/Extension` 100 % (784), `YM/ProjectorNext` 99 %, `YM/Trace` 96 %, `YM/MultipleContact` 93 %, `YM/Further` 90 %, `YM/RG05Readout` 90 %, `YM/WilsonBulk` 89 %; the largest groups of modules with nothing reached are `YM/Push/LOOP_COEFFICIENT` (157 modules), `YM/Planned/PRIMARY_INTEGRAL_295` (85), `YM/AnalyticNext/QUARTIC_MATCH` (81), `YM/MultipleContact/Bunch` (72), `YM/Next/MULTISOURCE` (68), `YM/Further/CURVED_GAUSSIAN_JETS` (58), `YM/Extension/UV` (57), `YM/MultiNext/VACUUM_STABILITY` (51); (3) generated auxiliaries that no proof term names (4,000 of the 4,176 recursors, most equation lemmas and `match_` helpers) and the 208 `vintage` copies; (4) independent corollaries and alternative statements next to used lemmas. The directory names (`Planned`, `Further`, `Extra`, `…_MATCH`, `MULTISOURCE`) suggest exploratory or abandoned routes, which fits the committee's remark on code quality (assessment p. 15). None of this material can affect the validity of the endpoints, since the kernel replays cover exactly the reached part; it does inflate the code a reader must sift through.


## 6. The committee repository (task 5)

### 6.1 Is `YM/submissions/openai-20261028/submission` the same as the OpenAI repository?

Yes, byte for byte.

```
$ diff -r --exclude=.git --exclude=.lake OpenAI-YM-20261028 YM/submissions/openai-20261028/submission
(no output, exit 0)
$ git ls-files -s (mode, blob, path) of both trees, sorted and compared
GIT BLOB LISTS IDENTICAL (mode, blob sha, path) for 9508 files
$ sha256sum --quiet -c SOURCES.sha256     # in each tree, 9,507 entries
exit 0 (OpenAI clone)      exit 0 (committee copy)
```

One inconsistency inside the OpenAI distribution itself: `verification/verified-sources.sha256` and the `SOURCE_SHA256` line in `verification/joint-check.log` give `PublicTheory.lean` the hash `3940e8dd…`, while the shipped file hashes to `94111ad2…`, which matches `verification/challenge.sha256` and `SOURCES.sha256`. The shipped `joint-check.log` was therefore produced from a different `PublicTheory.lean` than the one distributed. The committee's 30 October Comparator run recorded `94111ad2…` (`evidence/historical/submission-comparator/source-snapshot-before.json`), and this review's own build and checks used the distributed file, so the discrepancy affects only the evidential value of OpenAI's shipped log.

### 6.2 What `checks/`, `verification/`, `docs/`, `evidence/` and `provenance/` contain

* `checks/` — 43 Lean modules (5,762 lines) importing the submission. `AcceptanceSpec.lean` defines `CombinedAcceptance g hg b`: one `Family` chosen before the extraction order, and for each order one refinement, one `Table` and one `Spec.Final` satisfying seven clauses: `LatticeAndScale` (the submitted finite law equals lgt's `ymMeasure` with β_lgt = β/(n+1); finite moments; full-UV ordered limit; public limit; reference spacing 1; common reference coupling; shared kinetic paths; insertion read-out; calibrated reset), `PhaseAndOS` (ν probability with full support; phase average equals the lattice table; DMY `OsterwalderSchraderAxioms 3` and `OSArityLinearGrowthCondition` for the selected centered trace; normalization, centering, integrability), `TranslationWard` (fixed sign and coefficient of the translation Ward identity, every phase), `OperatorContent` (label exhaustion, F_d ≅ free Maxwell shell sector in every phase, dense words, faithfulness), `LeadingTrace` (all-direction leading law with coefficient 3 dim 𝔤/π⁴ and the group predicate `KernelUVPowerLaw`), `TwoPointScale.MassLimit` (positive lattice probe, §4.6), and `SourceConclusions` (the submitted conclusions retained on the same witness). `CombinedAcceptance.lean` proves it by one call to `YangMills.constructed` plus adapters (`combined_acceptance`, lines 111-121). `OPESpec.lean`/`OPECheck.lean` restate the public OPE with explicit radius quantifiers and derive it from the submitted OPE (`from_source`), with phase-difference, channel-assembly and single-field lemmas. `CompleteOS.lean` packages the DMY OS axioms E0–E4 (+E0′) for the scalar centered-trace family of the selected phase on zero-diagonal Schwartz tests; the bridge concerns that scalar family only.
* `verification/` — Comparator references `AcceptanceChallenge.lean`, `OPEChallenge.lean`; configurations `submission.json` (identical to the submission's `comparator.json`), `acceptance.json`, `ope.json`; `tool-pins.json` (Comparator `d03acab` on Lean 4.34.0, lean4export `4e79152` on Lean 4.32.0, mode "upstream-development-launcher", `external_kernel: false`); four control projects (`accept`, `statement_mismatch`, `forbidden_axiom`, `definition_mismatch`).
* `docs/` — `checks.md` (scope table A1–A8 and explicit non-claims), `rerun.md`, seven commented Lean walkthroughs in `docs/examples/` (`OctoberChain.lean` plus one per A-topic).
* `evidence/` — `historical/` (29 Oct build, 30 Oct submission Comparator PASS, 3 Nov combined Comparator PASS, OPE build, OS/AF/lgt correspondences), `release-2026-11-05/` (package replay: build, review, tools, controls, OPE Comparator, all "passed"), `examples-2026-11-10/`, `documentation-2026-11-10/`. Every recorded path in these records lies under `/Users/oai/…` (706 occurrences; for example `"build_directory": "/Users/oai/Documents/Codex/2026-10-28/thre/work/ym-rebuild/source"` in `historical/build/environment.json`). The recorded builds and Comparator runs were therefore executed in an account named `oai` inside a Codex workspace; the assessment says OpenAI's Astra model assisted the review. I cannot tell from the files who operated that machine; the point matters for how independent the recorded evidence is, and this review's rerun is independent of it.
* `provenance/` — import hashes (`october-import.json`), upstream snapshots of DMY OSreconstruction (`osreconstruction/Specification.lean`), the group's `yang-mills` OS and analysis files, the group's AF specification (`af/YangMills/Core/ShortDistance.lean`, which also contains the stronger two-loop criterion `KernelUVAsymptoticallyFree`, which lies outside the checks' claims), and lgt (`lgt/LGT/…`, including `MassGap/StrongCoupling.lean` and `MassGap/YMMeasure.lean`; role discussed in §4.6).

### 6.3 Which committee stages I ran (`scripts/verify.py`, pointed at the single built tree)

All stages ran from `YM/submissions/openai-20261028/` with `--source /path/to/ym-release/OpenAI-YM-20261028`, so the one project build was reused (no second build of `submission/`). Results land in the git-ignored `runs/` directory; `git status` of YM stayed clean. I ran the three Comparator targets the runner knows, so the committee's two stronger endpoints were checked as well.

| Stage (command) | `runs/` record | `result.json` status | Notes |
|---|---|---|---|
| `integrity` (default source = the committee's `submission/`) | `20261111T043603.321651Z` | passed | 9,508 submitted files, 43 review modules and the packaged inputs match their recorded hashes; four OS declarations match the bundled DMY snapshot after the documented normalization |
| `integrity --source <OpenAI clone>` | `20261111T043606.055610Z` | passed | same checks against the OpenAI clone |
| `tools` | `20261111T045522.088007Z` | passed | cloned and built Comparator `d03acab` (93.5 s, Lean 4.34.0 from `review/elan-home`) and lean4export `4e79152` (17.1 s); binary sha256 `8efd5e15…` and `e5736998…` |
| `controls` | `20261111T060236.329911Z` | passed | `accept`: "Lean default kernel accepts the solution"; `statement_mismatch`: "Challenge and solution theorem statement do not match: 'comparatorSmoke'"; `forbidden_axiom`: "Illegal axiom detected: 'unapproved'"; `definition_mismatch`: "Const does not match between challenge and target 'reference'" |
| `comparator --target submission` | `20261111T072932.552598Z` | passed | controls repeated (all as expected), then `comparator-submission` exit 0 after 1,078 s: `lake build Solution` found everything up to date ("Build completed successfully (18121 jobs)"), lean4export exported `YangMills.jointExistence` with its closure, then "Running Lean default kernel on solution. / Lean default kernel accepts the solution / Your solution is okay!" |
| `review` | `20261111T074738.302766Z` | passed | all 43 review modules freshly compiled into `runs/…/review-objects` against this review's build (102.7 s in total), 0 warnings; the 13 required endpoints (`YMReview.Acceptance.{finite_law_on_family, lattice_and_scale, phase_and_os, translation_ward, operator_content, leading_trace, accepted_of_source, combined_acceptance}`, `YMReview.OPE.{from_source, phase_difference, constructed, channel_assembly, single_field}`) and all 96 printed axiom reports use only `propext`, `Classical.choice`, `Quot.sound` |
| `comparator --target acceptance` | `20261111T074947.838509Z` | passed | prepared a fresh review project with the 43 modules (the submission's modules were only replayed from this review's build), controls as expected, then `comparator-acceptance` exit 0 after 1,161 s: exported `YMReview.Acceptance.combined_acceptance` and "Lean default kernel accepts the solution / Your solution is okay!" |
| `comparator --target ope` | `20261111T080914.410287Z` | passed | controls as expected, then `comparator-ope` exit 0 after 1,083 s: exported `YMReview.OPE.constructed` and "Lean default kernel accepts the solution / Your solution is okay!" |

Verification mode: the runner's Comparator stage uses the upstream development launcher `.tools/comparator/scripts/fake-landrun.sh`, which prints "WARNING: THIS IS NOT REAL LANDRUN! UNSAFELY RUNNING …" and runs every step unsandboxed; no external kernel (nanoda) is configured. Comparator's README lists as assumptions that the solution has not been compiled beforehand in the checking environment and that landrun isolates the build; both fail here (the solution tree was built first, as in the committee's macOS runs). What the run establishes is statement and definition agreement with `Challenge`, the permitted-axiom check and acceptance by the Lean 4.34.0 kernel inside Comparator, under the assumption that the build environment was not adversarially modified. This review's scan (§3) found no file or process I/O in any `YM/` or construction module (`IO.FS`, `IO.Process`, `System.FilePath` occur only in `Verify.lean`, `VerifyJoint.lean`, `verification/Inventory.lean`, `verification/Usage.lean`), which makes build-time tampering with other artifacts implausible without a Lean exploit.

The committee's 2,453 warnings in the original build include the intentional `sorry` in `Challenge.lean` (assessment §9.1); this review's build log has the same 2,453 warning lines in 1,063 files, with the same single `sorry` warning.

### 6.4 What the committee's assessment-1.pdf concludes (35 pages, read in full)

Conclusion (p. 1): "In our judgment the submission proves that a relativistic quantum field theory satisfying the Wightman axioms can be constructed as a scaling limit of four-dimensional Wilson lattice gauge theory for any simple compact gauge group. It does not prove that the infinite-volume limit is unique or that there is a mass gap." They also write "We do not claim to fully understand the proof yet" and that OpenAI's Astra model helped digest the Lean code (p. 1; Acknowledgements p. 22).

Proof outline as they describe it (Part I): Wilson LGT on tori of side L_p with spacing a_N; renormalized lattice representatives of gauge-invariant curvature polynomials; Theorem 4.1 fixed-volume UV limit along the whole spacing sequence, proved by an explicit RG map for the marginal terms "following the general approach of Balaban but with many improvements such as a gauge fixing invariant under discrete lattice symmetries" (p. 6); Theorem 5.1 subsequential infinite-volume limit by Arzelà–Ascoli using reflection positivity, chessboard estimates, transfer operators and Cauchy estimates (p. 7); phase decomposition by Gelfand and Riesz–Markov on the commutative ground-state compression algebra (p. 8); the submission's own OS reconstruction for each phase (Thm 6.1); Euclidean invariance via symmetric gauge fixing, a divergence-free stress tensor with Ward identities, and a flux-decay argument with reflection positivity in several planes (p. 9); evidence of Yang–Mills: stress tensor and Ward identity (§7.1), trace law Thm 7.1 (p. 10), exclusion of finite free-field descriptions (§7.3), effective coupling log(1/r) g_W(r)² → 1/(2b₀) (Thm 7.2) and a stress-tensor scaling limit to dim g free Maxwell fields along one sequence r_k ↓ 0 (p. 11), OPE with bounds and contact extensions (§7.5).

Checks they ran (Part II): clean rebuild on Apple Silicon, 9,470 modules, ~184 min, 2,453 warnings including the intentional reference `sorry` (§9.1); inventory of 250,319 declarations, no project axioms, no `sorryAx`, no `unsafe`, 302 generated `._unsafe_rec` helpers outside the audited dependencies; the submitted VerifyJoint replay; Comparator passes on 30 Oct (public theorem), 3 Nov (their `YMReview.Acceptance.combined_acceptance`) and 5 Nov (`YMReview.OPE.constructed`), with four controls; adapters A1–A8 (DMY OS axioms for the selected trace family, operator content, `mrdouglasny/lgt` Wilson-law equality with β_submission = m β_lgt, leading trace law, common scale and positive lattice probe, translation Ward identity, combined acceptance, OPE statement alignment).

Caveats they list: the public target "omitted some of the connections to the lattice construction" (p. 14); Comparator ran with the macOS development launcher `fake-landrun.sh`, without Landrun isolation and without an external kernel, so the runs "do not test isolation of potentially hostile build code" (p. 16); "an additional external kernel implementation was not used"; code-quality concerns: only 100,168 of 250,319 declarations are used by the main theorems, and unconventional names such as `Farewell.dead`, `Cake`, `cookie`, `anxiety` (p. 15); OS comparison uses diagonal-flat Schwartz tests and cannot see contact terms (§10); OPE coefficients are not compared with perturbation theory (§7.5, §11); open questions (§8): convergence and uniqueness of the infinite-volume limit, a continuum probability measure, a uniform mass gap, Wilson loops and area law, single-particle states.


## 7. What remains unresolved or unchecked

* **Internal definitions of the detailed theorem.** The identification of the continuum fields with Yang–Mills curvature polynomials, the slope 2b₀, the Ward-normalized stress tensor and the RG calibration all live in `YangMills.constructed` and the internal types it mentions (`YM.Family`, `C.Makes`, `YM.Table`, `YM.Spec.Final`, `Spec.Calibrated`, …). The kernel checked their proofs; I read only the top layers (`YM/Source/Construction.lean`, `YM/Source/Local.lean`, `YM/Spec/Closed.lean`, `YM/RG/History.lean`, `YM/Nonperturbative/*`, `YM/Independent/*`, `YM/R2I/Campaign/Accepted.lean`, `YM/RG17/Joint.lean`). Whether these ~1M lines of definitions mean what their docstrings say is the open human-review question, as the committee also states ("We do not claim to fully understand the proof yet").
* **Generalized free fields and non-Gaussianity.** The public statement admits a selected phase whose n-point functions are Gaussian, and no theorem in either repository states that a connected 3- or 4-point function is nonzero. *Editor's note:* the Ward identity of the detailed theorem implies a nonzero truncated ⟨T; Θ; Θ⟩ by a short unformalized argument (§4.5); composites of Gaussian fields with a continuum of masses remain unexcluded.
* **Item 4 of §4.2** (dim F₀ = 1 in the selected Wightman theory) is a standard argument I did not formalize; Probe E covers the zero-insertion case formally without it.
* **Kernel diversity.** All checks here use the Lean C++ kernel (4.32.0 in VerifyJoint and my replay, 4.34.0 inside Comparator). No external kernel (nanoda, lean4lean) was run, here or by the committee.
* **Isolation.** The Comparator run used `fake-landrun.sh` after the solution had been built in the same tree, as in the committee's runs.
* **Full-coverage kernel replay.** The toolchain's `leanchecker` replays each module in the environment of its imports; a trial on five public modules needed 22 GB and was OOM-killed (exit 137), so the per-module replay of all 9,467 modules (estimated tens of hours at safe parallelism) was not attempted. The replays that were run (VerifyJoint and this review's `OwnReplay.lean`) cover every project declaration reachable from the endpoints, which is the set the theorems depend on.
* **Committee runner leftovers.** The runner's outputs stay in the git-ignored `YM/submissions/openai-20261028/runs/` (153 MB, including every `result.json` cited in §6.3) and `.tools/` (643 MB); delete them when no longer needed.
* **November submission.** Out of scope here, as in the committee package.


## Appendix A. Commands

All Lean/Lake commands used `review/env.sh` (PATH with `~/.elan/bin`; `XDG_CACHE_HOME`, `LAKE_CACHE_DIR`, `MATHLIB_CACHE_DIR`, `TMPDIR` pointing into `review/`), so caches and temporary files stayed inside `/path/to/ym-release`. The Comparator toolchain (Lean 4.34.0) went into a separate `ELAN_HOME=review/elan-home` (with a symlink to the existing 4.32.0 toolchain); the only write to `~/.elan` was the anticipated download of Lean 4.32.0. Afterwards `git status` in the OpenAI clone shows only `?? .lake/` (the repository has no `.gitignore`; no tracked file changed), and `git status` in YM is empty (its `.gitignore` covers `runs/` and `.tools/`).

| Step | Command (cwd) | Log |
|---|---|---|
| toolchain | `elan toolchain install leanprover/lean4:v4.32.0` | `logs/00-toolchain-install.log` |
| cache | `lake exe cache get` (OpenAI clone) | `logs/01-cache-get.log` |
| build | `lake build WilsonReference WilsonConstruction` (OpenAI clone), via `scripts/run_build.sh` with a memory sampler | `logs/02-build.log`, `logs/02-build.mem.log` |
| VerifyJoint | `lake env lean -j1 -DmaxHeartbeats=0 -DmaxRecDepth=4096 VerifyJoint.lean` (OpenAI clone) | `logs/03-verify-joint.log` |
| Usage | `lake -d <clone> env lean -j1 -DmaxHeartbeats=0 <clone>/verification/Usage.lean` (cwd `review/run-usage`, which holds a copy of `verification/joint-headlines.txt`; Usage.lean writes `verification/*.tsv` relative to the cwd, so running it in the clone would overwrite two tracked files); a copy of the clone's `lean-toolchain` in that directory makes elan select Lean 4.32.0 | `logs/04-usage.log` (first attempt), `logs/04b-usage.log` (rerun) |
| CompactCheck | `lake env lean -j1 verification/CompactCheck.lean` (OpenAI clone) | `logs/05-compact-check.log` |
| scan | `python3 -I scripts/lean_scan.py <clone> work/scan` | `logs/10-escape-hatch-scan.log` |
| import graph | `python3 -I scripts/import_graph.py <clone> work/graph` | `logs/11-import-graph.log` |
| committee copy | `diff -r`, `git ls-files -s` comparison, `sha256sum -c SOURCES.sha256` | `logs/20-*.log`, `logs/21-*.log` |
| committee runner | `python3 -I scripts/verify.py <stage> [--source <clone>]` for the stages integrity, tools, controls, `comparator --target submission`, review, and `comparator --target acceptance` / `ope` (cwd `YM/submissions/openai-20261028`) | `logs/22-*.log` … `logs/26-*.log`, `YM/submissions/openai-20261028/runs/*/result.json` |
| probes | `lake env lean review/lean/SpecProbes.lean` and `review/lean/ZeroInsertionProbe.lean` (both Mathlib-only closure) | `logs/30-spec-probes.log`, `logs/34-zero-insertion-probe.log` |
| own audit | `lake env lean review/lean/OwnAudit.lean`, `ArchMap.lean`, `OwnReplay.lean` | `logs/31-*.log`, `logs/32-*.log`, `logs/33-*.log`, `work/audit/*.tsv` |
| comparisons | `scripts/compare_verify.sh`, `scripts/unreached.py`, `scripts/stage_sizes.py` | `logs/36-compare-verify.log`, `logs/35-unreached-summary.log` |

