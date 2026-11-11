# Independent review of the OpenAI Yang–Mills submission of 28 October 2026

**This directory was added by the fork owner (arivero) on the branch `independent-review`.** Every other file on this branch is identical to the upstream commit `3456e5e` of `yang-mills-group/OpenAI-YM-20261028`.

The review was produced on 11 November 2026 with Claude Fable 5.2 in Claude Code. The build and the formal audit were run by a Claude Opus subagent. OpenAI and the Yang–Mills group have no part in it and have given it no endorsement.

## Contents

| File | Content |
|---|---|
| [SCHEME.md](SCHEME.md) | The proof in seven steps, what is new, why the spectrum is outside the result, and the reservations with their evidence. Start here |
| [VERIFICATION.md](VERIFICATION.md) | Record of the rebuild from source, the axiom and escape-hatch audit, the reading of the public statement, the architecture map and the rerun of the group's checks |
| [CONTEXT.md](CONTEXT.md) | What was released, by whom, the planned QCD and chiral SU(5) categories, and source searches for physics beyond pure gauge theory |
| `lean/` | Lean files written for this review: axiom audit, kernel replay, architecture walk, and probes of the public statement |
| `scripts/`, `env.sh` | Shell and Python helpers used for the build, scans and comparisons |
| `logs/` | Output of every command cited in `VERIFICATION.md` |
| `work/` | Small derived tables: source scan hits, import-graph summaries, proof-tree spine, log comparisons |

Local absolute paths in logs and scripts appear as `/path/to/ym-release`, the directory that held the two clones and this review. Where the reports say `review/…`, read this directory. The 32 MB table of all 250,319 declarations (`work/audit/declarations.tsv`), three large scan and graph files, and the group runner's `runs/` records are left out; `lean/OwnAudit.lean` and the group's `scripts/verify.py` regenerate them.

## Follow-up notes

Each note answers one question raised after the main review. They are commentary of the same independent status.

| Note | Question |
|---|---|
| [notes/01-PROVENANCE.md](notes/01-PROVENANCE.md) | Where do the methods of the proof come from? |

## Findings in brief

1. **The proof compiles and the kernel accepts it.** `lake build` passed in 2 h 45 min on Lean 4.32.0 with the pinned Mathlib; the public theorem `YangMills.jointExistence`, the detailed theorem `YangMills.constructed` and the SU(2) corollary depend on `propext`, `Classical.choice` and `Quot.sound` only; our own kernel replay accepted the 93,999 declarations they use.
2. **The group's checks reproduce.** Its integrity, review and Comparator stages passed here for the public target and for its two stronger targets.
3. **What is proved:** a Wightman quantum field theory obtained as a continuum limit of four-dimensional Wilson lattice gauge theory, for one phase of a subsequential infinite-volume limit, with a stress tensor, an operator product expansion and the leading short-distance laws of asymptotic freedom.
4. **What stays open:** the mass gap, uniqueness of the infinite-volume limit and of the phase, universality of the lattice limit, all-orders perturbative agreement, Wilson loops and particle states.
5. **Main caution of this review:** the public target leaves the identity of the lattice observables unspecified; the Yang–Mills identification sits in the detailed theorem, stated through internal definitions that no human has yet read in full.

## Novelty and review status

| Part | Status |
|---|---|
| The construction itself (OpenAI) | New if it stands; kernel-checked; its definitions await full human review |
| Techniques it formalizes: block-spin renormalization group, reflection positivity, OS reconstruction | Known mathematics |
| Rebuild, axiom audit, kernel replay, rerun of the group's checks (this review) | Reproduction of existing claims on independent hardware |
| Probes A, B, D, E of the public statement (this review) | New, machine-checked, small |
| Reading of the statement, proof scheme, account of the spectrum (this review) | Our interpretation; unreviewed |
| The remark that the Ward identity forces a nonzero truncated ⟨T; Θ; Θ⟩ | Ours; unformalized |
| Conditional elements | All conclusions about Yang–Mills content depend on the internal definitions meaning what their comments say |

## Reproducing

From a clone of this repository with [elan](https://github.com/leanprover/elan) installed, about 60 GB of free disk and 32 GB of memory:

```sh
lake exe cache get
lake build WilsonReference WilsonConstruction
lake env lean -j1 -DmaxHeartbeats=0 -DmaxRecDepth=4096 VerifyJoint.lean
lake env lean -DmaxHeartbeats=0 independent-review/lean/OwnAudit.lean
lake env lean -DmaxHeartbeats=0 independent-review/lean/OwnReplay.lean
lake env lean independent-review/lean/SpecProbes.lean
lake env lean independent-review/lean/ZeroInsertionProbe.lean
```

`OwnAudit.lean` and `ArchMap.lean` write their tables to an absolute output directory set inside the file; adjust it before running. Building executes the submission's Lean code with the permissions of the account that runs it.
