# Release context and scope: OpenAI Yang–Mills submission of 28 October 2026

**Independent review notes by the fork owner (arivero), produced with Claude Fable 5.2.**
These notes are separate from the original submission and from the Yang–Mills group's assessment. They carry no endorsement from OpenAI or from the group.

Status on 2026-11-11: reading of the released documents and source search are complete. The build and formal audit are reported in `VERIFICATION.md`; the proof outline, the discussion of the spectrum and the detailed reservations are in `SCHEME.md`.

Reliability of each part:

| Part | Basis |
|---|---|
| Quotes from the group's documents | Read directly from the released files; paths given |
| Term searches | `grep` over all `.lean`, `.md`, `.txt` sources of both repos and the assessment text; counts are exact, interpretation of hits is by sampling |
| Reading of individual Lean files | First-hand for the files named here; the bulk of the 990,000 lines is unread |
| Inferences about future releases | Our interpretation, marked as such |

## 1. What was released

The shepherding committee (Douglas, Gross as chair, Jaffe, Klebanov, Nekrasov) announced on 9 November that it would publish two repositories on 10 November. Both became public between our checks at 03:42 and 04:12 UTC on 11 November, that is between 19:42 and 20:12 Pacific time on the promised day.

| Repository | Content | State at clone |
|---|---|---|
| `yang-mills-group/OpenAI-YM-20261028` | The Lean code as submitted by OpenAI on 28 October | One branch, one commit `3456e5e` |
| `yang-mills-group/YM` | Assessment PDF, a byte-preserved copy of the submission, the group's own Lean checks, evidence logs, provenance, rerun scripts | One branch, one commit `55ba9fc` |
| `yang-mills-group/.github` | Org profile (marked "draft for group review"), archived statements, membership record | Created 8 November |

Size of the submission: 9,477 Lean files, about 990,000 lines, Lean 4.32.0, Mathlib at `81a5d257`. The group reports a three-hour source build and a 52 GiB build tree.

Contributors named besides the committee: Ron Nissim and Fred Rajasekaran (members since 2 November).

## 2. What is claimed

Headline theorem: `YangMills.jointExistence` (`Solution.lean`) proves `JointExistence` (`ChallengeSpec.lean`), for every closed matrix group with nonabelian simple real Lie algebra. `ConcreteSU2.lean` specializes to SU(2).

The group's summary (`docs/assessment-1.pdf`, page 1):

> In our judgment the submission proves that a relativistic quantum field theory satisfying the Wightman axioms can be constructed as a scaling limit of four-dimensional Wilson lattice gauge theory for any simple compact gauge group. It does not prove that the infinite-volume limit is unique or that there is a mass gap.

The assessment measures the result against the four Jaffe–Witten requirements:

| Requirement | Group's finding |
|---|---|
| 1. Nontrivial theory satisfying QFT axioms | Provided: Wightman axioms via OS reconstruction; non-freeness of the centered stress trace |
| 2. Yang–Mills local fields | Provided: renormalized operators for gauge-invariant polynomials in F and its covariant derivatives, with a conserved stress tensor |
| 3. Short-distance behavior | Partial: an OPE with error bounds and the asymptotic-freedom scaling of β; agreement with perturbative predictions is open |
| 4. Positive mass gap | Open: "The construction provides no evidence for or against a mass gap in the theory" |

The group's own caveat about its understanding: "We used OpenAI's Astra to assist with the digestion of the supplied Lean code. We do not claim to fully understand the proof yet."

## 3. Shape of the construction, as the assessment describes it

1. **Ultraviolet limit at fixed physical volume.** Wilson lattice correlations of renormalized observables are Cauchy in the lattice index along the proof's spacing sequence. The method is an explicit renormalization-group map for the marginal terms "following the general approach of Balaban but with many improvements such as a gauge fixing invariant under discrete lattice symmetries", with bounds on irrelevant terms propagated through the map. Convergence holds for test functions supported away from coincident points, and for the proof's own sequence of spacings.
2. **Infinite-volume limit by compactness.** Uniform bounds and equicontinuity (reflection positivity, chessboard estimates, transfer operator, Cauchy estimates) feed an Arzelà–Ascoli argument. Every increasing volume sequence has a convergent subsequence; one subsequence serves all correlation functions.
3. **Phase decomposition.** The limit decomposes into pure phases, each satisfying the Osterwalder–Schrader axioms.
4. **Reconstruction.** OS reconstruction, proved inside the submission, yields the Wightman theory for each phase.
5. **Identification as Yang–Mills.** Lattice origin, local field content, normalized stress tensor, leading short-distance law of the stress trace, and an all-orders separated OPE.

## 4. Why the spectrum is outside the result

The released documents agree on this point, in three places.

- Submission `README.md`: "The Wightman spectrum condition and uniqueness of the vacuum are the spectral conclusions in the public challenge. A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope."
- `docs/checks.md` in the group's package: the combined theorem "does not assert uniqueness of the large-volume limit, a mass gap, confinement, or all-orders perturbative matching", and the scale calibration with its positive lattice probe "do not establish a nonzero intrinsic continuum reference mass".
- Assessment, open questions 1, 3, 4 and 5: convergence and uniqueness of the infinite-volume limit; a uniform mass gap with exponential decay of correlations and a spectral gap of the OS Hamiltonian; Wilson loops with the area law; single-particle states and their energy-momentum spectrum.

The structural reason, in our reading of step 2 above: the infinite-volume limit comes from compactness. Compactness delivers a limit object and the positivity of the energy. A gap Δ > 0 requires a quantitative input of a different kind, a decay rate of connected correlations that is uniform in volume and lattice spacing, and the construction contains no such estimate. The same missing uniformity leaves open whether different subsequences, or different phases, give the same theory.

The package also carries a lattice-level decay result from prior work (`provenance/lgt/LGT/MassGap/StrongCoupling.lean`, by M. R. Douglas after Chatterjee 2026, §16.3): exponential decay at strong coupling with several analytic hypotheses supplied by the caller. The continuum limit lives at weak coupling, β → ∞, so this regime is disjoint from the one the construction uses. No file under `checks/` refers to these modules by name.

The reservations of the group and of this review, each with its evidence, are listed in `SCHEME.md` §6.

## 5. Hints of work beyond pure Yang–Mills

**Planned repositories.** The org profile states: "We also maintain one results repository for each major category: YM, QCD, and chiralSU5", and defines chiralSU5 as "chiral SU(5) gauge theory". `YM/README.md` repeats it: "Proposals concerning QCD or chiral SU(5) should identify that category". Only `YM` exists. Our interpretation: the group expects submissions on QCD and on a chiral gauge theory with fermions; the documents stop short of saying any has arrived.

**More OpenAI material exists outside the release.**

- A second submission: `YM/README.md` lists "OpenAI, 4 November 2026 | work in progress", described in `docs/checks.md` as having "additional perturbative matching claims".
- An informal proof manuscript: the assessment "does not draw on the separate informal proof manuscript".
- A private development repository `YM-lean/OpenAI-YM` (source of the group's check files, commit `1dec9fa`) and a private `math-commons/yang-mills`.

**The October sources are pure gauge theory.** Search results over all sources:

| Term | Finding |
|---|---|
| chiral | One occurrence in total: the `YM/README.md` sentence above |
| fermion, spinor, Grassmann, Berezin | Zero fermionic fields. Only disclaimers, e.g. `YM/Maxwell/Wick.lean:10` |
| quark | Three helper files named `Quark.lean` and a function `quarks`; see section 6 |
| QCD | One comment, `checks/ImportedAFGauge.lean:136`: "For `SU(3)` (quantum chromodynamics without quarks): `b₀ = 11`", and two JHEP citations |
| gluon | Eight comment lines describing the gauge field, including the "`3/π⁴` per gluon" amplitude |
| SU(5), SU(3) | SU(5) occurs in zero Lean files; its only mentions are the planning sentences quoted above. SU(3) appears in comments only. The theorem covers both as pure gauge theories |
| anomaly | The trace anomaly Θ = (β/2g) F², and a lattice Ward-identity residual named `anomaly` |
| Weyl | Weyl operators of the free Maxwell Fock space |
| instanton, θ-term, topological charge, BRST, Gribov | Zero occurrences |
| staggered, domain wall, Ginsparg–Wilson, Nielsen–Ninomiya | Zero occurrences |
| Higgs, Yukawa, supersymmetry, large N, finite temperature, stochastic quantization, gradient flow | Zero occurrences as physics content |
| Wilson loop, area law, glueball, single-particle states | Present only as open problems or citations |

The beta-function coefficient is defined at `checks/ImportedAFGauge.lean` as `betaZero = 11/3 * casimirAdj`, in the convention μ dg/dμ = −b₀ g³/(16π²). This is the QCD value 11 − (2/3)n_f with n_f = 0.

## 6. Objects worth knowing in the two repositories

| Object | What it is | Role |
|---|---|---|
| `YMReview.Acceptance.combined_acceptance` (`checks/CombinedAcceptance.lean`) | The group's own theorem | Binds lattice family, extracted limit and final witness into one object, so the acceptance clauses refer to a single theory |
| `YMReview.OPE.constructed` (`checks/OPECheck.lean`) | The group's OPE recheck | Explicit-radius form of the coefficient and remainder bounds; a separate endpoint from the combined theorem |
| Checks A1–A8 (`docs/checks.md`, `docs/examples/`) | Scope table with seven commented Lean walkthroughs | States what each check establishes and leaves open |
| `provenance/lgt` | M. R. Douglas, `mrdouglasny/lgt`, public | Independent definition of the Wilson lattice law |
| `provenance/osreconstruction` | Xi Yin, `xiyin137/OSreconstruction`, public | Source of the Douglas–Mei–Yin axioms E0–E4 |
| `provenance/af` | Asymptotic-freedom specification | "Version 0" formalization of the Jaffe–Witten short-distance requirement |
| Maxwell Fock files (`YM/TraceExtension/Fock`) | Free-photon Fock space inside the submission | Countertest: the stress trace has no realization in free Maxwell theory |
| Problem formulation | Credited to Cherkis–Douglas–Jaffe–Nissim–Rajasekaran | Acceptance criteria that predate the review |

Limits the group states for its own checks:

- The independent OS check covers the centered stress-trace scalar family, paired with test functions vanishing on the diagonals. An all-field OS interface is unspecified.
- Operator content has "no comparison with an independently constructed canonical Hilbert space".
- The leading trace law "is not all-orders perturbative matching".
- The two-loop ratio b₁/b₀² = 102/121 is the same for every compact simple group (`betaOne_div_betaZero_sq`), so the short-distance law of the tr F² two-point function leaves the gauge group undetermined at that order; the lattice origin carries the identification.
- The rerun script uses a development launcher without sandbox isolation, and records 2,453 build warnings in the original, one of them the intentional `sorry` of the reference statement.

**Identifier names carry little meaning.** Files such as `Quark.lean`, `Fermi.lean`, `Codex.lean`, `Clays.lean`, `SkyFall.lean` and definitions such as `chimes`, `quay`, `drum`, `ghost` are arbitrary words. `Quark.lean` exists in three near-identical copies (49 to 73 lines) and contains label bookkeeping: data attached to several operator insertions is transported from one distinguished insertion through a renormalization step, and one finite family of expansion terms serves all of them. The submission's usage table marks two of the three copies as reached by the headline theorems. Readers should take the architecture from the import graph and the statements.

**Unreached material.** By the submission's own count the 17 audited theorems reach 100,168 of 250,319 imported project declarations.

## 7. Novelty status

| Item | Status |
|---|---|
| Continuum limit of 4D Wilson lattice gauge theory with Wightman axioms | New if it stands. To our knowledge no such construction existed before 2026; Bałaban's work gave ultraviolet stability on the lattice without a continuum limit of correlations |
| OS reconstruction, reflection positivity, chessboard and compactness arguments | Known techniques, formalized here |
| One-loop RG and asymptotic-freedom scaling | Known physics; its rigorous control along the full RG trajectory is the new part |
| Mass gap, confinement, uniqueness of the vacuum state across phases and subsequences | Open, by the authors' and the group's own statements |
| The group's assessment | Preliminary by its own description; a fuller review with attribution is promised |
| These notes | Unreviewed. Document reading and source search only |
