# Scheme of the proof: OpenAI's Lean construction of four-dimensional Yang–Mills theory

**Independent review by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code. The build and the formal audit were delegated to a Claude Opus subagent.**
This document is separate from OpenAI's submission and from the Yang–Mills group's assessment. It carries no endorsement from either.

| Reference | Meaning |
|---|---|
| "the submission" | `yang-mills-group/OpenAI-YM-20261028`, commit `3456e5e`, Lean code of 28 October 2026 |
| "A §n" | Section n of `docs/assessment-1.pdf` in `yang-mills-group/YM`, commit `55ba9fc`, dated 10 November 2026 |
| `PKG/` | `submissions/openai-20261028/` inside the `YM` repository |
| `VERIFICATION.md`, `CONTEXT.md` | Companion files of this review: build and audit record; release context and source searches |

## 1. The result in one paragraph

For every compact matrix group with simple nonabelian Lie algebra, the submission builds a quantum field theory of gauge-invariant local fields as a limit of four-dimensional Wilson lattice gauge theory. The theory satisfies the Wightman axioms, has a stress tensor obeying the translation Ward identity, has an operator product expansion, and shows at leading order the short-distance behavior that asymptotic freedom predicts. The proof is a Lean 4 development of 9,477 files and about 990,000 lines. We rebuilt it from source in 2 h 45 min; the Lean kernel accepted it with the three standard axioms only (`VERIFICATION.md` §1–3). The mass gap, uniqueness of the infinite-volume limit and all-orders agreement with perturbation theory lie outside the theorem.

## 2. The statement

Three nested statements exist, each stronger than the previous one.

| Statement | Where | Role |
|---|---|---|
| `YangMills.JointExistence` | `ChallengeSpec.lean:186`, Mathlib-only definitions (about 600 lines in three files) | Public target; a reader can audit it without the proof |
| `YangMills.constructed` | `Construction.lean:15` | Detailed theorem; adds the Yang–Mills identification through internal definitions |
| `YMReview.Acceptance.combined_acceptance` | `PKG/checks/CombinedAcceptance.lean` | The group's own target; the basis of its judgment |

```lean
-- ChallengeSpec.lean:186-188
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q)
```

In words: for each gauge group there is one family of Wilson lattice theories (side lengths L_p, lattice spacings a_N, couplings β_{N,p}, local gauge-invariant observables) such that every sequence of volumes has a subsequence along which a "hierarchy" T exists with four properties (`ChallengeSpec.lean:177-181`):

1. **`wilson`**: lattice correlations converge, first a_N → 0 at fixed volume, then along the volume subsequence, to the correlations S^mix of T.
2. **`reconstruction`**: S^mix is an average ∫ S^ξ dν(ξ) over a compact space of phases; one selected phase continues analytically to a Wightman theory (axioms W0–W3).
3. **`ope`**: an operator product expansion with remainder bounds, with one set of coefficients for all phases.
4. **`nonfree`**: a field Θ whose two-point function follows the law r⁻⁸ log⁻²(1/r) with coefficient 3·dim 𝔤/π⁴, a law that no finite combination of free-field kernels reproduces.

## 3. The proof in seven steps

Sizes are modules and lines in the import closure of the solution, from our stage count (`VERIFICATION.md` §5.2); directory boundaries are approximate.

### Step 1. Lattice theory and renormalized observables

The starting point is Wilson's measure on the periodic lattice (ℤ/L_p a_N⁻¹)⁴, with normalized Haar measure on links (`PublicWilson.lean:25-33`). Each gauge-invariant polynomial in the curvature F and its covariant derivatives is an abstract "label" of weight d. A label gets a lattice representative: a gauge-invariant polynomial in link variables on a fixed stencil, whose Taylor expansion on smooth connections matches the label to order d.

```lean
-- YM/Source/Local.lean:85-89
def Projects {d : ℕ} (H : Hol G) (p : Label G d) (F : CoverConfig G → ℂ) := ∀ J : Jet G,
    let f := fun h => F (H.links d J h)
    let g := fun h => read (scaleJet J h) p.val
    ContDiffAt ℝ (d : ℕ∞) f 0 ∧ ContDiffAt ℝ (d : ℕ∞) g 0 ∧
      ∀ k ≤ d, iteratedDeriv k f 0 = iteratedDeriv k g 0
```

The renormalized observable is a combination Σ_j c_j(N,p;v) L_{v_j} of such representatives (A §4.2, eq. 5). **Status:** classical setup; the existence of the coefficients c_j is part of the new result.

### Step 2. An exact multiscale renormalization group

This step holds three quarters of the code (6,882 modules, about 755,000 lines). For every cutoff N and volume p, the Wilson weight is rewritten at each coarser scale m ≤ N as a local action with coupling β_m times a gas of polymer activities, down to unit lattice spacing at m = 0.

```lean
-- YM/RG/History.lean:223-240
def Transfer (N p m : ℕ) :=
  let C := A.levels.clock
  (A.rep N p m).eval = (C.op m p).push (A.β N p (m+1)) (A.rep N p (m+1)).eval ∧
  |A.β N p (m+1) - A.β N p m - G.slopeConstant*Real.log (A.S.block m).val| ≤
    (C.params (m+1)).drift

structure Selected : Prop where
  path_shared (N p q m : ℕ) : m ≤ N → (A.rep N p m).path = (A.rep N q m).path
  represents (N p m : ℕ) : m ≤ N → A.Conv N p m
  starts (N p : ℕ) : (A.rep N p N).v = 0 ∧ (A.rep N p N).eval = bare (A.β N p N)
  steps (N p m : ℕ) : m < N → A.Transfer N p m
  reaches (N p : ℕ) : A.β N p 0 = A.levels.clock.bar
  running : A.Running
```

Reading of the fields:

- **`starts`**: at the finest scale the representation equals the bare Wilson weight.
- **`steps`**: each blocking step is an identity between densities. The coupling moves by `slopeConstant · log(block ratio)` up to a bounded drift, and `slopeConstant = 11·C_A/(24π²)` (`YM/Gauge/Colors.lean:184`) is the one-loop coefficient of asymptotic freedom.
- **`represents`**: at every scale the activities obey bounds that shrink with the running coupling ĝ_m = β̂_m^{-1/2}, for instance the allowance ĝ^{11/5} (`History.lean:79-85`).
- **`reaches`**: the bare couplings are tuned so that the coupling at unit scale equals one fixed number `bar` for all N and p. This is the renormalization condition.

The method is Bałaban's block-spin programme: small-field and large-field regions, polymer expansions, Gaussian integration with covariance bounds. The group notes "many improvements such as a gauge fixing invariant under discrete lattice symmetries" (A §4.3). **Status:** the class of method is known from the 1980s; closing the induction along the whole trajectory, for the measure and for all renormalized local observables, is new.

### Step 3. Ultraviolet limit at fixed volume (A Theorem 4.1)

With the multiscale representation, smeared correlations at successive cutoffs are compared and shown to be Cauchy in N. The limit holds along the entire spacing sequence, for test functions supported away from coincident points. The coupling satisfies β_{N,p}/log(1/a_N) → 11 C_A/(24π²), uniformly in the volume.

```lean
-- PublicWilson.lean:85-90
def Converges (volumeOrder : ℕ → ℕ)
    (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop :=
  ∀ n (v : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (volumeOrder k) t) ∧ ∃ row : ℕ → ℂ,
    (∀ p, C.suitable p t → Tendsto (fun N => C.smear N p v t) atTop (𝓝 (row p))) ∧
    Tendsto (fun k => row (volumeOrder k)) atTop (𝓝 (∫ x, t x * unselected v x))
```

The first `Tendsto` is this step; the second is Step 4. **Status:** new. This is the continuum limit of correlation functions that earlier stability bounds left open.

### Step 4. Infinite volume by compactness (A Theorem 5.1)

Bounds and equicontinuity of the fixed-volume correlations, uniform in the volume on compact sets of distinct points, give convergent subsequences by Arzelà–Ascoli; a diagonal argument yields one subsequence for all correlations, with limit S^mix. The tools are reflection positivity, chessboard estimates, the transfer operator and Cauchy estimates: "These general mechanisms are not specific to Yang–Mills" (A §5). **Status:** known tools; their input from Step 3 is new.

### Step 5. Phases and reconstruction (A §6, Theorem 6.1)

S^mix is reflection positive, and its clustering is unproved, so the proof decomposes it. The Gelfand and Riesz–Markov theorems, applied to a commutative algebra acting on the space of vacuum vectors, give S^mix = ∫ S^ξ dν(ξ). Each component S^ξ clusters, and the submission's own Osterwalder–Schrader reconstruction turns it into a Wightman theory with a unique vacuum.

```lean
-- ChallengeSpec.lean:133-138
  mixture {n : ℕ} (a : Fin n → T.Tag) (x : Points n) (h : x ∈ WilsonFamily.separated n) :
    (∫ i, T.correlation (some i) a x ∂T.phaseMeasure) = T.correlation none a x
  root {n : ℕ} (v : Fin n → T.Tag) (x : Points n) (h : StrictMono fun i => time (x i)) :
    T.continuation v (imaginaryTimes x) (spatialPoints x) = T.correlation (some T.selected) v x
```

**Status:** classical functional analysis, formalized; the application to a four-dimensional gauge theory is new.

### Step 6. Euclidean invariance through the stress tensor (A §6.3, §7.1)

The lattice keeps only a finite symmetry group. Three ingredients restore the full Euclidean group, hence Poincaré covariance after reconstruction: a gauge fixing that respects the lattice symmetries; a divergence-free symmetric tensor T_{μν} of degree 4, unique up to a factor that the translation Ward identity fixes; and decay of the stress flux at infinity, proved with reflection positivity in several orthogonal planes, which excludes spontaneous breaking. The group's formal version of the Ward identity is `TranslationWard` (`PKG/checks/AcceptanceSpec.lean:84`), valid for every field, every list of spectators and every phase. **Status:** new for a four-dimensional gauge theory.

### Step 7. Identification as Yang–Mills (A §3, §7)

- **Field content.** The space of fields of each degree is isomorphic to the gauge-invariant polynomials of classical Maxwell theory of that degree (A §3).
- **Trace law** (A Theorem 7.1). The centered trace Θ of the stress tensor is nonzero through renormalization, the trace anomaly:

```lean
-- ChallengeSpec.lean:173-175
  shortDistance : Tendsto (fun r : ℝ => (r^8 * (Real.log r⁻¹)^2) • T.traceTwo r)
    (𝓝[>] 0) (𝓝 ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4 : ℝ) : ℂ))
  excludes (terms : List (ℂ × Track)) : ¬ T.traceTwo =ᶠ[𝓝[>] 0] wickProfile terms
```

- **Running coupling** (A Theorem 7.2). log(1/r)·g_W(r)² → 1/(2b₀) with b₀ = 11 C_A/(48π²), for a coupling read from the effective action and for a second one read from continuum correlations.
- **Free-field scaling limit.** Along one sequence r_k → 0, rescaled stress-tensor correlations converge to those of dim 𝔤 free Maxwell fields (A §7.4).
- **Operator product expansion** (A §7.5, eq. 20) with remainder r^{D+1−w−ε}, and an extension of correlations across coincident points.

**Status:** non-perturbative proofs of these leading laws are new.

## 4. What is new

| Item | Status | Basis |
|---|---|---|
| Continuum limit of renormalized correlations of 4D Wilson lattice gauge theory, along a whole spacing sequence | New if it stands | Step 3; A Theorem 4.1 |
| A Wightman quantum field theory in four dimensions obtained from a gauge theory | New if it stands | Steps 4–5; W0–W3 at `PublicTheory.lean:270-319` |
| Restoration of Euclidean and Poincaré invariance by a Ward-normalized stress tensor | New if it stands | Step 6 |
| Non-perturbative leading asymptotic-freedom laws and a non-perturbative OPE | New if it stands | Step 7 |
| A formal proof of about one million lines, accepted by the Lean kernel, ahead of human understanding | New in kind | "We do not claim to fully understand the proof yet" (A p. 1) |
| Block-spin RG, reflection positivity, chessboard estimates, Gelfand and Riesz–Markov, OS reconstruction, SNAG theorem | Known mathematics, formalized here | `VERIFICATION.md` §5.3 |
| One-loop coefficient 11 C_A/(48π²), trace anomaly, form of the OPE | Known physics, here derived for the constructed theory at leading order | A §7 |

To our knowledge, before 2026 the rigorous results in four dimensions were ultraviolet stability bounds on the lattice (Bałaban) and a finite-volume construction with an infrared cutoff (Magnen–Rivasseau–Sénéor); complete constructions existed in two dimensions. "New if it stands" means: the kernel has certified the proofs, and the meaning of the internal definitions awaits human review (reservation V1 below).

## 5. Why the proof leaves out the spectrum

**What the theorem says about the spectrum.** Two clauses, for the selected phase: the energy–momentum spectrum lies in the closed forward cone, and the vacuum is the only translation-invariant state.

```lean
-- PublicTheory.lean:270-278 (structure W0)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H.carrier) :
    (∀ x, theory.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • theory.fields.vacuum.1 = state
```

A mass gap is the stronger statement that the spectrum of the Hamiltonian is contained in {0} ∪ [Δ, ∞) with Δ > 0 (A §1, requirement 4). Every released document places it outside the result: the submission README ("A positive mass gap ... outside its scope"), the group ("The construction provides no evidence for or against a mass gap in the theory", A §2) and the code (`YM/Fields/Spectrum.lean`, module comment: "No gap").

**The structural reason.** The renormalization group of Step 2 runs from the lattice spacing a_N up to unit physical length and stops there: scale m = 0 has spacing 1 (`YM/Lattice/Scale.lean:39-41`, `denominator 0 = 1`) and the clause `reaches` fixes its coupling to the constant `bar`. Along that range the coupling is small, so expansions converge; this is asymptotic freedom at work. Distances from 1 to L_p → ∞ receive no further renormalization-group step. That range is handled in Step 4 by positivity and compactness, which give existence of limit points and no rate of decay. A mass gap is equivalent to exponential decay of connected correlations at a rate uniform in volume and cutoff, which is quantitative infrared information of exactly the kind compactness cannot supply. In our reading, the construction reduces the question to the unit-scale effective lattice theory at fixed coupling `bar` in infinite volume, which is the long-standing open problem of the mass gap in lattice gauge theory away from strong coupling.

**What the proof does contain about the infrared.** The detailed theorem carries two power-law bounds, for every finite word state and uniformly over phases:

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

The spectral weight at energies in (0, u] is O(u²), and ⟨x, (e^{−sH} − P₀) x⟩ is O(s⁻²). These are upper bounds of the size a massless theory would saturate. A gap Δ would give zero weight below Δ and decay e^{−Δs}. The bounds are compatible with both outcomes.

**Two further obstacles.**

- A gap is a property of one definite theory, and the theorem delivers a family: one limit per volume subsequence, and within each limit a space of phases (reservations G1 and G2).
- Clustering of each phase is qualitative. The group's own walkthrough says of its OS clustering check: "Neither statement specifies an exponential rate, proves a mass gap, or makes the infrared extraction unique" (`PKG/docs/examples/OSAxioms-20261028.lean:131-132`).

**Two items that sound like a gap and are something else.**

- `TwoPointScale.MassLimit` (group check A5): the eighth root of one smeared lattice ⟨ΘΘ⟩ correlation converges to a number M > 0. Its own comment: "no intrinsic scale or spectral gap is asserted" (`PKG/checks/TwoPointPhysicalObservable.lean:129-132`).
- `PKG/provenance/lgt/LGT/MassGap/StrongCoupling.lean`: exponential decay on a lattice under the hypothesis `β < 1 / (4 * n * maxNeighbors d)` (line 1591). The continuum limit has β → ∞, the opposite regime, and no group check imports these files.

**Relation to the Clay problem.** The Jaffe–Witten statement asks for existence and a mass gap. The submission addresses the existence half in a weakened form (subsequential in the volume, one phase) and leaves the gap half untouched. The group lists as open: a uniform mass gap, Wilson loops with the area law, and single-particle states with their energy-momentum spectrum (A §8, questions 3–5).

## 6. Reservations, with evidence

### 6.1 Stated by the Yang–Mills group

**G1. The infinite-volume limit exists along subsequences.**
The quantifier is visible in the statement: `∀ p, StrictMono p → ∃ q` (`ChallengeSpec.lean:187`). Whether two subsequences give the same limit is open. The group notes that the Jaffe–Witten formulation "regards a subsequential limit obtained via compactness as insufficient, unless additional arguments establish the requisite properties of the limit", and argues that reconstruction and the local-field theorems supply such arguments (A §5; open question 1 in A §8).

**G2. Phases.**
Reconstruction applied to S^mix directly gives a Wightman theory whose vacuum may be degenerate, since clustering of S^mix is unproved (A §6.2). The headline theorem concerns one selected phase: `root` equates the continuation with `T.correlation (some T.selected)` (`ChallengeSpec.lean:137-138`). Equality of the phases is open; clustering of S^mix would imply it, and would still leave G1 open. `PKG/docs/checks.md`: "Neither a unique phase nor a unique thermodynamic limit is inferred."

**G3. Mass gap, Wilson loops, particle states.** Section 5.

**G4. Universality in the ultraviolet.**
The construction chooses its own sequences a_N, L_p and β_{N,p}: "the UV convergence theorem does not assert convergence over all possible sequences of spacings" (A §4). In the code these are fields of the family, `period` and `denominator` (`PublicWilson.lean:36-37`), under the existential `∃ C`. Other lattice actions are outside the theorem.

**G5. Correlation functions away from coincident points, without a measure.**
Test functions are `SeparatedTest n`, smooth functions supported on distinct points (`PublicWilson.lean:59-73`). A probability measure on continuum fields realizing exp(−S) DA: "This is not what is asserted by the submission" (A §3; open question 2). For the OPE-based extension across coincident points, "uniqueness, the full OS axioms for these extensions, and lattice convergence are not proven" (A §7.5); the submission README says the same about its contact construction.

**G6. Implicit renormalization.**
The coefficients c_j(N,p;v) come out of the RG transformations and "are not explicitly expressed in terms of sums or integrals" (A §4.2; `YangMills.WilsonFamily.insertion`, `PublicWilson.lean:45`).

**G7. Perturbative agreement at leading order only.**
The trace law, the running coupling and the Maxwell scaling limit are leading-order statements. In the OPE, "The cutoff D counts local observable label degrees, not loop orders. Perturbative agreement to all orders remains unproved" (A §7.5). The effective coupling g_W and the OPE coefficients are unproved to be independent of the volume subsequence (A §7.4, §7.5). `PKG/docs/checks.md`, row A4: "This is not all-orders perturbative matching."

**G8. Non-triviality against a specific class.**
`excludes` (`ChallengeSpec.lean:175`) rules out finite combinations of products of mass-shell kernels, hence polynomial observables of free fields with finitely many masses. The source comment marks the boundary:

```lean
-- YM/TraceExtension/Wick/Refute.lean:4-8
/-! Exclusion against arbitrary finite polynomial field descriptions in the
sense of the mass-shell kernels. ... No claim against a continuous-mass
generalized free field. -/
```

The group: the theorem "does not rule out every description in terms of composites of Gaussian fields" (A §7.3).
Our addition, unformalized: the Ward identity of Step 6 with Θ as central field and as spectator gives −Σ_a ∫ ∂_aχ(y) ⟨T_{ab}(y) Θ(x₀) Θ(x₁)⟩ dy = ∂_b ⟨Θ(x₀) Θ(x₁)⟩, and the right side is nonzero by the trace law. The constant ⟨T_{ab}⟩ integrates to zero against ∂χ, so the truncated three-point function ⟨T; Θ; Θ⟩ is nonzero and the fields T, Θ form a non-Gaussian family. Descriptions by composites of Gaussian fields with a continuum of masses remain unexcluded.

**G9. Reach of the independent checks.**
The group's own Osterwalder–Schrader check (axioms E0–E4 and a growth condition) covers the centered trace as a scalar family, on test functions vanishing at coincident points (`PKG/checks/CompleteOS.lean`; `PKG/docs/checks.md`). Operator content has "no comparison with an independently constructed canonical Hilbert space". The combined target and the OPE target are separate theorems with separate witnesses.

**G10. Understanding.**
"We used OpenAI's Astra to assist with the digestion of the supplied Lean code. We do not claim to fully understand the proof yet" (A p. 1).

### 6.2 Added by this review

**V1. The public target is weaker than the proof, and the stronger claims rest on unread definitions.**
In `JointExistence` the lattice observables are any continuous, gauge-invariant, finite-stencil functions (`ChallengeSpec.lean:12-22`); the slope of β is some positive number (`running : ∃ slope : ℝ, 0 < slope ∧ ...`, line 13), with the value 2b₀ appearing in the bridge (`HierarchyBridge.lean:18`); Θ is an arbitrary element of `Field 4`, so the coefficient 3 dim 𝔤/π⁴ fixes a normalization only. Our probes confirm this by machine: constant observables satisfy `WilsonRegularity` (Probe B), and positivity of the coefficient follows from simplicity alone (Probe A). The group reports the same weakness: "OpenAI subsequently informed us that its original public Comparator target YangMills.jointExistence omitted some of the connections to the lattice construction established by its proof" (A §9). The identification with curvature polynomials, the slope and the stress-tensor normalization live in `YangMills.constructed` and the group's combined target, stated through internal types (`YM.Family.Makes`, `YM.Spec.Final`) inside the million lines. The kernel checked those proofs; a human reading of those definitions is the main open review task.
In the other direction, the public statement resists cheap witnesses: zero observables are machine-checked to be impossible (Probe E, `lean/ZeroInsertionProbe.lean`), because the OPE clause quantifies over the lattice limit S^mix together with all phases, with shared coefficients (`∀ s` at `ChallengeSpec.lean:76`). Details in `VERIFICATION.md` §4.2.

**V2. Independence of the group's recorded evidence.**
The group's recorded builds and Comparator runs carry paths under `/Users/oai/Documents/Codex/...` (66 files under `PKG/evidence/`, for example `historical/build/environment.json`), and the group used OpenAI's Astra model for analysis. The files leave open who operated that machine. Our rebuild ran on separate Linux hardware and reproduced the results: same module count, same 2,453 warnings, same replay count of 100,168 declarations.

**V3. One kernel family, no sandbox.**
Every check, here and at the group, used the reference Lean kernel (4.32.0, and 4.34.0 inside Comparator). An independent kernel implementation was not run. Comparator ran with the development launcher `fake-landrun.sh`, after the solution had been built in the same tree. Our source scan found file or process access only in the verification scripts (`VERIFICATION.md` §3.2, §6.3).

**V4. Two shipped records predate the final sources.**
`verification/joint-check.log:5` records hash `3940e8dd…` for `PublicTheory.lean`; the distributed file hashes to `94111ad2…`, as `SOURCES.sha256:10` says. Three line numbers in `verification/declaration-usage.tsv` are off by two. Our reruns on the distributed sources give the same results as the shipped logs.

**V5. Readability.**
The 17 audited theorems reach 100,168 of 250,319 declarations; the rest are superseded variants, unconnected sub-projects and generated helpers (`VERIFICATION.md` §5.4). File and lemma names are arbitrary words (`Quark.lean`, `SkyFall.lean`, `chimes`), so the architecture has to be read from the import graph and the statements.

**V6. Scope of this review.**
We read the public statement in full, the top layers of the proof, the assessment and the group's check documentation. The stage descriptions in section 3 rest on the assessment, on module comments and on the dependency graph. The November submission is outside this review.

## 7. What this review checked

| Check | Result | Detail |
|---|---|---|
| Build from source, Lean 4.32.0, pinned Mathlib from cache | Passed, 9,470 modules, 2 h 45 min | `VERIFICATION.md` §1 |
| Axioms of `jointExistence`, `constructed`, SU(2) corollary, 17 endpoints (own code) | `propext`, `Classical.choice`, `Quot.sound` | §3.1 |
| Statement identical to the reference, free of project constants | 7,122 constants identical | §3.1 |
| Kernel replay of everything the theorem uses (own code) | 93,999 declarations accepted | §3.1 |
| Source scan for escape hatches | One `sorry`, the reference placeholder, outside the solution's imports | §3.2 |
| Submission's own verification scripts | Same result lines as the shipped logs | §2 |
| Group's runner: integrity, review modules, Comparator on three targets | All passed | §6.3 |
| Group's copy of the submission | Byte-identical to the OpenAI repository | §6.1 |
| Probes of the public statement | Four machine-checked probes (A, B, D, E) | §4.2, `lean/SpecProbes.lean`, `lean/ZeroInsertionProbe.lean` |

**Status of this document:** unreviewed by any third party. It summarizes a machine-checked proof that we rebuilt and audited at the level described, and it interprets a mathematical argument that we read through the assessment and the top of the code.
