# Note 1. Provenance: where the methods of the proof come from

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Quotes from the group | The archived statements in `yang-mills-group/.github/statements/` and `docs/assessment-1.pdf` ("A §n"), read directly |
| Counts and code fragments | `grep` and reading of the submission at commit `3456e5e`; word-match counts include identifiers |
| "Classical source" attributions | Our knowledge of the literature; the sources cite no paper, so every such attribution is ours |

## Answer in brief

The proof is built on earlier methods, and the people shepherding it say so: Wilson's lattice gauge theory and Bałaban's renormalization group are named as its base. The Lean sources themselves name no author and cite no paper. They formalize an unreleased manuscript, which the group puts at 1147 pages of machine-written proofs. The parts that go beyond the earlier literature are the closing of the renormalization-group induction with observables, the continuum limit of correlations, and the route to Euclidean invariance through the stress tensor.

## 1. What the released documents say

**The group's October statement** (`statements/2026-10-statement.pdf`):

> The OpenAI work builds on methods to tackle these problems developed over several decades. These include a lattice regularization of Yang-Mills theory introduced by Kenneth G. Wilson in 1974 [...]

> [...] a rigorous treatment of the renormalization group was developed in constructive quantum field theory papers published by Tadeusz Balaban in the 1980s. Balaban's ideas were among the important elements that recently enabled OpenAI to follow the theory all the way to infinite distances and prove the existence of its proper continuum limit.

The same statement describes the origin of the result: "the exciting new results discovered by OpenAI's LLM", "the full 1147-page LLM proofs", "The length and complexity of the OpenAI manuscripts are formidable". OpenAI asked David Gross on 16 October to take custody of the proof. The statement also describes the result as "the existence of quantum Yang-Mills theory, including coupling to fermions"; the fermion part is absent from the October Lean release.

**The assessment:**

- The renormalization-group map is "following the general approach of Balaban but with many improvements such as a gauge fixing invariant under discrete lattice symmetries" (A §4.3).
- "The OpenAI work rests on prior work by many physicists and mathematicians. A full review with careful attribution will be provided in later releases by the Yang–Mills group" (A p. 1).
- The assessment "does not draw on the separate informal proof manuscript" (A p. 1).

**The group's rules** commit it to "a careful review of the work of the many researchers whose work went into these results" and to "help ensure that the work appropriately credits the researchers, techniques, and ideas that it draws on".

## 2. What the Lean sources say

**No literature citations.** A word search over all `.lean` and `.md` files of the submission gives zero occurrences for each of: Bałaban, Dimock, Brydges, Kotecký, Preiss, Kadanoff, Symanzik, Lüscher, Seiler, Federbush, Magnen, Rivasseau, Sénéor, Gawędzki, Kupiainen, Glimm, Jaffe, Fröhlich, Spencer, Lieb, Osterwalder, Schrader, Streater, Jost, Nelson, Källén, Lehmann, Haag, Ruelle, Gelfand, Naimark, Arzelà, Zimmermann, Polyakov, Wilczek, Politzer, 't Hooft, Callan, Gribov. The names that do occur are eponyms of standard objects: Wilson (7,756), Laurent (3,381), Maxwell (1,271), Taylor (1,160), Ward (828), Wick (800), Haar (332), Lorentz (324), Killing (114), Wightman (73), Mayer (50).

**Working notes that show familiarity with the constructive literature.** The comments are terse and use a private vocabulary, with occasional technique names:

```lean
-- YM/SectorNext/VACUUM_NORMALIZATION/Deletion.lean:6
Dobrushin/GK-style site induction rather than graph trees. Here we
-- YM/WilsonBulk/Heat/Devices.lean:8
to drop into Polchinski heat coefficient update with an ordered sum over
-- YM/PertExtension/OrbHaar.lean:9
Faddeev–Popov factor on this slice, including with the inversion convention.
```

"GK" is presumably Gawędzki–Kupiainen; "Polchinski" refers to the flow-equation form of the renormalization group.

**Pointers to a manuscript.** The comments carry 46 distinct LaTeX-style labels such as `eq:b2loop`, `eq:HRGv`, `prop:nfock`, `sec:qphys`, and phrases such as:

```lean
-- YM/Contacts/Expressions.lean:18
one. We keep the unit fields' slots as in `sec:omult` of the revised ms.
-- YM/Mink/Boost.lean:7
E eq:osconeM and . Shared with full-tube phase and analytic exchange.
-- YM/RG/History.lean (module comment)
See ledger on specialization/generalization from E; do not infer any usual beta-function claim
beyond `Running`.
```

A module is named `YM/Integration/ManuscriptTraceTests.lean`. The Lean development therefore follows a TeX manuscript with labelled equations and sections, revised at least once, together with an internal "ledger" (805 mentions). Neither is in the release.

**Code attributions.** `NOTICE` credits adaptations from four Mathlib files in nine modules (authors Kudryashov, Loeffler, Roblot, Degenne and Marion). `THIRD_PARTY.md` reports a comparison "with 11,353 Lean sources from the pinned libraries and compiler" and states its limit: "It cannot establish the origin of every independently reworded passage."

**Earlier versions exist privately.** `NOTICE` says the public interfaces "adapt earlier challenge and solution sources at revision eea94292e31734d46498be7836d7e8fa50ca8cd2". The shipped `verification/build.log` records that 9,340 of 9,457 modules reused compiled objects "from the verified base" and that 121 modules were removed. We queried GitHub for that revision in OpenAI's public `openai/math` repository and it is absent there. The submission repository has a single commit, so the development history is unavailable.

**Packaging lineage.** `THIRD_PARTY.md` says the notice "follows the source-attribution pattern in the maths release", meaning `openai/math`, a public repository created on 6 October 2026 that holds Comparator challenges for other formal results. Its file tree (55,173 paths on 11 November) contains no path matching Yang, Mills, Wilson, gauge or Wightman.

## 3. Lineage of each ingredient

The middle column is evidence in the code. The right column is our attribution from the literature.

| Ingredient | In the submission | Classical source |
|---|---|---|
| Lattice action with Haar measure | `wilsonLaw`, `PublicWilson.lean:29-33` | Wilson 1974 |
| Reflection positivity of the Wilson measure | `YM/Slice/Reflection.lean`: "Proof of seam reflection positivity for actual Wilson lattice. Works for all nonnegative beta" | Osterwalder–Seiler 1978; Lüscher 1977 |
| Block-spin renormalization group for gauge fields | Blocking kernel with `penalty` and `axial_factor` (`YM/RG/Patch.lean:37-45`); stationary background configurations (`YM/Next/STATIONARY`, `YM/Analytic/Frame.lean:50`); small-field threshold ĝ·monitor and large-field factor exp(−monitor^{1/5}) (`YM/RG/History.lean:83-85`); local action plus gas of activities (`History.lean:165-179`) | Bałaban, Commun. Math. Phys. 1983–1989; Wilson–Kadanoff block spins |
| Coupling recursion with the one-loop coefficient | `Transfer`, `History.lean:223-227`; `slopeConstant = 11·C/(24π²)`, `YM/Gauge/Colors.lean:184` | Gross–Wilczek and Politzer 1973 for the coefficient; Bałaban for the recursive definition of the running coupling |
| Polymer and Mayer expansions, site induction | 50 mentions of Mayer; "Dobrushin/GK-style site induction" | Classical statistical mechanics; Gawędzki–Kupiainen; Brydges and coauthors |
| Chessboard estimates and transfer operator | `YM/Cells/Chess.lean`: "Chessboard theorem. Conditional internal only on seam reflection positive" | Fröhlich–Simon–Spencer 1976; Fröhlich–Israel–Lieb–Simon 1978 |
| Compactness for the infinite-volume limit | Equicontinuity files; A §5 | Arzelà–Ascoli |
| Decomposition into pure phases | `Hierarchy.Character`, `mixture` (`ChallengeSpec.lean:34-40, 133`); `YM/Ground`, `YM/Phase` | Gelfand and Riesz–Markov representation; decomposition of states into clustering components, standard in constructive field theory |
| Reconstruction of the relativistic theory | `YM/OS`, `YM/Boundary`, `YM/Fields`; A §6.1: the submission "states and proves its own version" | Osterwalder–Schrader 1973 and 1975; Glimm–Jaffe |
| Energy–momentum spectral measure | `YM/SNAG` | Stone–Naimark–Ambrose–Godement theorem |
| Stress tensor, Ward identity, trace anomaly | `YM/Ward`, `YM/TraceExtension`; A §7.1–7.2 | Ward identities; trace anomaly of Collins–Duncan–Joglekar and Nielsen 1977 |
| Operator product expansion | `OperatorProductExpansion`, `ChallengeSpec.lean:70-80` | Wilson 1969; Zimmermann 1970 |
| Exclusion of free-field descriptions | `YM/TraceExtension/Wick`, `Fock` | Wick calculus; Källén–Lehmann positivity |

## 4. Where the proof goes beyond its sources

The earlier results it builds on stopped at the following points, to our knowledge: Bałaban obtained ultraviolet stability of the effective actions on a finite lattice torus, without correlation functions of local observables and without a continuum limit; Magnen, Rivasseau and Sénéor constructed a four-dimensional theory with an infrared cutoff; complete constructions with the axioms existed in two dimensions.

Against that baseline the new elements are:

1. Renormalized gauge-invariant local observables carried through every renormalization-group step, with a full limit a → 0 of their correlations (`SCHEME.md`, Steps 2–3).
2. A gauge fixing compatible with the lattice symmetries, named as an improvement by the group (A §4.3, §6.3).
3. Rotation and translation invariance of the limit, proved through a stress tensor normalized by its Ward identity and a flux-decay argument (A §6.3).
4. The phase decomposition as a way around the missing clustering of the infinite-volume limit (A §6.1).
5. Non-perturbative leading short-distance laws and an operator product expansion with remainder bounds (A §7).

Whether each element is new in idea or a new execution of a known programme is a question for the attribution review that the group has announced.

## 5. Open provenance questions

- **The manuscripts.** Comparison of the argument with the literature needs the 1147 pages, which are unreleased.
- **How the result was produced.** The released files name "OpenAI's LLM" without a model, a method or the extent of human involvement. The group's analysis used OpenAI's Astra model.
- **Development history.** Earlier revisions are private.
- **Fermions.** The October statement and the group's rules speak of coupling to fermions and of QCD; the group plans a separate QCD repository (`CONTEXT.md` §5).
