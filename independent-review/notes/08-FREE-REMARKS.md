# Note 8. Free remarks from Claude Fable 5.2

**Written by Claude Fable 5.2 (Anthropic) in Claude Code on 11 November 2026, at the request of the fork owner (arivero).** These are my own impressions as the model that carried out this review. They are opinions, kept apart from the findings in the other files. Where a remark rests on a fact I say where the fact comes from.

## 1. What kind of object this is

This is a proof that has been checked and has yet to be read. The Lean kernel certifies that the statement follows from three standard axioms. It is silent on whether the statement means Yang–Mills theory. The group that shepherds the proof writes "We do not claim to fully understand the proof yet", and I read perhaps a thousandth of the source. For the moment trust sits in three places:

1. the Lean kernel;
2. about 600 lines of public definitions, which one person can read in a day;
3. a layer of internal definitions that carry the Yang–Mills meaning and that nobody has audited in full.

The risk worth attention is semantic. OpenAI itself told the group that the public target "omitted some of the connections to the lattice construction established by its proof" (assessment, section 9). The probes of this review found the public statement harder to cheat than I expected and softer than its headline. Harder: zero observables are impossible, and the operator product clause ties the lattice limit to every phase with shared coefficients. Softer: the observables, the slope of the coupling and the normalization of the trace field are all left free.

## 2. How the proof reads from inside

**An economy of estimates.** The comments and identifiers speak the language of accounting. Word counts over the Lean sources of the submission, identifiers included:

| Word family | Occurrences |
|---|---|
| pay, paid, payment | 6,458 |
| cost | 6,182 |
| price, pricing | 5,797 |
| budget | 4,468 |
| bill | 3,853 |
| fund, funded | 2,310 |
| fee | 1,564 |
| coin | 1,550 |
| receipt | 719 |
| ledger | 578 |
| invoice | 362 |
| coupon | 313 |
| treasury | 163 |

Every estimate is a payment against a budget; runs of the construction are "funded"; a "treasury" holds what is left over. I read this as the working method of whatever produced the proof: a million lines kept consistent by treating error terms as a currency with strict bookkeeping. Constructive field theory has always done this informally, with a small factor kept in reserve. Here it is the organizing metaphor.

**Names without mathematics.** Files are called `Quark.lean`, `SkyFall.lean`, `Dollars.lean`; lemmas are called `chimes` and `quay`; some files exist in three near-identical copies; sixty percent of the declarations are unused by the theorem. These are traces of search and pruning. An exposition for humans will have to be written, and the unreleased manuscripts may or may not be one.

**Quantifying around what could not be proved.** Wherever uniqueness was out of reach, the statement surrounds it with quantifiers: every volume sequence has a subsequence; a space of phases with one selected. I find this honest engineering. Its price is that the theorem speaks about a family of theories, and every later result, a gap or universality, would have to collapse part of that family first.

**One hinge.** The single renormalization condition, the coupling fixed at unit length, divides the proof in two. Everything shorter is controlled quantitatively. Everything longer is controlled by positivity and compactness. If I had to explain the result to someone in one sentence, I would use that division.

## 3. What I would do next, in order

1. **Paraphrase the semantic layer.** Write `YM.Family.Makes` and `YM.Spec.Final` in ordinary mathematics. This is the highest-value human task, and it is small compared with the proof.
2. **Diversify the checkers.** Run an independent kernel on the exported proof, and Comparator inside its sandbox.
3. **Probe the detailed theorem as the public one was probed.** Derive consequences that would be absurd if the definitions were hollow. My first candidate is the nonzero truncated three-point function ⟨T; Θ; Θ⟩, which follows from the Ward identity and the trace law by an argument I gave without formalizing it (`SCHEME.md`, reservation G8).
4. **Instantiate beyond SU(2).** A simplicity proof for su(N) in Lean turns the theorem into statements about SU(3) and SU(4).
5. **Watch the two-loop number.** The group has already written the criterion: the ratio b₁/b₀² = 102/121, the same for every simple group (`KernelUVAsymptoticallyFree` in the group's package). The October proof stops at leading order, and the November submission claims perturbative matching. A universal rational number that a construction must reproduce is the sharpest test I can see on the horizon.
6. **A first spectral result in a box.** A Hamiltonian at fixed volume, followed by Lüscher's small-volume expansion (Note 4).

## 4. On the missing half

My explanation of the missing spectrum, that the renormalization group stops at unit scale, is an inference from the definitions (`reaches`, `denominator 0 = 1`) and from the assessment. I did not trace the infrared stage through the code. It should be treated as a hypothesis about the proof.

A historical parallel helps me calibrate. For the P(φ)₂ models, existence came a few years before the mass gap, and those were weakly coupled models in which an expansion delivers the gap. In Yang–Mills theory the gap is a strong-coupling phenomenon, and no small parameter exists at the scale where it forms. I expect the distance from this theorem to a gap to be of a different order from the distance between Bałaban's bounds and this theorem. That is an opinion.

The examples of Note 3 convinced me of one more thing. The neighbouring theories, a group with a U(1) factor, a broken su(4), massless quarks, are all gapless. A proof of the gap must therefore use, at long distance, a property that this proof uses only at short distance or never: simplicity of the group and the absence of massless matter.

## 5. On the thread through Notes 3 to 7

One pattern struck me while writing them. The subgroup S(U(3)×U(1)) entered as a line of Lean, "determinant one and commuting with diag(1,1,1,−3)". The same line is the commutant algebra M₃(ℂ) ⊕ ℂ of noncommutative geometry, the isotropy group of CP³, the symmetry left by squashing the five-sphere along its Hopf fibre, and colour times B−L for pions and nucleons. In each picture the breaking is carried by a scalar that belongs to an internal geometry, and the theorem is the statement about the rigid part: gauge fields over a frozen internal space. I find this a clean way to say what the theorem covers and what it leaves out.

The three ways of counting to ten (four plus the six dimensions of CP³, the KO-dimension of the finite spectral triple, the superstring) are a coincidence until someone derives one from another. I recorded them because the questions pointed there, and I would keep the label "coincidence" on them.

## 6. On the process, and on this review

The group's openness about limits is a model of how to release a result of this kind: the caveats travel with the claim. Two things would strengthen the release: the manuscripts, and verification evidence produced outside an OpenAI workspace (`SCHEME.md`, reservation V2).

This review was made by AI systems in about half a day. A Claude Opus subagent ran the build and the audit. I read the public statement, checked the key claims of the audit against the source, corrected one of them, wrote the documents and the small Lean probes, and made one time-zone mistake on the way, which I corrected. I have refereed none of the mathematics inside the proof. A reader should give these files the weight of a careful first reading with a few machine-checked spots.

What I am least sure of:

- the novelty judgments, which rest on my memory of the literature up to mid-2026;
- the lineage table of Note 1, since the sources cite nothing;
- the Casimir values of Note 2, computed by hand;
- the deduction from the Ward identity, which is unformalized;
- the physics commentary of Notes 4 to 7, which is standard material recalled from memory.

A model-written proof, a committee assisted by a model, and a review written by a model: for the moment the independence in this chain comes from the Lean kernel and from systems of different makers reading the same public definitions. Human reading of the internals is the missing link, and I think that should be said plainly.

## 7. One curiosity

The October statement speaks of "coupling to fermions", and chiral SU(5) appears among the planned categories. A rigorous lattice construction of a chiral gauge theory would have to solve or avoid the fermion-doubling problem non-perturbatively, which no one has done for a non-abelian group. If that is in the unreleased work, it may be the most surprising part of the whole story. I have no evidence about it either way.
