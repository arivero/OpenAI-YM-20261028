# Note 9. Fermions and the doubling problem: what the sources show and what can be guessed

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Search results and code fragments | `grep` and reading of the submission at commit `3456e5e` |
| Quotes | Released documents, read directly; "A §n" is `docs/assessment-1.pdf` |
| Sections 3 and 4 | Guesses. They combine the design of the released proof with standard lattice field theory recalled from memory. No released file supports them directly |

## Answer in brief

The October code contains no fermions and no preparation for them. What the released material offers is indirect: the design of the proof shows which treatments of fermions would fit it. For QCD the doubling problem is harmless and the fit is good. For a chiral gauge theory such as SU(5) the problem is real, and the proof's own way of restoring a symmetry that the lattice breaks is the most natural guess for how it could be attacked.

## 1. What the sources show

**No fermionic machinery.** Case-insensitive search over all Lean sources of the submission:

| Pattern | Lines |
|---|---|
| Grassmann, Berezin, Pfaffian | 0 |
| spinor, Clifford, gamma matrices, γ₅ | 0 |
| Majorana, left-handed, right-handed, chiral | 0 |
| Ginsparg, domain wall, Kogut, Susskind, Nielsen, Ninomiya | 0 |
| staggered | 1, an unrelated comment about "staggered windows" (`YM/AnalyticBridge/SECTOR_AFFINE_JETS/Reach.lean:50`) |
| fermion, fermionic | 1 |

The single hit is a disclaimer:

```lean
-- YM/Maxwell/Wick.lean:7-10
`correlation` acts on the actual polynomial labels (it restricts to shell and
invariant sector). `moment` on any Wick polynomial, useful algebraically and in detector proofs.
Both only use different insertions for pairings. Stars on reflected legs must be
supplied separately. No sign representation from any fermionic grading.
```

Words that look relevant turn out to be identifiers with other meanings: `Flavor` (274 lines), `Species`, `doubling` (a map on index sums), `helicity` (a lemma name), and the file names `Quark.lean` and `Fermi.lean` (`CONTEXT.md`, section 6). The 150,151 declarations that the theorem leaves unused contain no fermionic development either, since the search covers every file.

**What the documents claim.** The group's October statement describes OpenAI's result as existence "including coupling to fermions", its rules name "YM theory in four dimensions and QCD", and its repository plan adds a category "chiralSU5" (`CONTEXT.md`, section 5). The fermion work therefore exists outside this release, in the manuscripts or in a later submission.

## 2. Two different problems under one name

A naive lattice Dirac operator describes sixteen fermions in four dimensions where one was intended. The Nielsen–Ninomiya theorem says that a lattice action that is local, translation invariant and exactly chirally symmetric always has such doublers. The consequences depend on the theory.

| Theory | Is doubling an obstacle? | Why |
|---|---|---|
| QCD, a vector-like theory | No | Wilson's term removes the doublers. Its price is chiral symmetry at finite lattice spacing, which the continuum limit recovers after tuning the quark mass |
| A chiral gauge theory, such as SU(5) with 5̄ ⊕ 10 | Yes | The gauge symmetry itself is chiral. Removing the doublers breaks gauge invariance at finite lattice spacing, or requires a more elaborate construction |

## 3. Guess for QCD: the proof's design already fits

Three features of the released proof match the standard treatment of Wilson fermions.

**Reflection positivity is available.** Steps 4 and 5 of the proof start from reflection positivity of the lattice measure (`YM/Slice/Reflection.lean`: "Works for all nonnegative beta"). Wilson fermions keep this property (Osterwalder and Seiler; Lüscher), and so do staggered fermions in a site-reflection form. A construction with either could reuse the chessboard estimates and the reconstruction.

**A symmetry broken by the lattice and restored by a Ward identity.** The proof faces this situation already. The lattice breaks rotations, and Step 6 recovers them through a stress tensor whose normalization is fixed by the translation Ward identity (A §6.3, §7.1; `TranslationWard` in the group's checks). Chiral symmetry with Wilson fermions is treated in exactly this way in lattice QCD: the axial Ward identities fix the tuning of the quark mass and the normalization of the axial current. We expect a QCD version of the proof to treat chiral symmetry as it treats rotations, with one more renormalization condition beside the one on the coupling (`reaches`, `YM/RG/History.lean:239`).

**The blocking kernel is the one from which the Ginsparg–Wilson relation was derived.** The renormalization group of the proof integrates out short scales through a smooth blocking kernel with a free positive parameter:

```lean
-- YM/RG/Patch.lean:37-39
structure KernelChoices where
  penalty : ℝ
  frame_cut : ℝ

-- Construction.lean:15-16
theorem constructed (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
    ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
```

Ginsparg and Wilson obtained their relation, the modified form of chiral symmetry that a lattice Dirac operator can satisfy exactly, by applying a block-spin transformation with a Gaussian kernel to a chirally symmetric theory; the parameter of the kernel is the coefficient in the relation. A block-spin proof for fermions would produce effective Dirac operators of this kind at every coarse scale as a by-product. We read the parameter `penalty` as a sign that the machinery is of the right type. It is a structural analogy; the released code blocks gauge fields only.

**Asymptotic freedom survives.** For SU(3) the slope is proportional to 11 − 2n_f/3, positive up to sixteen flavours, so Step 2 keeps its starting point.

## 4. Guesses for a chiral gauge theory

Here the released material gives no hint beyond the category name. The known strategies, with our view of how each fits the proof:

| Strategy | Idea | Fit with the released proof |
|---|---|---|
| Break the gauge symmetry at the cutoff and restore it by counterterms (the "Rome approach") | Use a Wilson term that violates the chiral gauge symmetry, fix the gauge, and tune finitely many counterterms so that the Ward identities hold in the limit | The closest fit, in our judgment. The proof already fixes the gauge ("a gauge fixing invariant under discrete lattice symmetries", A §4.3), already tracks every marginal and relevant term through the renormalization group, and already restores a broken symmetry through Ward identities. Anomaly cancellation of 5̄ ⊕ 10 is the condition for such a restoration to be possible |
| Ginsparg–Wilson fermions with Lüscher's construction of the chiral measure | Exact gauge invariance at finite lattice spacing | Complete for abelian groups, and for non-abelian groups to all orders of perturbation theory. Reflection positivity of the resulting measure is unclear, which matters for Steps 4 and 5 |
| Domain-wall fermions with an extra dimension | Chiral modes on a four-dimensional boundary | Needs the mirror modes of the other boundary to decouple; a fifth direction is outside the setting (Note 4) |
| Mirror fermions made heavy by strong interactions (symmetric mass generation) | Start vector-like and gap the mirror sector without breaking the gauge symmetry | Needs strongly coupled lattice interactions with no small parameter, the opposite of what Step 2 uses |

Two properties of chiral SU(5) make it a natural target for this method, and one makes it instructive for the spectrum.

- **It is asymptotically free and anomaly free.** With n generations of 5̄ ⊕ 10 the one-loop coefficient is proportional to 55/3 − 4n/3, positive up to thirteen generations, and the gauge anomalies of 5̄ and 10 cancel.
- **It has no fermion mass terms.** A chiral theory admits no gauge-invariant mass, so there is no quark-mass parameter to tune. The relevant-operator problem that Wilson fermions bring to QCD takes another form here: the counterterms that restore gauge invariance.
- **Its expected spectrum is gapless.** The classic expectation for one generation is confinement with a massless composite fermion, built from 5̄ · 5̄ · 10, that saturates the 't Hooft anomaly of the surviving global U(1) (charges 3 and −1 for the two multiplets give 5·27 − 10 = 125 = 5³). As with massless QCD in Note 7, existence would come with massless states, and a mass gap would be the wrong second question.

## 5. Where to look when more is released

| Signal in a future release | What it would indicate |
|---|---|
| A Grassmann integral or a determinant in the lattice measure, with a Wilson term | The standard route for QCD |
| A second renormalization condition beside `reaches` | Tuning of the quark mass |
| Axial Ward identities among the acceptance clauses | Chiral symmetry restored as rotations were |
| An operator relation of Ginsparg–Wilson type in the effective actions | Chirality carried through the blocking |
| Gauge-variant counterterms, or BRST identities, in a chiral construction | The counterterm route for chiral SU(5) |
| A fifth lattice direction | Domain walls |

References, from memory and unchecked against the originals: Nielsen and Ninomiya, Nucl. Phys. B185 (1981) 20; Ginsparg and Wilson, Phys. Rev. D25 (1982) 2649; Osterwalder and Seiler, Ann. Phys. 110 (1978) 440; Bochicchio, Maiani, Martinelli, Rossi and Testa, Nucl. Phys. B262 (1985) 331; Borrelli, Maiani, Rossi, Sisto and Testa, Nucl. Phys. B333 (1990) 335; Lüscher, Nucl. Phys. B549 (1999) 295 and Nucl. Phys. B568 (2000) 162; Kaplan, Phys. Lett. B288 (1992) 342; Eichten and Preskill, Nucl. Phys. B268 (1986) 179; Dimopoulos, Raby and Susskind, Nucl. Phys. B173 (1980) 208.
