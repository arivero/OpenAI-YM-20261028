# Note 5. What is special about four dimensions, and where string theory stands

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Code fragments and quotes from the group's files | Read directly; "A §n" is `docs/assessment-1.pdf`, `PKG/` is `submissions/openai-20261028/` in the `YM` repository |
| Everything else: dimensional analysis, the history of constructive field theory, string theory | Commentary from general knowledge. References are from memory and unchecked. Nothing here is a result of the review |

## Answer in brief

Four is the dimension in which the gauge coupling is a pure number. Classically the theory has no scale; quantum mechanically a scale appears through the running of the coupling, and for non-abelian groups the running makes the theory weakly coupled at short distance. The proof is built on exactly this: every step that controls the ultraviolet uses the logarithmic law. Below four dimensions gauge theories are easier and partly solved. Above four the coupling carries a length and the lattice route closes.

String theory arranges the same ingredients the other way round. Its basic quantum field theory is two-dimensional and conformal, with a vanishing trace of the stress tensor as the consistency condition. That condition fixes the dimensions 26 and 10 and yields the Yang–Mills equations in the target space. The four-dimensional theorem constructs a theory whose trace is nonzero and measures it.

## 1. Four dimensions inside the proof

| Feature of four dimensions | Where it appears |
|---|---|
| The coupling is dimensionless, so it runs logarithmically | `hatBeta m = bar + slopeConstant * scale m`, with `scale m = log(1/a_m)` (`YM/RG/History.lean:79`) |
| The sign of the running is asymptotic freedom | `slopeConstant_pos`, used in 82 files (Note 2, section 4) |
| A mass scale arises with no mass parameter in the action | The single renormalization condition `reaches : β N p 0 = bar` (`YM/RG/History.lean:239`) defines the unit of length |
| F² has dimension four, equal to the dimension of spacetime | The centered trace lives in `Field 4` (`ChallengeSpec.lean:48`); its two-point function scales as r⁻⁸ |
| The scale anomaly | The trace Θ of the stress tensor is nonzero, with the law r⁻⁸ log⁻²(1/r) (`ChallengeSpec.lean:173`) |
| Spacetime itself | `abbrev Axis := Fin 4` (`YM/Space/Index.lean:18`), with no dimension parameter |

The group's own specification states the role of the logarithm. A power law with pure logarithms separates an asymptotically free theory from its alternatives:

```lean
-- PKG/provenance/af/YangMills/Core/ShortDistance.lean:40-43
1. `UVPowerLaw` — `S₂(x)·‖x‖⁸·ℓ(x)² → A > 0`: the canonical power `‖x‖⁻⁸`
   with *exactly two* powers of the asymptotic-freedom logarithm.  A free
   massive scalar (`S₂ ~ ‖x‖⁻²`), a generalized free field, or a nontrivial
   UV fixed point (anomalous power of `‖x‖`, no pure logs) all fail this.
```

## 2. The ladder of dimensions for pure gauge theory

| d | Dimension of g² | Ultraviolet behaviour | Rigorous status, to our knowledge | Relation to the proof |
|---|---|---|---|---|
| 2 | mass² | Super-renormalizable; no local degrees of freedom | Solved exactly (Migdal; Witten) and constructed as a measure on holonomies (Gross–King–Sengupta, Driver, Lévy); exact area law | The machinery of the proof is unnecessary |
| 3 | mass | Super-renormalizable: finitely many divergent diagrams | Ultraviolet stability on the lattice (Bałaban); local solutions by stochastic quantization (Chandra, Chevyrev, Hairer, Shen); mass gap open | An easier version of Step 2 |
| 4 | none | Marginal, asymptotically free for non-abelian groups | The submission under review | — |
| ≥ 5 | length^{d−4} | Strongly coupled at the cutoff | No continuum limit expected from the lattice at weak coupling | Step 2 has no starting point (Note 4, section 3) |

Two facts make four dimensions with a simple non-abelian group a unique combination.

- Among four-dimensional field theories, asymptotic freedom requires non-abelian gauge fields (Coleman and Gross). The hypothesis of the theorem, a simple non-abelian Lie algebra, describes exactly the pure gauge theories that have it.
- The other marginal theory in four dimensions, the scalar φ⁴ model, has the opposite sign of running and its continuum limit is trivial (Aizenman and Duminil-Copin). Four-dimensional Yang–Mills theory is therefore the natural first candidate for an interacting quantum field theory in the physical dimension, and the U(1) case of Note 2 fails for the same reason as φ⁴: no asymptotic freedom.

## 3. Two-dimensional field theory as the training ground

The rigorous constructions that preceded this one live in two and three dimensions: the P(φ)₂ models with their mass gap and particle spectrum (Glimm, Jaffe, Spencer), Yukawa₂, φ⁴₃, and the Gross–Neveu model in two dimensions. The last is the closest precedent in spirit: a renormalizable, asymptotically free model constructed by a renormalization-group analysis (Gawędzki and Kupiainen; Feldman, Magnen, Rivasseau and Sénéor). The tools of Steps 4 and 5 of the proof, reflection positivity, chessboard estimates and reconstruction, were developed for those models.

The released files acknowledge the lineage in two places. The assessment's open question 5 says of single-particle states: "Such an analysis has been carried out for many constructive models in 2 and 3 space-time dimensions" (A §8). The group's prior lattice formalization, `mrdouglasny/lgt`, describes itself as "toward the 2D Yang-Mills mass gap", and its strong-coupling file is titled "for the d ≥ 3 Mass Gap" (`PKG/provenance/lgt/LGT/MassGap/StrongCoupling.lean:5`).

What two dimensions has and four still lacks is the second half: a mass gap and a particle interpretation, proved together with existence.

## 4. Two-dimensional conformal field theory against the constructed theory

| Aspect | Two-dimensional conformal field theory | The constructed four-dimensional theory |
|---|---|---|
| Scale | None | Generated dynamically; fixed by one condition on the coupling |
| Trace of the stress tensor | Zero in flat space; the central charge c measures the response to curvature | Nonzero operator Θ, with a universal coefficient 3·dim 𝔤/π⁴ in its two-point law |
| Two-point functions | Pure powers r^{−2Δ} | Powers times logarithms |
| Operator product expansion | Convergent, organized by the Virasoro algebra | Asymptotic, with remainder bounds r^{D+1−w−ε} (`ChallengeSpec.lean:74-80`) |
| Symmetry | Infinite-dimensional | Poincaré only; scale invariance broken by the anomaly |
| Spectrum | Gapless by definition | Expected to have a gap; unproved (`SCHEME.md`, section 5) |
| Axioms | Wightman axioms hold, with massless spectrum | Wightman axioms proved for a phase |
| Gauge groups | Appear as current algebras on the worldsheet | Appear as the structure group of the lattice |

The comparison shows why the axioms alone leave the spectrum open: both columns satisfy them. The spectral condition and the unique vacuum of the theorem hold equally in a conformal theory, which has no gap.

## 5. The critical dimensions 26 and 10

On the string worldsheet the matter fields are D free bosons, one per target dimension, with central charge D. The ghosts of the worldsheet gauge fixing contribute −26. The trace of the worldsheet stress tensor vanishes when the total is zero, at D = 26. With worldsheet supersymmetry the count is 3D/2 − 15, which vanishes at D = 10.

The link to Yang–Mills theory is in the next order of the same condition. For a string moving in background fields, the vanishing of the worldsheet beta functions is equivalent to field equations for the background: Einstein's equations for the metric and the Yang–Mills equations for a background gauge field (Callan, Friedan, Martinec and Perry; for open strings Abouelsaood, Callan, Nappi and Yost). Classical Yang–Mills theory in the target space is thus a consistency condition of a two-dimensional conformal field theory.

| Dimension | Object | Status as a quantum gauge theory |
|---|---|---|
| 2 | Worldsheet theory | A conformal field theory, required to have zero trace |
| 4 | The theory of the theorem | Complete by itself at short distance, through asymptotic freedom |
| 10 | Gauge fields of the superstring; anomaly cancellation selects SO(32) and E₈×E₈ (Green and Schwarz) | g² has dimension length⁶; the field theory needs the string as its short-distance completion |
| 26 | Bosonic string | The same, with a tachyon |

For the groups: SO(32) and E₈ have simple Lie algebras and belong to the class of the theorem as four-dimensional pure gauge groups; E₈×E₈ is a product and is excluded (Note 2).

Four dimensions are reached from ten by compactifying six, the Kaluza–Klein step of Note 4. Far below the compactification and string scales the gauge sector is a four-dimensional gauge theory, and its pure-gauge part is the object the theorem constructs. The theorem adds one piece of information to this chain: the four-dimensional endpoint exists as a quantum field theory by itself and needs no higher-dimensional completion.

## 6. Strings and the missing half of the problem

The parts the theorem leaves open (mass gap, Wilson loops and the area law, particle states) are the parts where string pictures of gauge theory live.

- **The confining string.** An area law for Wilson loops is a string tension. At long distance the flux tube between static sources is described by a two-dimensional field theory on its worldsheet with D − 2 = 2 massless transverse modes, which predicts the universal Lüscher correction to the potential. A proof of the area law would establish the first step towards this description. The constructed theory has local gauge-invariant fields only; Wilson loops are open question 4 of the assessment (A §8).
- **Large N.** In 't Hooft's expansion a gauge theory with group SU(N) resembles a string theory with coupling 1/N. The theorem treats each group separately and has no uniformity in N (Note 2, section 3).
- **Holography.** The maximally supersymmetric gauge theory in four dimensions is conformal, has no gap, and is dual to strings on AdS₅ × S⁵. Its global symmetry SU(4) is the isometry group SO(6) of the same five-sphere that appeared in Note 4, there as a gauge group. The Hopf fibration of S⁵ over CP² is used in that literature to pass to a description on CP² × S¹ with manifest SU(3)×U(1) symmetry (Duff, Lü and Pope). Confining theories arise in this framework after a further compactification on a circle, where the gap is of Kaluza–Klein type (Witten).
- **Non-critical strings.** Away from the critical dimension the worldsheet theory keeps one extra field, the Liouville mode, whose weight is governed by 26 − D. Polyakov's proposal reads this field as an extra coordinate, the origin of the radial direction of holography. For D = 4 the deficit is 22.

These remarks place the theorem in a landscape. They add no evidence for or against a mass gap in the constructed theory.

References, from memory and unchecked against the originals: Coleman and Gross, Phys. Rev. Lett. 31 (1973) 851; Aizenman and Duminil-Copin, Ann. Math. 194 (2021) 163; Gawędzki and Kupiainen, Commun. Math. Phys. 102 (1985) 1; Feldman, Magnen, Rivasseau and Sénéor, Commun. Math. Phys. 103 (1986) 67; Callan, Friedan, Martinec and Perry, Nucl. Phys. B262 (1985) 593; Green and Schwarz, Phys. Lett. B149 (1984) 117; Lüscher, Nucl. Phys. B180 (1981) 317; Duff, Lü and Pope, Nucl. Phys. B532 (1998) 181; Witten, Adv. Theor. Math. Phys. 2 (1998) 505.
