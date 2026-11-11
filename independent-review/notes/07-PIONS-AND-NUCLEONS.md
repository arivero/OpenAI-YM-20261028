# Note 7. Pions and nucleons seen from S(U(3)×U(1))

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| The group S(U(3)×U(1)) and its generator Z = i·diag(1,1,1,−3) | Machine-checked definitions in `lean/BrokenSU4Probe.lean` (Note 3) |
| The centre lemma of section 2 | Machine-checked: `centre_in_U1` and `charge_congruence` in `lean/VariationCharge.lean` (Note 10). The step from the centre to the triality of a representation is the argument in words given here |
| Quotes | Released documents, read directly; "A §n" is `docs/assessment-1.pdf` |
| Hadron physics, anomaly matching, mass inequalities, lattice fermions, numerical values | Standard physics from general knowledge; references from memory, unchecked. Nothing here is a result of the review |

## Answer in brief

Pions and nucleons are made of quarks, and the October construction contains gauge fields only. The theorem therefore says nothing about them. Three things can still be said with some precision.

1. The group formalized in Note 3 already fixes one property of every hadron: the U(1) charge of a colour singlet is an integer in the right units. The reason is that the centre ℤ₃ of SU(3) lies inside the U(1).
2. Once quarks are present the second half of the Millennium problem changes its form. With two massless flavours the theory is gapless whatever its dynamics: anomaly matching requires massless pions or massless nucleons. The meaningful spectral questions are the pion mass as a function of the quark mass and the nucleon mass, which stays finite.
3. A construction in the style of this proof would give some facts about pions and nucleons before any control of the infrared, because they follow from positivity of the measure alone.

## 1. Quantum numbers under S(U(3)×U(1))

Charges are eigenvalues of D = diag(1,1,1,−3). In the Pati–Salam reading D/3 is B−L.

| State | SU(3) representation | Triality | D-charge | B−L |
|---|---|---|---|---|
| Quark q | 3 | 1 | +1 | 1/3 |
| Antiquark | 3̄ | 2 | −1 | −1/3 |
| Lepton, the fourth colour | 1 | 0 | −3 | −1 |
| Gluons | 8 | 0 | 0 | 0 |
| U(1) gauge boson | 1 | 0 | 0 | 0 |
| Heavy vector bosons of broken su(4) | 3 | 1 | +4 | 4/3 |
| **Pion**, q q̄ | 1 | 0 | 0 | 0 |
| **Nucleon**, q q q | 1 | 0 | +3 | 1 |
| Nucleon plus lepton | 1 | 0 | 0 | 0 |

Two readings of the table.

- The nucleon and the antilepton carry the same charges under the gauge group. The combination of three quarks and one lepton is the SU(4) invariant ε_{abcd} ψ^a ψ^b ψ^c ψ^d, the fourth exterior power of the defining representation.
- The pure gauge theory of Note 3 contains only the two rows with zero charge and zero triality. Its U(1) has nothing to act on, which is the group-theoretic form of the statement that its photon is free.

## 2. Why hadron charges are integers

**Rule.** For every state, D-charge ≡ triality (mod 3). Every row of the table obeys it.

**Reason.** Take the element g₀ = exp((2π/3)·Z) of the U(1) subgroup. With ω = e^{2πi/3},

  g₀ = diag(ω, ω, ω, e^{−2πi}) = diag(ω, ω, ω, 1).

The same matrix is the generator of the centre of SU(3), embedded in the upper block. On a state of charge q it acts as e^{2πi q/3} through the U(1), and on a state of triality t it acts as ω^t through SU(3). Both descriptions refer to one group element, so q ≡ t (mod 3). In other words the group is (SU(3)×U(1))/ℤ₃ ≅ U(3), and only representations with this congruence exist.

**Consequence.** Colour singlets have triality zero, so their D-charge is a multiple of 3 and their B−L is an integer: 0 for the pion, 1 for the nucleon.

**Electric charge.** The unbroken gauge group of the Standard Model has the same structure: colour and electromagnetism form (SU(3)×U(1)_em)/ℤ₃ ≅ U(3). The quark charges 2/3 and −1/3 are both congruent to 2/3 modulo 1, and the same argument gives integer charge to every hadron: +1 for π⁺ = u d̄ and for the proton u u d, 0 for π⁰ and for the neutron u d d. The electromagnetic U(1) depends on flavour, so it is embedded differently from the D of this note: through S(U(3)×U(2)) ⊂ SU(5), or as Q = T₃L + T₃R + (B−L)/2 in the Pati–Salam model.

## 3. What the October theorem contains

| Item | Status |
|---|---|
| Quark fields | Absent: the measure is on link variables only (`PublicWilson.lean:29-33`) |
| Meson and baryon operators q̄Γq and ε q q q | Absent: the local fields are gauge-invariant polynomials in the curvature and its covariant derivatives (A §3) |
| Particle states of any kind | Absent: single-particle states are open question 5 of the assessment (A §8) |
| Fermions in OpenAI's unreleased work | Claimed: the October statement speaks of existence "including coupling to fermions", and the group plans a QCD repository (`CONTEXT.md`, section 5) |

In the pure gauge theory the expected particles are glueballs. Pions and nucleons enter with the QCD submission, if and when it is released.

## 4. Three structural facts a construction with quarks must face

**4.1 The pion is a Goldstone boson.** With massless up and down quarks the chiral symmetry SU(2)×SU(2) breaks to isospin and the three pions are massless. With small quark masses, m_π² is proportional to the quark mass. In the chiral limit the theory has a unique vacuum, satisfies the spectrum condition and has no gap. The spectral clauses of the present theorem are of exactly this generality, and the infrared bounds of the detailed theorem are power laws of the kind massless particles produce (`SCHEME.md`, section 5).

**4.2 Anomaly matching forces massless states.** The flavour symmetries of massless QCD have 't Hooft anomalies, and the massless spectrum must reproduce them. Two options exist: Goldstone pions, or massless baryons. For two flavours a massless nucleon doublet matches the anomaly. For three flavours no baryon spectrum does, and chiral symmetry must break. Either way massless two-flavour QCD is gapless. The second half of the Millennium problem has no direct analogue there, and the spectral statements worth proving are different ones: the pion mass vanishes with the quark mass, and the nucleon mass stays nonzero in that limit.

**4.3 Positivity gives inequalities early.** In a vector-like theory the integral over quarks leaves a positive weight for the gauge field, so the lattice measure remains a probability measure. Correlation inequalities follow at fixed lattice spacing: the pion correlator dominates the others, which gives m_π ≤ m_N (Weingarten; Witten; Nussinov), and isospin and baryon number cannot break spontaneously (Vafa and Witten). Inequalities between correlators survive any limit of correlations. A construction that produced the continuum correlators would inherit them at once, as statements about pions and nucleons that need no solution of the infrared problem.

## 5. The U(1) factor for pions and nucleons

- **A coupling without asymptotic freedom.** Once charged quarks exist the U(1) interacts, and its coupling grows at short distance. The lesson of Note 3 applies: SU(3)×U(1) with charged matter is an effective theory, and a simple group above it (SU(4), SU(5)) restores asymptotic freedom. This is presumably why the group's third planned category is chiral SU(5).
- **The photon is massless.** With electromagnetism included the spectrum is gapless for a second reason, independent of the pions.
- **Sizes.** The U(1) is a small correction for hadrons: the charged pion is heavier than the neutral one by 4.6 MeV, mostly an electromagnetic effect, and the neutron is heavier than the proton by 1.29 MeV, the net result of electromagnetism and the quark mass difference. Lattice QCD with QED reproduces the second number (Borsanyi and coauthors).
- **An anomaly that counts colours.** The decay π⁰ → γγ is fixed by the axial anomaly, with amplitude proportional to N_c (Q_u² − Q_d²) = 3·(4/9 − 1/9) = 1. It joins the two factors of the group in one observable.

## 6. What the method would need

| Ingredient | State of the art, to our knowledge | Relation to the present proof |
|---|---|---|
| Fermion integration with reflection positivity | Known for Wilson fermions (Osterwalder and Seiler; Lüscher) | Steps 4 and 5 could start from it |
| Quark mass | Wilson fermions break chiral symmetry and need an additive mass renormalization | A second parameter to tune, beside the coupling condition `reaches` |
| Chiral symmetry on the lattice | Ginsparg–Wilson fermions keep it, with less simple locality and positivity | A choice between easy positivity and exact chiral symmetry |
| Asymptotic freedom | Slope proportional to 11 − 2n_f/3 for SU(3), positive up to 16 flavours | Step 2 keeps its starting point |
| New local fields | Quark bilinears and baryon operators | Extends the label space of Step 1 |
| Chiral gauge theories such as SU(5) with 5̄ ⊕ 10 | Open on the lattice beyond the abelian case (Nielsen and Ninomiya; Lüscher) | A rigorous construction would be a larger surprise than QCD |

Note 9 collects what the sources show about fermions and our guesses on the doubling problem.

## 7. Summary

| Question | Answer |
|---|---|
| Does the theorem describe pions or nucleons? | No field or state in it corresponds to them |
| What does the formalized group say? | Hadrons have integer B−L, and by the same argument integer electric charge |
| Is there a mass gap with quarks? | In the chiral limit the theory is gapless: massless pions, or massless nucleons for two flavours |
| What comes cheaply with positivity? | m_π ≤ m_N and unbroken isospin and baryon number |
| What does the U(1) add? | A massless photon, a coupling without asymptotic freedom, and MeV-scale mass splittings |

References, from memory and unchecked against the originals: 't Hooft, in Recent Developments in Gauge Theories (1980); Weingarten, Phys. Rev. Lett. 51 (1983) 1830; Witten, Phys. Rev. Lett. 51 (1983) 2351; Vafa and Witten, Nucl. Phys. B234 (1984) 173; Osterwalder and Seiler, Ann. Phys. 110 (1978) 440; Lüscher, Commun. Math. Phys. 54 (1977) 283; Nielsen and Ninomiya, Nucl. Phys. B185 (1981) 20; Lüscher, Nucl. Phys. B549 (1999) 295; Borsanyi et al., Science 347 (2015) 1452; Pati and Salam, Phys. Rev. D10 (1974) 275.
