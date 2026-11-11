# Note 6. A remark on spectral triples

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Code fragments and counts | Reading and `grep` of the submission at commit `3456e5e` and of our own Lean files |
| Everything about noncommutative geometry and the cited literature | Commentary from general knowledge; references from memory, unchecked. The submission and the group's documents contain no mention of spectral triples, noncommutative geometry or Dirac operators (one occurrence of the word "Dirac", in a comment about auxiliary data) |

## Answer in brief

A spectral triple (A, H, D) is an algebra acting on a Hilbert space together with a Dirac operator. It can meet this proof at three levels, with three different verdicts.

| Level | Idea | Verdict |
|---|---|---|
| The lattice | Rewrite each Wilson lattice theory as a finite spectral triple whose spectral action is the Wilson action | A faithful relabelling. The measure is unchanged, so the proof stands as it is |
| The regulator | Replace the lattice by a spectral cutoff on D | Conflicts with reflection positivity, on which Steps 4 and 5 of the proof rest |
| The result | Present the constructed quantum theory as a spectral triple | An ingredient is missing: pure gauge theory offers no Dirac operator. Fermions or supersymmetry would supply one |

Independently of these, the algebraic dictionary for the groups of Notes 3 and 4 is exact, and it shows the theorem and noncommutative geometry excluding the same U(1).

## 1. The dictionary for the groups

In an almost-commutative geometry the gauge group is the unitary group of a finite-dimensional algebra A_F, reduced by the unimodularity condition.

| Object of Notes 3 and 4 | Algebraic counterpart |
|---|---|
| SU(4) | Unitaries of determinant one in M₄(ℂ) |
| D = diag(1,1,1,−3) | A self-adjoint element of M₄(ℂ) |
| S(U(3)×U(1)) | Unitaries of determinant one in the commutant of D, the subalgebra M₃(ℂ) ⊕ ℂ |
| Breaking of su(4) | Passage from M₄(ℂ) to the subalgebra M₃(ℂ) ⊕ ℂ, driven by the finite Dirac operator and its inner fluctuations |
| Internal space of Kaluza–Klein theory | The finite spectral triple (A_F, H_F, D_F) |

The third row is literally how our Lean example defines the group:

```lean
-- lean/BrokenSU4Probe.lean
abbrev SU3U1 : Gauge where
  n := 3
  imageGroup := {
    carrier := {X | X.val.det = 1 ∧ X.val * D = D * X.val}
    … }
```

Four remarks on this dictionary.

- **The same U(1) is removed on both sides.** The natural gauge group of M_N(ℂ) is U(N). Noncommutative geometry imposes unimodularity to obtain SU(N). The theorem excludes U(N) because its Lie algebra has a centre (Probe G of Note 2). The condition added by hand on one side is a hypothesis of the theorem on the other.
- **The Pati–Salam spectral model.** The finite algebra ℍ ⊕ ℍ ⊕ M₄(ℂ) gives the gauge group SU(2)×SU(2)×SU(4), and the reduction of M₄(ℂ) to ℂ ⊕ M₃(ℂ) gives the colour group and B−L (Chamseddine, Connes and van Suijlekom). The chain of Note 3 is the colour part of that model.
- **Scalars from geometry, again.** The Higgs fields of the spectral model are the inner fluctuations of D in the finite directions. Note 3 found that breaking su(4) needs a scalar; Note 4 found the Kaluza–Klein scalar in the squashing of S⁵; here it is a component of the Dirac operator. The three pictures agree that the breaking is a degree of freedom of the internal geometry, and all three lie outside a pure-gauge construction.
- **Ten, once more.** The finite space of the spectral Standard Model has KO-dimension 6, so the product with spacetime has KO-dimension 10 modulo 8 (Connes; Barrett), the same count as M⁴ × CP³ in Note 4 and as the superstring in Note 5.

**Reach of the two frameworks on the group side.** Unitary groups of associative algebras are the classical groups and their products. The exceptional groups G₂, F₄, E₆, E₇, E₈ lie outside that list and inside the theorem (Note 2). Products and U(1) factors are natural in noncommutative geometry and excluded by the theorem.

## 2. Level one: the lattice as a finite spectral triple

Marcolli and van Suijlekom's gauge networks attach a finite spectral triple to each vertex of a graph and a unitary intertwiner to each edge, and show that the spectral action of such a network reproduces the Wilson action of lattice gauge theory, with a Higgs field when the vertex triples have a nontrivial Dirac operator. In that language the family of the theorem,

```lean
-- PublicWilson.lean:29-33
def wilsonLaw (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    Measure (Configuration g l) :=
  let prior : Measure (Configuration g l) := Measure.pi fun _ => haar
  let density := fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)
```

is a family of probability measures on spaces of gauge networks over the periodic lattice, with weight exp(−β · spectral action). The link variables, the Haar measure and the plaquette energy are the same objects under other names, so every step of the proof applies unchanged. The theorem then reads: the integral over finite spectral triples of this type has a continuum limit for its gauge-invariant local correlations, for each simple matrix algebra with unimodularity.

This rewriting is a change of language. Its value would lie in what the new language suggests next: vertex triples with a Dirac operator bring in Higgs fields and fermions in a controlled way, which is the direction of the group's planned QCD category.

## 3. Level two: a spectral cutoff as regulator

The spectral action Tr f(D/Λ) regularizes by a cutoff on the spectrum of D and keeps gauge invariance. Its expansion is a gauge theory with higher-derivative terms, which van Suijlekom showed to be superrenormalizable as a perturbative theory. A constructive proof along the lines of this one would need more than renormalizability. Steps 4 and 5 use reflection positivity of the regularized measure: the chessboard estimates, the transfer operator and the reconstruction of the Hilbert space all start from it.

```lean
-- YM/Slice/Reflection.lean (module comment)
# Proof of seam reflection positivity for actual Wilson lattice
Works for all nonnegative beta.
```

The Wilson action has this property at every lattice spacing. Higher-derivative actions generally lose it, and a sharp spectral truncation has no evident reflection structure. A spectral regulator would therefore have to recover positivity in the limit by a separate argument. We regard this as the main obstacle to a spectral-cutoff version of the proof.

## 4. Level three: the constructed theory as a spectral triple

What the proof constructs, for a phase, is a Hilbert space, a field algebra on a dense domain, and the joint spectral measure of the translations:

```lean
-- PublicTheory.lean:270-275 (structure W0)
  spectralRepresentation : ∀ state : H.carrier, ∀ momentum : Spacetime,
    charFun (theory.energyMomentum.diagonal state) momentum =
      inner ℂ state (theory.translations.operator momentum state)
  positiveEnergy :
    theory.energyMomentum.projection forwardConeᶜ = 0
```

Two of the three entries of a triple are present. The third, an operator D with D² tied to the Hamiltonian, is absent, and pure gauge theory has no candidate for it. The known examples of spectral triples built from quantum field theories use a supercharge: for superconformal theories in two dimensions the supercharge Q with Q² equal to the Hamiltonian up to a constant plays the role of D (Carpi, Hillier, Kawahigashi and Longo). A four-dimensional analogue would need supersymmetric Yang–Mills theory, or at least fermions, both outside the October submission.

One structural fact points the same way on the lattice. In the Hamiltonian form of lattice gauge theory the electric energy is a sum of Laplacians on copies of the group, one per link, and a Laplacian on a compact Lie group is, up to a constant, the square of its Dirac operator. Aastrup and Grimstrup built spectral triples over spaces of lattice connections from exactly these operators, along sequences of refined lattices like the one the proof uses (`denominator (k+1) = denominator k * block k`, `YM/Lattice/Scale.lean:39-41`). Their Hilbert space carries the product Haar measure. The proof supplies what that construction lacks, a continuum limit for the interacting measure, and lacks what it supplies, a Dirac operator. Whether the two can be combined is an open question that we only record.

A mass gap in this language would be a gap in the spectrum of D² above zero. The reformulation gives no new handle on it.

## 5. Summary

| Question | Answer |
|---|---|
| Can the lattice theory be written with spectral triples? | Yes, as gauge networks; the proof is unaffected |
| Can the regulator be made spectral? | Reflection positivity is the obstacle |
| Is the result a spectral triple? | Two entries of three; a Dirac operator needs fermions or supersymmetry |
| Do the groups match? | Classical groups match through matrix algebras with unimodularity; exceptional groups are covered by the theorem only; products and U(1) factors by noncommutative geometry only |
| Does broken su(4) have a spectral reading? | Yes: the commutant of D in M₄(ℂ), with the scalar supplied by the finite Dirac operator |

References, from memory and unchecked against the originals: Chamseddine and Connes, Commun. Math. Phys. 186 (1997) 731; Connes, JHEP 11 (2006) 081; Barrett, J. Math. Phys. 48 (2007) 012303; Chamseddine, Connes and van Suijlekom, JHEP 11 (2013) 132; Marcolli and van Suijlekom, J. Geom. Phys. 75 (2014) 71; van Suijlekom, JHEP 03 (2011) 146; Carpi, Hillier, Kawahigashi and Longo, Commun. Math. Phys. 295 (2010) 71; Aastrup, Grimstrup and Nest, Commun. Math. Phys. 290 (2009) 389.
