# Note 2. Generality: which gauge groups the theorem covers

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Code fragments and usage counts | Reading and `grep` of the submission at commit `3456e5e` |
| Probes F, G, H | Machine-checked: `lean/GeneralityProbes.lean`, log `logs/40-generality-probes.log`, standard axioms only |
| Group-theory classification and numerical constants | Standard mathematics and our hand computation from the code's definitions; unformalized |

## Answer in brief

The theorem is one statement for a whole class: every compact Lie group whose Lie algebra is simple, presented as a closed group of unitary matrices in any faithful representation. One proof serves all of them, without case analysis on the group. Only SU(2) has been instantiated formally. Abelian groups, groups with a U(1) factor, product groups and finite groups fail the hypothesis.

## 1. The hypothesis

```lean
-- PublicTheory.lean:25-33
structure GaugeGroup where
  n : ℕ
  image : Subgroup (UnitaryRepresentation n)
  imageClosed : IsClosed (image : Set (UnitaryRepresentation n))
  lieAlgebra : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  generates : ∀ X,
    X ∈ lieAlgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Set.range (fun u : image ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

-- PublicTheory.lean:39-45
def IsSimple (gauge : GaugeGroup) : Prop :=
  (∃ X ∈ gauge.lieAlgebra, ∃ Y ∈ gauge.lieAlgebra,
    X * Y - Y * X ≠ 0) ∧
  ∀ ideal : Submodule ℝ (Matrix (Fin (gauge.n + 1)) (Fin (gauge.n + 1)) ℂ),
    ideal ≤ gauge.lieAlgebra →
    (∀ X ∈ gauge.lieAlgebra, ∀ Y ∈ ideal, X * Y - Y * X ∈ ideal) →
    ideal = ⊥ ∨ ideal = gauge.lieAlgebra
```

A gauge group is a closed subgroup G of U(n+1). The field `generates` pins `lieAlgebra` to the true Lie algebra, the matrices X with exp(tX) ∈ G for all t. `IsSimple` asks for two non-commuting elements and for the absence of real ideals other than 0 and the whole algebra. The theorem then reads `∀ g : GaugeGroup, g.IsSimple → …` (`ChallengeSpec.lean:186`).

Two classical facts show that this class is the natural one. Every compact Lie group embeds as a closed subgroup of a unitary group (Peter–Weyl), and every closed subgroup of U(m) is a Lie group (Cartan). The class is therefore exactly: compact Lie groups with simple Lie algebra, each together with a choice of faithful unitary representation.

## 2. Which groups qualify

| Group, in a faithful unitary representation | Lie algebra | Covered | Reason |
|---|---|---|---|
| SU(N), N ≥ 2 | su(N) | Yes | Simple |
| SO(3), SO(N) for N ≥ 5 | so(N) | Yes | Simple |
| Sp(N), N ≥ 1 | sp(N) | Yes | Simple |
| G₂, F₄, E₆, E₇, E₈ | exceptional | Yes | Simple |
| Quotients by central subgroups, such as SU(N)/ℤ_N in the adjoint representation | same algebra | Yes | The hypothesis sees the Lie algebra only |
| Disconnected groups with simple Lie algebra, such as O(3) | so(3) | Yes | Same |
| A covered group in another representation, such as SU(3) acting on ℂ⁴ as 3 ⊕ 1 | same algebra | Yes | A different instance with rescaled coupling (section 5) |
| U(1), tori | abelian | No | First clause fails (Probe F) |
| U(N), S(U(3)×U(1)), any group with a U(1) factor | nonzero center | No | The center is a proper ideal (Probe G) |
| SU(3)×SU(2), SO(4), the Standard Model group | several ideals | No | Proper ideal (Probe H) |
| Finite groups, the trivial group | zero | No | First clause fails (Probe F) |

The three exclusions are machine-checked against the public definitions:

```lean
-- lean/GeneralityProbes.lean
theorem not_simple_of_abelian (g : GaugeGroup)
    (h : ∀ X ∈ g.lieAlgebra, ∀ Y ∈ g.lieAlgebra, X * Y - Y * X = 0) : ¬ g.IsSimple

theorem not_simple_of_central (g : GaugeGroup)
    (Z : Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ)
    (hZ : Z ∈ g.lieAlgebra) (hZ0 : Z ≠ 0)
    (hc : ∀ X ∈ g.lieAlgebra, X * Z - Z * X = 0) : ¬ g.IsSimple

theorem not_simple_of_proper_ideal (g : GaugeGroup)
    (I : Submodule ℝ (Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ))
    (hle : I ≤ g.lieAlgebra)
    (hid : ∀ X ∈ g.lieAlgebra, ∀ Y ∈ I, X * Y - Y * X ∈ I)
    (h0 : I ≠ ⊥) (h1 : I ≠ g.lieAlgebra) : ¬ g.IsSimple
```

## 3. One proof for all groups

The proof term of `YangMills.jointExistence` takes g and the simplicity proof as arguments and passes them on (`Solution.lean:5-6`). The construction never branches on the type of the group. The group enters through three numbers and one structural fact:

- the dimension of the Lie algebra, `Module.finrank ℝ g.lieAlgebra`, which sets the coefficient 3·dim 𝔤/π⁴ of the trace law;
- the adjoint Casimir constant, which sets the asymptotic-freedom slope;
- the matrix size n+1, which normalizes the action and the inner product;
- simplicity itself (section 4).

**Limits of this uniformity.**

- The quantifier order is `∀ g, … ∃ C`: each group gets its own family of lattice spacings, couplings and bounds. No estimate is uniform in the group, so statements about N → ∞ lie outside the theorem.
- The detailed theorem holds for every positive blocking-kernel penalty b (`Construction.lean:15`), and the public theorem takes b = 1 (`Solution.lean:6`). Whether different b give the same continuum theory is open, as part of the universality question (`SCHEME.md`, reservation G4).

## 4. What simplicity is used for

The internal copy of the hypothesis is `YM.Gauge.Simple` (`YM/Gauge/Lie.lean:179`), and the file that consumes it says so in its header: "the simplicity here is *real*, and has actual consequences for later Ward and schedule arguments" (`YM/Gauge/Casimir.lean`).

```lean
-- YM/Gauge/Casimir.lean:99-102
/-- Every real symmetric Lie-invariant form has this shape. -/
theorem invariant_scalar (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x)
    (hi : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z)) :
    ∃ c : ℝ, ∀ x y : G.Color, B x y = c * ⟪x, y⟫_ℝ

-- YM/Gauge/Casimir.lean:140-141
theorem trace_adjoint (h : G.Simple) (x y : G.Color) :
    -trace ℝ G.Color (G.ad x * G.ad y) = G.casimir * ⟪x, y⟫_ℝ
```

| Consequence of simplicity | Lean | Files that use it | Role in the proof |
|---|---|---|---|
| Every invariant quadratic form is a multiple of the inner product | `invariant_scalar` | 7, among them `YM/Push/LOOP_COEFFICIENT/Color.lean`, `YM/Push/STRESS_FLUX/Color.lean`, `YM/Next/MAXWELL/Simple.lean` | Loop corrections to the action have the form of the action, so one coupling β suffices; the stress tensor has one normalization |
| The adjoint Casimir operator is a scalar | `trace_adjoint` | 2 | The one-loop coefficient is one number |
| The slope 11·C/(24π²) is positive | `slopeConstant_pos` | 82 | Asymptotic freedom in every direction of the Lie algebra; the coupling runs to zero at short distance |
| The Lie algebra is nonzero | `Simple.nontrivial_color` | 22 | Nondegeneracy |

For a group with two simple factors the space of invariant quadratic forms is two-dimensional. The flow then needs two couplings with two slopes, and the space of conserved symmetric tensors of degree 4 has dimension two. For a U(1) factor the slope is zero. The structures `Rep.beta : ℝ` (`YM/RG/History.lean:170`) and `running` with a single positive slope (`ChallengeSpec.lean:13`) have no room for either case. Note 3 works this out on examples.

## 5. The role of the representation

The Wilson energy uses the trace of the chosen representation, divided by its dimension (`PublicWilson.lean:25-27`), and the internal inner product on the Lie algebra is ⟨X,Y⟩ = −tr(XY)/m with m the matrix size (`YM/Gauge/Colors.lean`, header). The Casimir constant in that normalization is

```lean
-- YM/Gauge/Colors.lean:180-184
def casimir : ℝ :=
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ;
  -(∑ i : G.ColorIndex, LinearMap.trace ℝ G.Color (G.ad (b i) ∘ₗ G.ad (b i))) / G.lieDim

def slopeConstant : ℝ := 11 * G.casimir / (24 * Real.pi ^ 2)
```

Our hand evaluation gives C = m · I(adjoint)/I(R), with I the Dynkin index of the representation R of dimension m. The values below are ours and unformalized.

| Instance | m | dim 𝔤 | C | Slope 11C/(24π²) | Trace-law coefficient 3·dim 𝔤/π⁴ |
|---|---|---|---|---|---|
| SU(2), defining | 2 | 3 | 8 | 0.372 | 0.092 |
| SU(3), defining | 3 | 8 | 18 | 0.836 | 0.246 |
| SU(4), defining | 4 | 15 | 32 | 1.486 | 0.462 |
| SU(5), defining | 5 | 24 | 50 | 2.322 | 0.739 |
| SO(3), vector | 3 | 3 | 3 | 0.139 | 0.092 |
| SO(6), vector (same algebra as SU(4)) | 6 | 15 | 24 | 1.115 | 0.462 |
| SU(3) on ℂ⁴ as 3 ⊕ 1 | 4 | 8 | 24 | 1.115 | 0.246 |

For SU(N) in the defining representation C = 2N², so the slope equals 11N²/(12π²). This matches the textbook one-loop law for the Wilson coupling β = 2N/g², with 1/g² = (11N/24π²)·log(1/aΛ).

Two instances of the same Lie algebra, such as SU(2) in the defining representation and SO(3) in the vector one, are different lattice theories with differently normalized couplings. The theorem gives a continuum theory for each. That the two continuum theories coincide is expected physically and is outside the theorem.

## 6. Instances proved so far

`ConcreteSU2.lean` is the only instance. Its simplicity proof, `YM/Examples/SU2.lean`, is 112 lines of explicit computation with three 2×2 matrices. Applying the theorem to another group needs a Lean proof of `IsSimple` for that group, and nothing else. Our search of `Mathlib/Algebra/Lie` at the pinned revision found the abstract notion `LieAlgebra.IsSimple` and a root-system criterion, with no ready theorem for sl(N) or su(N). A proof for su(N) by elementary matrices is a self-contained exercise that we estimate at a few hundred lines; we have left it undone.

## 7. Semisimple and abelian groups in principle

- **Products of simple groups.** With one coupling per factor the Wilson measure of a product group is a product measure, and the theory is the tensor product of the theories of the factors. Existence for semisimple groups would follow from the simple case. The public statement has a single coupling and a single trace, so it leaves this corollary unstated.
- **U(1).** Pure U(1) gauge theory is free in the continuum, with a traceless stress tensor. The trace test of the theorem (a nonzero Θ with a log⁻² law) is false there, and the correct statements are of a different kind; rigorous results on the continuum limit of the U(1) lattice theory exist in the literature (Gross 1983; Driver 1987).
