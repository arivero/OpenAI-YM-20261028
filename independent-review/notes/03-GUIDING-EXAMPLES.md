# Note 3. SU(4), SU(3)×U(1) and broken su(4) as guiding examples

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Lean statements about SU(4) and S(U(3)×U(1)) | Machine-checked here: `lean/BrokenSU4Probe.lean`, `lean/SU4Skeleton.lean`, logs `logs/41-…` and `logs/42-…`, standard axioms only |
| Which lemmas of the proof use simplicity | Reading of `YM/Gauge/Casimir.lean` (Note 2, section 4) |
| Group theory, constants, expected continuum limits, physics of symmetry breaking | Standard material and our own reasoning; unformalized |

## Answer in brief

- **SU(4)** lies inside the theorem. The only missing piece for a formal instance is a Lean proof that su(4) is simple; we compiled the instance conditional on that proof.
- **SU(3)×U(1)**, realized as the subgroup S(U(3)×U(1)) of SU(4), lies outside. We proved in Lean that it is a legitimate gauge group of the public statement and that it fails the hypothesis. It is the cleanest example of what simplicity buys: one coupling, one slope, one stress tensor, and a mass gap that can hold at all.
- **Broken su(4)**, an SU(4) gauge theory whose symmetry is broken to SU(3)×U(1), needs a scalar field or an extra dimension, and both are outside the construction. As a thought experiment it is valuable: it has an asymptotically free gauge coupling and a massless photon.

## 1. The chain of subgroups inside U(4)

| Group | Realization in U(4) | Lie algebra | Status for the theorem | Evidence |
|---|---|---|---|---|
| SU(4) | determinant one | su(4), dimension 15 | Covered, given simplicity of su(4) | `su4Theory` |
| S(U(3)×U(1)) | elements of SU(4) commuting with D = diag(1,1,1,−3) | su(3) ⊕ u(1), dimension 9 | Excluded | `not_simple` |
| SU(3) | block 3 ⊕ 1 | su(3), dimension 8 | Covered, given simplicity of su(3) | Note 2, section 5 |

The hypothesis is lost and regained along the chain. It depends on the Lie algebra of each group and passes neither to subgroups nor to overgroups.

```lean
-- lean/BrokenSU4Probe.lean
abbrev SU3U1 : Gauge where
  n := 3
  imageGroup := {
    carrier := {X | X.val.det = 1 ∧ X.val * D = D * X.val}
    … }

abbrev su3u1 : YangMills.GaugeGroup :=
  ⟨SU3U1.n, SU3U1.imageGroup, SU3U1.closed_imageGroup, SU3U1.lie, fun _ => Iff.rfl⟩

theorem Z_mem : Z ∈ SU3U1.lie                       -- Z = i·diag(1,1,1,−3)
theorem Z_central {X : M} (hX : X ∈ SU3U1.lie) : X * Z - Z * X = 0
theorem not_simple : ¬ su3u1.IsSimple
theorem su3u1_le_su4 : SU3U1.imageGroup ≤ SU4.imageGroup
theorem lie_le : SU3U1.lie ≤ SU4.lie

-- lean/SU4Skeleton.lean
theorem su4Theory (h : su4.IsSimple) : ∃ C : WilsonFamily su4, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) :=
  jointExistence su4 h
```

## 2. SU(4)

With a proof of `su4.IsSimple`, the theorem gives for SU(4) everything it gives for SU(2). The constants, by our evaluation of the code's definitions (Note 2, section 5):

| Quantity | SU(4), defining representation |
|---|---|
| dim 𝔤 | 15 |
| Adjoint Casimir in the code's normalization, ⟨X,Y⟩ = −tr(XY)/4 | 32 |
| Slope of β against log(1/a) | 44/(3π²) ≈ 1.486 |
| Coefficient of the trace law, 3·dim 𝔤/π⁴ | 45/π⁴ ≈ 0.462 |

The same Lie algebra appears as SO(6) in its vector representation, a second covered instance with Casimir 24 and slope 1.115.

A simplicity proof for su(4) on the model of the SU(2) file (`YM/Examples/SU2.lean`, explicit matrices and commutators) means a basis of 15 matrices and a case analysis on the nonzero coefficient of an ideal element. A proof for general su(N) through elementary matrices is the better investment. We have left both undone.

## 3. S(U(3)×U(1))

**Structure.** The group is (SU(3)×U(1))/ℤ₃. Its elements are U = diag(e^{iθ}V, e^{−3iθ}) with V ∈ SU(3). Under it the adjoint of SU(4) splits as 15 = 8₀ ⊕ 1₀ ⊕ 3₄ ⊕ 3̄₋₄, with the U(1) charge measured by D. The six charged directions are absent from the subgroup.

**The Wilson action on the subgroup.** The plaquette trace is Re tr U = Re(e^{iθ} tr V) + cos 3θ. The two factors are coupled on the lattice through the phase e^{iθ}. To second order in the fields the action is the restriction of the trace form of u(4), which is an orthogonal sum of a form on su(3) and a form on u(1), both multiplied by the same β.

**Where the proof stops applying.** Each failure is an instance of a lemma that uses simplicity (Note 2, section 4).

| Step of the proof | For a simple group | For S(U(3)×U(1)) |
|---|---|---|
| Invariant quadratic forms (`invariant_scalar`) | One, up to scale | Two independent ones, on su(3) and on u(1) |
| Adjoint Casimir (`trace_adjoint`) | A scalar C | 24 on su(3) and 0 on u(1) in this normalization. The code's `casimir`, an average over the algebra, evaluates to 64/3, and the identity −tr(ad z ad z) = C·⟨z,z⟩ fails for z along the U(1): the left side is 0 |
| One coupling with one slope (`Transfer`, `running`) | β grows like slope·log(1/a) | The su(3) directions need slope 11/π² ≈ 1.115; the u(1) direction has slope 0. A single β cannot follow both |
| Stress tensor unique up to normalization | One-dimensional space | The su(3) part and the u(1) part of the stress tensor are separately conserved in the expected limit |
| Trace law with coefficient 3·dim 𝔤/π⁴ | All directions of 𝔤 contribute | The U(1) part is a free Maxwell field with traceless stress tensor. The expected coefficient is 3·8/π⁴, while the formula with dim 𝔤 = 9 gives 27/π⁴ |

**Expected continuum limit.** If β is sent to infinity at the rate that suits the su(3) part, the U(1) coupling e² ∝ 1/β tends to zero at every physical scale, and no field in the subgroup theory carries U(1) charge. The expected limit is SU(3) Yang–Mills theory times a free Maxwell field. This is our expectation and has no proof here.

**Lessons from the example.**

1. Simplicity enters the proof on the ultraviolet side only: uniqueness of the invariant form, a scalar Casimir, a positive slope.
2. In the expected limit the product theory satisfies the Wightman axioms and has a unique vacuum, and it has a massless photon. A mass gap is false for it. Any argument for a gap must therefore use simplicity or asymptotic freedom of every direction, at the infrared end, in a way the present proof has no need for. This is one more way to see why a method that works uniformly from the ultraviolet delivers existence without a gap.
3. The formula 3·dim 𝔤/π⁴ is a statement about algebras whose every direction is asymptotically free. For a semisimple algebra without abelian factors it survives as a sum over factors, since the one-loop coefficient cancels factor by factor.

## 4. Broken su(4)

**The physical picture.** An adjoint scalar Φ with vacuum value along D = diag(1,1,1,−3) breaks SU(4) to S(U(3)×U(1)). The six vector bosons in 3₄ ⊕ 3̄₋₄ become massive. Below their mass the theory is an SU(3) gauge theory, which confines, together with a U(1) whose only charged states are heavy. In the Pati–Salam reading SU(4) is extended colour, D/3 is B−L and the fourth colour is lepton number.

**What the construction lacks for it.**

| Requirement | Status in the October submission |
|---|---|
| Matter fields on the lattice | Absent: the measure is the Wilson measure on links only (`PublicWilson.lean:29-33`) |
| A scalar mass term, a relevant operator that needs tuning | No counterpart: the single renormalization condition is the coupling at unit scale (`reaches`, `YM/RG/History.lean:239`) |
| Scalar self-couplings | No counterpart. To our knowledge the quartic couplings of an adjoint scalar are generally not asymptotically free, so the ultraviolet strategy of the proof has no direct analogue for them |
| An alternative without scalars: breaking by a Wilson line around a compact extra dimension | Outside the four-dimensional setting; see Note 4 |

**Why it is still a useful guide.**

- The gauge coupling of SU(4) with one real adjoint scalar remains asymptotically free at one loop (coefficient 11/3·4 − 1/6·4 > 0). In the broken phase the spectrum contains a massless photon. Asymptotic freedom of the gauge coupling therefore coexists with a gapless spectrum once matter is present.
- The embedding U(1) ⊂ SU(4) is the textbook cure for the lack of asymptotic freedom of an abelian factor: at short distance the U(1) is part of a simple group. The simplicity hypothesis of the theorem and the logic of unification are the same condition seen from two sides.

## 5. How the examples can guide further work

| Task | Use of the example |
|---|---|
| Formal instance beyond SU(2) | Prove `IsSimple` for su(4), or for su(N), and apply `su4Theory` |
| Extending the statement to semisimple groups | Allow one coupling per simple factor; the theory is then a product, and the trace coefficient stays 3·dim 𝔤/π⁴ |
| Abelian factors | Treat U(1) separately as a free field; S(U(3)×U(1)) shows how the clauses `running` and `nonfree` must change |
| Any future mass-gap argument | Check it against S(U(3)×U(1)), where the gap is false, and against broken su(4), where the gauge coupling is asymptotically free and the photon is massless |
| Matter and symmetry breaking | The group's planned QCD and chiral SU(5) categories (`CONTEXT.md`, section 5) are where such constructions would appear |
