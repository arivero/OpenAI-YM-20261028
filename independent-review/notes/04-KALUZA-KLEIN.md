# Note 4. Can the proof be reshaped into a Kaluza–Klein setting?

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Code fragments | Reading of the submission at commit `3456e5e` |
| Everything about Kaluza–Klein theory, compactification and the cited literature | Our knowledge and reasoning; commentary, with no formal content and no support in the repositories |

## Answer in brief

"Kaluza–Klein" can mean three things here, and they fare differently.

| Reading | Verdict |
|---|---|
| 1. Compactify some of the four dimensions of the constructed theory and study the tower of modes | Close to the proof. The fully compact case, the theory on a four-torus, is already an intermediate result. Tori with unequal sides are absent from the statement and look like a feasible extension |
| 2. Obtain the gauge field from the geometry of extra dimensions, as in the original Kaluza–Klein idea | Outside the reach of the method. The engine of the proof is a marginal, asymptotically free coupling, which exists in four dimensions only. A dictionary survives: lattice gauge theory is Kaluza–Klein theory with frozen internal geometry |
| 3. Put an extra dimension on a lattice of a few sites | Excluded twice: the gauge group becomes a product, and the links of the extra direction act as matter fields |

## 1. Where the code fixes four dimensions and the shape of the torus

```lean
-- YM/Space/Index.lean:18
abbrev Axis := Fin 4

-- PublicWilson.lean:11
abbrev Site (l : ℕ+) := Axis → ZMod l.val

-- YM/Lattice/Scale.lean:28-34
structure Schedule where
  block : ℕ → Side
  block_odd : ∀ m, Odd (block m).val
  block_large : ∀ m, 3 ≤ (block m).val
  period : ℕ → Side
  period_four : ∀ p, 4 ∣ (period p).val
  period_strict : StrictMono fun p => (period p).val
```

The dimension is the literal 4, with no dimension parameter anywhere in the development. The torus has one side length L_p for all four directions, a multiple of 4 in units of the coarsest lattice. The logarithmic law of the coupling, `hatBeta m = bar + slopeConstant * scale m` with `scale m = log(1/a_m)` (`YM/RG/History.lean:79`, `YM/Lattice/Scale.lean:115`), is the mark of four dimensions: only there is the gauge coupling dimensionless.

## 2. Reading 1: compactifying the constructed theory

**What the proof already contains.** For each volume index p the full limit a → 0 of the correlations exists on the torus of side L_p (the first limit in `Converges`, `PublicWilson.lean:89`; A Theorem 4.1). This is Yang–Mills theory on T⁴, a setting in which all four dimensions are compact.

**The Kaluza–Klein version.** Keep k directions compact with fixed lengths and send the others to infinity, giving a theory on ℝ^{4−k} × T^k. On ℝ³ × S¹ of circumference L the modes are a three-dimensional gauge field, an adjoint scalar from the component of the gauge field along the circle, and a tower with masses 2πn/L. For small L the tower decouples and the light sector is three-dimensional Yang–Mills theory with an adjoint scalar, with coupling g₃² = g²(1/L)/L.

**What an extension of the theorem would need.**

| Ingredient | Change |
|---|---|
| Lattice geometry | Separate periods per direction in `Schedule` and `Site` |
| Ultraviolet analysis (Steps 2–3 of `SCHEME.md`) | The renormalization-group steps are local; we expect them to carry over, with care for blocks that wrap around a short direction |
| Infinite-volume limit (Step 4) | Compactness in the non-compact directions only |
| Reconstruction (Step 5) | Time along a non-compact direction gives a Hamiltonian on T^k × ℝ^{3−k}; time along a compact direction gives a thermal state |
| Symmetry (Step 6) | The invariance group of the cylinder replaces the Euclidean group, which simplifies the step |

None of this is in the submission. We see no obstacle of principle.

**Why this reading matters for the spectrum.** In the proof the coupling is fixed to the constant `bar` at unit length and decreases logarithmically below it. Extrapolating the same one-loop law upward, the coupling becomes strong at a length of order exp(bar/slope) units. A box much smaller than that length is weakly coupled at every scale it contains. In that regime the spectrum of the Hamiltonian on a three-torus is computable: the light degrees of freedom are the constant modes of the gauge field, a quantum-mechanical system, and Lüscher's small-volume expansion gives its energy levels and its gap. The gap of the box is a Kaluza–Klein gap, of order 1/L up to powers of the coupling. So the fixed-volume theories that the proof constructs include a regime where spectral statements are within reach of perturbative control, and the open problem is confined to what happens as L grows past exp(bar/slope). The bounds of the proof are uniform in L and qualitative there (`SCHEME.md`, section 5).

**Symmetry breaking by a Wilson line.** A compact direction allows a constant holonomy, which acts as an adjoint Higgs field (Hosotani). For SU(4) a holonomy along diag(1,1,1,−3) would break the group to S(U(3)×U(1)), the example of Note 3, with no fundamental scalar. In pure gauge theory the one-loop potential of the holonomy has its minima at the centre of the group (Gross–Pisarski–Yaffe; Weiss), where the gauge group stays unbroken, so this breaking needs matter fields or twisted boundary conditions.

## 3. Reading 2: gauge fields from the geometry of extra dimensions

**Why the method does not transfer.** In d dimensions the gauge coupling g² has dimension length^{d−4}. For d > 4, holding g² fixed while a → 0 sends the dimensionless bare coupling g²·a^{4−d} to infinity: the theory is strongly coupled at the cutoff and there is no small parameter for a renormalization-group induction of the kind in Step 2. Gravity has the same property through Newton's constant. The original Kaluza–Klein mechanism needs one or the other.

**The dictionary that survives.** A Kaluza–Klein gauge field is the connection of a bundle whose fibre is the internal space K, and the gauge group is the isometry group of K. A lattice gauge theory assigns to each link an element of G that identifies the fibres over neighbouring sites, and the Wilson action is the curvature of that connection. In this reading the lattice theory is a Kaluza–Klein theory in which the internal metric and four-dimensional gravity are frozen. The four-dimensional coupling is proportional to G_N/R², with R the size of K, so the frozen limit is G_N → 0 and R → 0 at fixed ratio, where the tower of massive modes decouples. The theorem says that the gauge sector left over in this limit exists as a quantum field theory. It says nothing about finite R.

**Which internal spaces give covered groups.**

| Internal space K | Isometry group | Status in the theorem |
|---|---|---|
| S² | SO(3) | Covered |
| S³ | SO(4) | Excluded: so(4) = su(2) ⊕ su(2) |
| S⁴ | SO(5) | Covered |
| Round S⁵ | SO(6), the same Lie algebra as SU(4) | Covered |
| Circle bundles over CP²: squashed S⁵, lens spaces S⁵/ℤ_k, CP² × S¹ | SU(3)×U(1) at the level of Lie algebras | Excluded: the case of Note 3 |
| CP³ | SU(4)/ℤ₄ | Covered |
| S⁷ | SO(8) | Covered |
| Tori | U(1)ⁿ | Excluded: abelian |
| Witten's seven-dimensional spaces with isometry SU(3)×SU(2)×U(1) | Standard Model group | Excluded: product with a U(1) factor |

**The five-sphere and its Hopf fibration.** The isomorphism of Lie algebras su(4) ≅ so(6) singles out one internal space for the gauge group of Note 3: the round five-sphere, whose isometry group is SO(6). The same sphere is a circle bundle over the complex projective plane, S¹ → S⁵ → CP². The base carries the isometries SU(3) and the fibre carries U(1). The three objects of Note 3 then have a geometric reading:

| Object of Note 3 | Internal geometry |
|---|---|
| SU(4), as SO(6) | The round S⁵ |
| SU(3)×U(1) | A circle bundle over CP²: the fibre and the base keep their own isometries |
| Broken su(4) | The squashed S⁵: rescaling the Hopf fibre against the base reduces the isometry group from SO(6) to U(3) |

The subgroup U(3) ⊂ SO(6) that survives the squashing is the stabilizer of a complex structure on ℝ⁶. It is the image of S(U(3)×U(1)) ⊂ SU(4) of Note 3, since the six-dimensional representation of SU(4) decomposes as 3 ⊕ 3̄ under it. Every circle bundle over CP² shares this symmetry algebra: the lens spaces S⁵/ℤ_k, which are the bundles of Chern number k, and the product CP² × S¹, the trivial bundle.

Two consequences for the comparison with the theorem:

- The order parameter of the breaking is the squashing, a modulus of the internal metric, and such a modulus is a scalar field in four dimensions. Note 3 found that breaking su(4) needs a scalar; in the Kaluza–Klein reading the scalar is supplied by geometry. The frozen-geometry limit, where the theorem applies, has no such field: it sees the round sphere and the squashed one as two separate gauge groups, one covered and one excluded.
- M⁴ × S⁵ has nine dimensions. A second homogeneous space built from the same pair of groups is CP³ = SU(4)/S(U(3)×U(1)), with isometry SU(4) and isotropy S(U(3)×U(1)); it is the base of the Hopf fibration of S⁷, has six dimensions, and makes M⁴ × CP³ ten-dimensional. Note 5 returns to these dimensions.

**Coset-space dimensional reduction.** A higher-dimensional gauge theory on M⁴ × G/H with symmetric fields reduces to a four-dimensional gauge theory with Higgs fields of geometric origin (Forgács–Manton). This is a natural source of theories with broken symmetry. It lies outside the construction because it has scalar matter, as in Note 3, section 4.

## 4. Reading 3: an extra dimension on a lattice

A fifth dimension with n lattice sites turns a five-dimensional gauge theory with group G into a four-dimensional one with group Gⁿ and group-valued fields on the links of the fifth direction (dimensional deconstruction, Arkani-Hamed–Cohen–Georgi). The group Gⁿ fails the simplicity hypothesis (Probe H of Note 2), and the link fields are matter of non-linear sigma-model type, which is not asymptotically free in four dimensions. One corner connects to the theorem: when the coupling along the fifth direction vanishes the layers decouple, and each layer is a four-dimensional theory of the covered kind.

## 5. Summary

| Variant | Inside the theorem | Obstacle | What would be needed |
|---|---|---|---|
| Theory on T⁴ of side L_p | Yes, as intermediate result | None | Nothing |
| ℝ^{4−k} × T^k with a tower of modes | No | Statement uses a single period | Anisotropic tori; the rest should adapt |
| Spectrum in a small box | No | No Hamiltonian is stated at fixed volume | Reconstruction on the torus, then the small-volume expansion |
| Gauge group from isometries of K | No | Needs gravity; no marginal coupling above four dimensions | A different method |
| Breaking by squashing the internal space (S⁵ over CP²) | No | The squashing modulus is a scalar field | Matter fields, as in Note 3 |
| Higher-dimensional gauge theory, reduced | No | Dimensionful coupling; scalars after reduction | A different method, and matter fields |
| Lattice fifth dimension | No | Product group, sigma-model matter | Products and matter fields |

References, from memory and unchecked against the originals: Lüscher, Nucl. Phys. B219 (1983) 233; Gross, Pisarski and Yaffe, Rev. Mod. Phys. 53 (1981) 43; Hosotani, Phys. Lett. B126 (1983) 309; Witten, Nucl. Phys. B186 (1981) 412; Forgács and Manton, Commun. Math. Phys. 72 (1980) 15; Arkani-Hamed, Cohen and Georgi, Phys. Rev. Lett. 86 (2001) 4757.
