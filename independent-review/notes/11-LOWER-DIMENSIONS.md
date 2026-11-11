# Dimension dependence and the D=3,2,1 endpoints

Here D denotes total Euclidean spacetime dimension, including the direction
used as time in reconstruction. The released theorem has D=4 fixed; it
does not quantify over D. The analysis below refers to submission commit
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`.

Three levels of evidence are distinguished: source definitions read directly,
the finite-lattice statements proved in `../lean/VariationDimension.lean`,
and deductions or proposed adaptations. No D=3 or D=2 continuum theorem is
proved by this probe. The earlier `05-DIMENSIONS-AND-STRINGS.md` gives a
broader discussion; the locators and derivations here concern the actual
dimension changes needed in the construction.

## 1. Explicit dependence in the statement and proof

The source links refer to the unchanged submission. The table gives source
identifiers and summarizes their definitions; the consequence column
contains deductions.

| Dependence | Exact source | Consequence of changing D |
|---|---|---|
| Public spacetime and time split | [PublicTheory.lean:51](../../PublicTheory.lean#L51): `Axis := Fin 4`, `SpaceAxis := Fin 3`, `timeAxis := Fin.last 3` | Parameterize by a spatial dimension s, with D=s+1; time is `Fin.last s`. |
| Internal geometry separately fixes the same dimensions | [YM/Space/Index.lean:18](../../YM/Space/Index.lean#L18) | Changing only the public aliases does not change the construction. |
| Periodic sites, links, and plaquettes | [PublicWilson.lean:11](../../PublicWilson.lean#L11): `Site := Axis → ZMod l.val`, `Directions := {p : Axis × Axis // p.1 < p.2}` | Site count becomes l^D and the number of plaquette planes becomes D(D−1)/2. The action formula itself generalizes directly. |
| Lattice volume count | [YM/Lattice/Site.lean:32](../../YM/Lattice/Site.lean#L32): `site_card ... = n.val ^ 4` | Replace the volume exponent by D; constants depending on coordination must also change. |
| Riemann-sum measure | [PublicWilson.lean:79](../../PublicWilson.lean#L79): `(C.mesh N : ℂ) ^ (4*n)` | An n-point smear requires a^(D n). |
| Required logarithmic running | [ChallengeSpec.lean:13](../../ChallengeSpec.lean#L13): `C.beta N p / Real.log (C.mesh N)⁻¹` tends uniformly to a positive slope | This clause must be replaced below four dimensions. |
| Internal reference trajectory | [YM/RG/History.lean:79](../../YM/RG/History.lean#L79): `hatBeta = bar + G.slopeConstant * scale`; [YM/Lattice/Scale.lean:115](../../YM/Lattice/Scale.lean#L115): `scale = log (a⁻¹)` | The induction is organized around logarithmic growth, rather than a dimension-independent small-coupling hypothesis. |
| Actual RG recurrence | [YM/RG/History.lean:223](../../YM/RG/History.lean#L223) bounds `β(m+1) - β(m) - slopeConstant * log(block)`; [YM/Gauge/Colors.lean:184](../../YM/Gauge/Colors.lean#L184) sets the slope to `11 * casimir / (24 * pi^2)` | Below D=4 the leading tree scaling is multiplicative. Keeping this recurrence would describe the wrong continuum scaling. |
| Free-field grading | [YM/Next/MAXWELL/Algebra.lean:20](../../YM/Next/MAXWELL/Algebra.lean#L20): `scaleW v := v.1 + 2` | A curvature with j derivatives receives weight j+2. Geometric grading and canonical scaling dimension must be distinguished below D=4. |
| Maxwell stress tensor | [YM/Next/MAXWELL/Stress.lean:24](../../YM/Next/MAXWELL/Stress.lean#L24): `sheetEnergy a b - (kr a b * (1/4)) • sum ...`; its conservation is proved at line 76 | The physical 1/4 stays fixed. Its trace cancels only when there are four axes. |
| Trace field and non-freeness endpoint | [ChallengeSpec.lean:48](../../ChallengeSpec.lean#L48): `centeredTrace : Field 4`; [ChallengeSpec.lean:168](../../ChallengeSpec.lean#L168) requires r^8 log²(1/r) times its two-point function to tend to 3 dim(g)/pi^4 > 0 | Neither the logarithmic trace law nor this non-freeness test transfers unchanged to D=3,2,1. |

Some numerals are unrelated to spacetime dimension. For example,
`Coeff := Fin 4` in
[YM/Push/STRESS_FLUX/Polynomial.lean:174](../../YM/Push/STRESS_FLUX/Polynomial.lean#L174)
indexes four tensor coefficients, explicitly listed in the following comment.
Replacing every `Fin 4`, degree four, or exponent four would therefore be
incorrect.

## 2. The ultraviolet simplification: powers replace logarithms

The following is dimensional analysis, not a theorem extracted from the Lean
construction. Use the connection convention
F = dA + A∧A and S = (1/(4g_D²)) integral |F|². Then [A]=mass,
[F]=mass², and [g_D²]=mass^(4−D). Expanding a small plaquette gives an
energy of order a^4 |F|²; summing over sites gives a^(4−D) integral |F|².
Matching the continuum action therefore requires

    beta(a) ~ c_G / (g_D² a^(4−D)),       D < 4,

where c_G depends on the matrix-trace convention. This is leading scaling
at fixed dimensionful coupling; it is not an all-orders matching formula.
In D=4 the tree scaling is constant and the released proof instead tunes
the bare coupling with the logarithmic RG correction in section 1.

| D | Plaquette planes | Leading beta(a) at fixed g_D² | Dimensionless squared coupling g_D² a^(4−D) |
|---|---:|---|---|
| 4 | 6 | Proof's logarithmic running | Renormalized running is needed. |
| 3 | 3 | c_G/(g_3² a) | g_3² a |
| 2 | 1 | c_G/(g_2² a²) | g_2² a² |
| 1 | 0 | The plaquette action is zero; beta is irrelevant. | No plaquette interaction to control. |

For a fixed geometric block factor L>1, the candidate leading trajectory is
beta_(m+1) = L^(4−D) beta_m, plus corrections, instead of the additive
logarithmic recurrence. In the same normalization, beta^(-1/2) decays as
a^(1/2) in D=3 and as a in D=2, rather than as log(1/a)^(-1/2).
A geometrically spaced sequence makes positive powers of a summable.
This is a reason to expect simpler ultraviolet estimates; it does not
establish the required polymer, gauge-fixing, or observable estimates.

Power counting gives a second way to see the improvement. For an ordinary
connected pure-gauge perturbative graph with E external legs and ell loops,
let V3,V4 be its cubic and quartic vertex counts and I its internal-line
count. A cubic vertex contributes at most one momentum power, so

    omega <= D ell − 2I + V3
    ell = I − V3 − V4 + 1,
    3V3 + 4V4 = 2I + E,
    omega <= 4 − E + (D−4) ell.

Thus in D=3 each added loop lowers the superficial divergence by one; in
D=2 it lowers it by two. At fixed external content only finitely many loop
orders can be superficially divergent. Gauge identities can improve these
bounds. Composite insertions have additional dimensions and require a
separate count; this argument does not bound all insertions at once.

## 3. A substantive obstruction: the stress trace

Let Q_ab = sum_i <F_ai,F_bi> and R = sum_a Q_aa. In the normalization of
the source's Maxwell tensor, suppressing its overall coupling factor,

    T_ab = Q_ab − (1/4) delta_ab R,
    sum_a T_aa = (1 − D/4) R.

The probe proves the second identity for arbitrary diagonal contractions.
The coefficients are zero in D=4, 1/4 in D=3, and 1/2 in D=2. The
four-dimensional quantum trace test starts from a classically traceless
free tensor; in lower dimensions the classical tensor already has a trace.
That changes the meaning of a trace-based non-freeness test.

Changing 1/4 to 1/D would force an algebraic trace cancellation but would
change the physical Maxwell stress tensor. In particular, conservation of
the altered tensor would need a new argument and generally fails for a
nonconstant R. This is a mathematical obstruction to a global replacement
of four by D, beyond the changes in coordinates and volume powers.

The distinction also affects grades. In the connection convention, F² has
geometric grade four for every D, while F²/g_D² has physical dimension D.
In canonical normalization the free curvature itself has dimension D/2.
One must either retain geometric grades and track powers of g_D, or change
the grading and scaling estimates together. The public `Field 4` should
not simply be renamed `Field D` without choosing that convention.

## 4. D=3: retain a construction, simplify its ultraviolet part

There are three curvature components, which can be written
B_i = (1/2) epsilon_ijk F_jk. Algebraically,
Q_ab = delta_ab |B|² − <B_a,B_b>. Unlike in D=2, this still allows a
nonzero traceless part of the stress tensor. The Bianchi identity gives
the covariant constraint sum_i D_i B_i=0: the dual field is not an
unconstrained free scalar.

The proposed adaptation retains the Wilson measure, local observables,
reflection positivity, compactness and reconstruction strategy, with new
dimension parameters. Its ultraviolet estimates would use the trajectory
and power counting of section 2. The logarithmic beta condition and the
positive logarithmic trace-amplitude test must be replaced. Finite-volume
infrared modes, uniform observable bounds and the continuum limit remain
construction obligations; ultraviolet power counting alone proves none of
them. No D=3 mass-gap conclusion follows from this analysis.

## 5. D=2: replace the multiscale construction by exact face integration

The heat-kernel construction uses the product of p_(g_2² area(f))(U_f)
over faces, with Haar integration over edges. Integrating an edge that
splits one face into two uses p_t * p_s = p_(t+s); the resulting measure
is exactly consistent under subdivision. On the plane or disk the lasso
holonomies of the faces are independent. On a closed surface global
relations remain. These are retrieved facts from
[Lévy, arXiv:1912.06246v1, §§1.4.2–1.4.5, Theorem 1.4 and Proposition 1.7](https://arxiv.org/pdf/1912.06246v1),
not new results of this review.

The heat-kernel semigroup could replace the polymer RG construction for a
holonomy-based target. The original exponential Wilson plaquette weight is not itself
this heat kernel: retaining that exact starting action requires a
Wilson-to-heat-kernel limit argument. Exact subdivision consistency does
not supply it automatically. Matching the submission's local-field, contact
and reconstruction conclusions is also a separate task.

A local classical calculation explains part of the simplification. There
is one curvature component B=F_12. Then Q_11=Q_22=|B|² and Q_12=0, so
T_ab=(1/2) delta_ab |B|² in the normalization of section 3. In a local
axial gauge A_1=0, F_12=partial_1 A_2, and the curvature action is
quadratic. Gauge fixing globally and imposing boundary or torus data are
additional issues; this local calculation does not remove them. The
four-dimensional positive trace-amplitude requirement cannot be imposed
as the definition of the two-dimensional theory.

## 6. D=1: the plaquette construction collapses exactly

There are no ordered pairs i<j in Fin 1. Consequently the generalized
Wilson energy is an empty sum, equal to zero for every configuration.
The exponential density equals one, its partition function equals one
for a probability Haar prior, and the Wilson law is precisely that prior,
independently of beta. These statements are proved in the probe.

On a circle a global holonomy may remain; zero local curvature does not
eliminate it. On a contractible interval all link variables can be removed
by vertex gauge transformations when endpoints are unrestricted. Also,
genuine one-dimensional pure gauge theory differs from reducing the
four-dimensional theory while retaining its other three gauge components:
the latter keeps adjoint scalar matrices and their interactions.

## 7. Formal deliverable and verification limits

[VariationDimension.lean](../lean/VariationDimension.lean) contains:

- Dimension-parametric sites, configurations, plaquettes, Wilson energy and law.
- Site count l^D and plaquette-plane counts 6,3,1,0.
- Definitional agreement with the submission's energy and law at D=4.
- Vanishing energy and exact product-prior law at D=1 for probability Haar input.
- The generic stress-trace contraction and its D=4,3,2 specializations.

The file imports only `PublicWilson`; it does not import the solution or
use the four-dimensional existence theorem. All fourteen printed theorem
axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
The compile record is [52-variation-dimension.log](../logs/52-variation-dimension.log).
The D=4 equalities establish compatibility of definitions. The
kernel proofs certify the stated finite-lattice and contraction identities;
the continuum adaptations above remain proposals.

Run from the submission directory with its built dependencies:

```sh
lake env lean independent-review/lean/VariationDimension.lean
```
