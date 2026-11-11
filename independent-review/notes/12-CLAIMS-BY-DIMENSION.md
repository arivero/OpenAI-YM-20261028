# What can be claimed in dimensions above four, four, three, two and one

**Independent explanatory note by gpt-6-astra.** D denotes total
Euclidean spacetime dimension. After continuation of one coordinate to real
time, the corresponding spacetime has D−1 spatial dimensions. Thus D=1
means quantum mechanics in 0+1 dimensions; one spatial dimension means D=2.
Units are chosen so that ħ=c=1.

The released construction fixes D=4. The other dimensions below combine
elementary deductions, established constructions cited at their point of
use, and proposed adaptations. They are not corollaries of the released
existence theorem. [Note 11](11-LOWER-DIMENSIONS.md) gives the source locations
and the finite-lattice Lean probe.

| Total D | Pure Yang–Mills: defensible claim | Matter and quantum dynamics | What this release establishes |
|---|---|---|---|
| **D>4** | Negative mass dimension of the coupling; perturbative nonrenormalizability about the Gaussian theory. A cutoff effective theory remains meaningful. This does not prove nonexistence of every possible ultraviolet completion. | Free massive scalar fields exist; interacting extensions require their own construction and ultraviolet assumptions. | No theorem in these dimensions. |
| **4** | The submitted theorem constructs a Wilson continuum hierarchy and a selected Wightman phase with the specified OPE and trace test. A positive mass gap is outside its statement. | Coupling dynamical matter changes the theory and the construction problem. | The dimension actually covered by the theorem. |
| **3** | Superrenormalizable ultraviolet power counting makes a construction more tractable. It does not by itself construct the continuum measure, its observables, or a mass gap. | Relativistic fields and their couplings can be formulated in 2+1 dimensions; existence claims remain model-specific. | No D=3 continuum theorem follows by substituting three for four. |
| **2** | Pure Yang–Mills has an exact heat-kernel/holonomy construction. Absence of local propagating gauge waves is compatible with nontrivial loop observables. | Adding matter permits local dynamics and generally removes the pure-gauge exact simplification. | The heat-kernel theory is a separate construction, not a specialization of the release. |
| **1** | Curvature and the pure plaquette action vanish. The finite-lattice Wilson law is product Haar measure, with possible global circle holonomy. | Suitable Euclidean scalar or matrix systems reconstruct quantum mechanics. The massive Klein–Gordon example reconstructs a harmonic oscillator. | The empty-action statement is proved in our probe; the quantum-mechanical examples below are separate elementary constructions. |

## Coupling dimensions and the ultraviolet distinction

In the connection convention,

$$
 F=dA+A\wedge A,\qquad
 S_E=\frac{1}{4g_D^2}\int d^Dx\sum_{\mu,\nu}
                  \langle F_{\mu\nu},F_{\mu\nu}\rangle,
 \qquad [g_D^2]=\mathrm{mass}^{4-D}.
$$

Here the Lie-algebra inner product is positive. The dimensionless coupling
at energy μ is $\lambda(\mu)=g_D^2\mu^{D-4}$. At fixed dimensionful
coupling it grows towards short distances for D>4 and decreases for D<4.
At D=4 its quantum running controls the ultraviolet behavior. These are
engineering dimensions; they do not determine a nonperturbative flow near
a hypothetical interacting fixed point.

For D>4, increasing loop order permits increasingly divergent amplitudes
and higher-dimension counterterms. A finite collection of classical
Yang–Mills parameters therefore does not suffice for perturbative
renormalization around the free theory. Effective field theory instead
organizes these operators at a fixed accuracy below a cutoff. Establishing
an interacting ultraviolet fixed point, or another completion, would be
an additional result. The stronger assertion that all higher-dimensional
continuum theories are impossible is unsupported by this argument. This
qualifies the broad wording about D>4 in Note 5.

For D=3 and D=2, the leading Wilson scaling at fixed physical coupling is
$\beta(a)\sim c_G/(g_D^2a^{4-D})$, where $c_G$ depends on trace
normalization. Thus the expected small parameter $\beta^{-1/2}$ decays
as $a^{1/2}$ or $a$, respectively. The released proof instead uses a
logarithmic trajectory in
[History.lean, lines 79 and 223–230](../../YM/RG/History.lean).
Replacing that trajectory requires new estimates, even when power counting
suggests better convergence.

## D=4: existence with the stated scope

The public statement selects a Wilson lattice family, takes the mesh limit
and a subsequential large-volume limit, and reconstructs a selected phase.
Its conclusions include Wightman properties, an all-orders separated OPE,
and a specific short-distance trace law excluding the stated finite Wick
profiles. The detailed construction supplies additional field identification
and contact information. These claims are stated in the
[submission README, “The public challenge” and “The detailed construction theorem”](../../README.md)
and [ChallengeSpec.lean, lines 168–188](../../ChallengeSpec.lean).

The README explicitly says: “A positive mass gap, general exclusion of
continuous-mass generalized free fields and all-orders MS-bar matching are
outside its scope.” The theorem also allows subsequence and phase choices;
it does not establish uniqueness of the entire infinite-volume limit.
This note reports the scope of that release, without extending its theorem
to matter or repeating its full kernel audit.

Four dimensions also enter the stress argument. With
$Q_{\mu\nu}=\sum_\rho\langle F_{\mu\rho},F_{\nu\rho}\rangle$, the
classical tensor proportional to $Q_{\mu\nu}-\delta_{\mu\nu}\operatorname{tr}Q/4$
has trace $(1-D/4)\operatorname{tr}Q$. The trace vanishes at D=4 before
quantum corrections. In lower dimensions the classical contribution must
already be accounted for. Keeping the four-dimensional logarithmic trace
test would therefore impose the wrong target.

## D=3: simpler ultraviolet behavior still leaves a construction problem

For a connected pure-gauge perturbative graph with E external legs and
ell loops, cubic vertices carrying at most one derivative give the
superficial bound

$$
 \omega\leq 4-E+(D-4)\ell.
$$

At D=3 each additional loop lowers the bound by one. At fixed external
content only finitely many loop orders can be superficially divergent;
composite insertions require their own counting. This explains
superrenormalizability and motivates adapting the ultraviolet part of the
construction. Uniform bounds, gauge symmetry, the infrared limit and
reconstruction remain separate requirements.

A concrete distinction in the literature is between stochastic dynamics
and their invariant measure. Chevyrev's 2022 review describes renormalized
gauge-covariant stochastic Yang–Mills dynamics, while §4 asks whether the
process possesses an invariant measure; §1.1 also distinguishes ultraviolet
stability from a construction of the three-dimensional measure. These are
statements about that source's results and open questions, rather than a
complete census of later work.
[Source: arXiv:2202.13359v2, §§1.1, 1.3 and 4](https://arxiv.org/pdf/2202.13359v2).

The claim supported by our repository analysis is consequently a proposed
route to simpler ultraviolet estimates, with no D=3 continuum existence
or mass-gap theorem established here.

## D=2: exact holonomies and the meaning of a gap

For compact G, face weights $p_{g_2^2|f|}(U_f)$ obey exact subdivision
consistency through $p_s*p_t=p_{s+t}$. Lévy's Theorems 1.4 and 1.6 give
consistency and continuum holonomy existence.
[Source: arXiv:1912.06246v1, §§1.4.2–1.4.5](https://arxiv.org/pdf/1912.06246v1).

On a spatial circle of circumference L, the heat-kernel generator gives,
in the convention
$\partial_s p_s=\Delta_Gp_s/2$,

$$
 H=-\frac{g_2^2L}{2}\Delta_G
 \quad\hbox{on class functions on }G,\qquad
 E_R=\frac{g_2^2L}{2}C_2(R).
$$

This is a deduction from cylinder area Lτ and Lévy's character expansion,
equation (17). For connected compact G with nontrivial representations,
the smallest nonzero Casimir gives a finite-circle gap for global
electric-flux states. It does not identify an infinite-line particle mass.

Retaining the exponential Wilson action requires a matching limit argument.
Adding matter requires a separate construction of the coupled theory.

## D=1: Wick rotation reconstructs quantum mechanics

With one Euclidean coordinate τ, there are no spatial coordinates left
after Wick rotation. For a quantum system with a self-adjoint Hamiltonian
bounded below, shift its lower bound to zero. Euclidean evolution is the
semigroup $e^{-\tau H}$; its real-time counterpart is the unitary group
$e^{-itH}$. Conversely, Euclidean correlation functions satisfying the
appropriate reflection-positivity and regularity assumptions reconstruct
a Hilbert space and Hamiltonian. This is the precise content of saying
that a one-dimensional Euclidean theory “rotates to quantum mechanics.”
The continuation requires those assumptions; an arbitrary Euclidean
weight does not automatically supply them. In 0+1 dimensions there are
no spatial translations or Lorentz boosts to reconstruct.

For a real scalar with m>0, the quadratic action corresponds to the
centered Gaussian process with covariance C_m:

$$
 S_E[q]=\frac12\int_{\mathbb R}
       \big((\partial_\tau q)^2+m^2q^2\big)\,d\tau,
 \qquad C_m(\tau)=\frac{e^{-m|\tau|}}{2m}.
$$

These formulas can be checked directly. Away from zero,
$(-\partial_\tau^2+m^2)C_m=0$; the derivative jump at zero is −1,
so distributionally $(-\partial_\tau^2+m^2)C_m=\delta_0$.
For a smooth test f supported at positive times,

$$
 \int_0^\infty\!\int_0^\infty
 \overline{f(\tau)}C_m(\tau+\sigma)f(\sigma)\,d\tau d\sigma
 =\frac1{2m}\left|\int_0^\infty e^{-m\tau}f(\tau)\,d\tau\right|^2\geq0.
$$

The Gaussian theory therefore has the required covariance positivity.
Its reconstruction is the harmonic oscillator,

$$
 H=\tfrac12(p^2+m^2q^2),\qquad E_n=m(n+\tfrac12),
 \qquad \ddot q+m^2q=0.
$$

After subtracting the vacuum energy, the excitation gap is m. The
Heisenberg equation is the Klein–Gordon equation with no spatial
derivatives. This checks the covariance normalization as well:
$|\langle0|q|1\rangle|^2=1/(2m)$ and $E_1-E_0=m$ reproduce
$C_m$. This elementary example is not a new Lean theorem. Quantum
mechanics is not automatically gapped: the free particle on the line has
continuous spectrum reaching zero and no normalizable ground state.

One-dimensional pure Yang–Mills has a different field content. Its only
curvature component is F_00=0, and its plaquette index set is empty. Our
[VariationDimension.lean](../lean/VariationDimension.lean), theorems
`energy_one` and `law_one`, proves zero Wilson energy and product Haar law.
The [compile record](../logs/52-variation-dimension.log) belongs to that
finite-lattice statement. Global circle holonomy can survive; there is no
local gauge oscillator from the pure curvature action.

A complex scalar instead has a covariant derivative
$D_t\phi=(\partial_t+iqA_0)\phi$ and a nonzero matter action. A dynamical
A_0 imposes a Gauss constraint without needing a curvature kinetic term.
An external A_0 can be removed locally on an interval, subject to boundary
conditions; circle holonomy need not be removable. Thus a vanishing pure
gauge action does not eliminate quantum dynamics with matter.

Dimensional reduction of four-dimensional Yang–Mills retains still more
variables: $X_i(t)=A_i(t)$, i=1,2,3. Using a positive invariant inner
product, its Euclidean action has the form

$$
 S_E=\frac1{g_{\rm QM}^2}\int d\tau\left[
 \frac12\sum_i\|D_\tau X_i\|^2+
 \frac14\sum_{i,j}\|[X_i,X_j]\|^2\right].
$$

This follows from $F_{0i}=D_\tau X_i$ and
$F_{ij}=[X_i,X_j]$ when spatial derivatives vanish. It is interacting
matrix quantum mechanics with a gauge constraint. Its existence and
spectrum depend on the precise model and constraints; the reduction alone
does not prove a gap. A one-dimensional particle worldline embedded in
higher-dimensional spacetime is a third use of “one-dimensional”: the
background fields still live in that higher-dimensional spacetime.

## Claims that survive the comparison

Free massive Klein–Gordon fields provide quantum theories in every finite
spacetime dimension under discussion. Their existence does not settle
interacting Yang–Mills. Minimal coupling writes a candidate charged-field
equation; it is not by itself a construction of the jointly quantized
matter and gauge system.

For the present release, D=4 is the proved target with its stated spectral
limits. D=3 suggests a simpler but unfinished adaptation; D=2 supplies a
separate exact holonomy construction; D=1 supplies both an exact pure-gauge
degeneracy and explicit nontrivial quantum-mechanical benchmarks once
matter or reduced matrix variables are retained. D>4 requires additional
ultraviolet input beyond the released argument.
