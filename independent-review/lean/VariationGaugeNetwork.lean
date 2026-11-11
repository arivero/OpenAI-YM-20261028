import ChallengeSpec

/-! Variation written for the independent review (not part of the submission).

Note 6, level one: a lattice configuration of the public statement read as a finite
"gauge network". To each configuration `U` we attach a self-adjoint operator `hop U` on
ℓ²(sites) ⊗ ℂ^(n+1), the covariant hopping operator (a discrete Dirac-type operator).
A lattice gauge transformation, in exactly the form used by `WilsonRegularity.invariant`,
acts on it by unitary conjugation. Its spectral moments `Tr (hop U)^k` are therefore
gauge-invariant functions of the configuration.

Left unformalized: the classical hopping expansion that expresses the fourth moment
through the plaquette traces, which is what identifies a spectral action with the
Wilson energy. -/
set_option autoImplicit false
noncomputable section
namespace ReviewNetwork
open YangMills Matrix

variable {g : GaugeGroup} {l : ℕ+}

/-- Matrices acting on the colour space at one site. -/
abbrev Blk (g : GaugeGroup) := Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ

/-- The matrix of a link variable. -/
def link (U : Configuration g l) (x : Site l) (μ : Axis) : Blk g := (U (x, μ)).val.val

/-- The covariant hopping operator, as a matrix over sites with matrix entries. -/
def hop (U : Configuration g l) : Matrix (Site l) (Site l) (Blk g) :=
  Matrix.of fun x y => ∑ μ : Axis,
    ((if y = x + Pi.single μ 1 then link U x μ else 0) +
      (if x = y + Pi.single μ 1 then star (link U y μ) else 0))

/-- A lattice gauge transformation, as in `WilsonRegularity.invariant`. -/
def gaugeAct (t : Site l → g.image) (U : Configuration g l) : Configuration g l :=
  fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹

/-- The block-diagonal unitary of a gauge transformation. -/
def gaugeMat (t : Site l → g.image) : Matrix (Site l) (Site l) (Blk g) :=
  Matrix.diagonal fun x => (t x).val.val

theorem link_gaugeAct (t : Site l → g.image) (U : Configuration g l) (x : Site l) (μ : Axis) :
    link (gaugeAct t U) x μ =
      (t x).val.val * link U x μ * star (t (x + Pi.single μ 1)).val.val := rfl

theorem unitary_right (u : g.image) : u.val.val * star u.val.val = 1 :=
  Matrix.mem_unitaryGroup_iff.mp u.val.property

theorem unitary_left (u : g.image) : star u.val.val * u.val.val = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp u.val.property

/-- The hopping operator is self-adjoint. -/
theorem hop_star (U : Configuration g l) : star (hop U) = hop U := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.star_apply]
  simp only [hop, Matrix.of_apply, star_sum, star_add, apply_ite star, star_star, star_zero]
  apply Finset.sum_congr rfl
  intro μ _
  rw [add_comm]

/-- Gauge transformations act on the hopping operator by conjugation. -/
theorem hop_gaugeAct (t : Site l → g.image) (U : Configuration g l) :
    hop (gaugeAct t U) = gaugeMat t * hop U * star (gaugeMat t) := by
  refine Matrix.ext fun x y => ?_
  rw [gaugeMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp only [hop, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [mul_add, add_mul]
  congr 1
  · by_cases h : y = x + Pi.single μ 1
    · rw [if_pos h, if_pos h, link_gaugeAct, h]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  · by_cases h : x = y + Pi.single μ 1
    · rw [if_pos h, if_pos h, link_gaugeAct, star_mul, star_mul, star_star, h, mul_assoc]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]

theorem gaugeMat_mul_star (t : Site l → g.image) : gaugeMat t * star (gaugeMat t) = 1 := by
  rw [gaugeMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact unitary_right (t x)

theorem star_mul_gaugeMat (t : Site l → g.image) : star (gaugeMat t) * gaugeMat t = 1 := by
  rw [gaugeMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact unitary_left (t x)

/-- Powers of the hopping operator transform by the same conjugation. -/
theorem hop_pow_gaugeAct (t : Site l → g.image) (U : Configuration g l) (k : ℕ) :
    hop (gaugeAct t U) ^ k = gaugeMat t * hop U ^ k * star (gaugeMat t) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, gaugeMat_mul_star]
  | succ k ih =>
    rw [pow_succ, ih, hop_gaugeAct, pow_succ]
    calc gaugeMat t * hop U ^ k * star (gaugeMat t) * (gaugeMat t * hop U * star (gaugeMat t))
        = gaugeMat t * hop U ^ k * (star (gaugeMat t) * gaugeMat t) * hop U * star (gaugeMat t) := by
          simp only [mul_assoc]
      _ = gaugeMat t * (hop U ^ k * hop U) * star (gaugeMat t) := by
          rw [star_mul_gaugeMat, mul_one, mul_assoc (gaugeMat t)]

/-- The spectral moments of the hopping operator: trace over sites and colours of its powers. -/
def moment (k : ℕ) (U : Configuration g l) : ℂ := (Matrix.trace (hop U ^ k)).trace

/-- Spectral moments are gauge invariant, in the sense of `WilsonRegularity.invariant`. -/
theorem moment_gaugeAct (k : ℕ) (t : Site l → g.image) (U : Configuration g l) :
    moment k (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) = moment k U := by
  change moment k (gaugeAct t U) = moment k U
  unfold moment
  rw [hop_pow_gaugeAct]
  unfold Matrix.trace
  rw [gaugeMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp only [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  have h : ∀ x : Site l, Matrix.trace ((t x).val.val * (hop U ^ k) x x * star (t x).val.val) =
      Matrix.trace ((hop U ^ k) x x) := by
    intro x
    rw [Matrix.trace_mul_cycle, unitary_left, one_mul]
  change (∑ x, (t x).val.val * (hop U ^ k) x x * star (t x).val.val).trace =
    (∑ x, (hop U ^ k) x x).trace
  rw [Matrix.trace_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl (fun x _ => h x)

end ReviewNetwork

#print axioms ReviewNetwork.hop_star
#print axioms ReviewNetwork.hop_gaugeAct
#print axioms ReviewNetwork.hop_pow_gaugeAct
#print axioms ReviewNetwork.moment_gaugeAct
