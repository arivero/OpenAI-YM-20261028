import ChallengeSpec
import YM.Gauge.Lie

/-! Variation written for the independent review (not part of the submission).

Charge quantization for S(U(3)×U(1)) ⊂ SU(4) (Note 7). The U(1) subgroup generated
by `Z = i·diag(1,1,1,-3)` contains the centre of SU(3): at the parameter `2π/3` the
one-parameter group passes through `diag(ω, ω, ω, 1)` with `ω = exp(2πi/3)`.
A state of U(1) charge `q` and SU(3) triality `t` sees this element as `ω^q` and as
`ω^t`, so `q ≡ t (mod 3)`. Colour singlets therefore have charge divisible by 3. -/
set_option autoImplicit false
noncomputable section
namespace ReviewCharge
open Matrix NormedSpace

private abbrev M := Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℂ

/-- The real charges (1,1,1,-3). -/
def dr : Fin (3 + 1) → ℝ := ![1, 1, 1, -3]

/-- i·diag(1,1,1,-3), the generator of the U(1) factor (as in `BrokenSU4Probe.lean`). -/
def Z : M := Matrix.diagonal fun i => (dr i : ℂ) * Complex.I

/-- The primitive cube root of unity. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

private def phase (t : ℝ) : Fin (3 + 1) → ℂ :=
  fun i => Complex.exp (((t * dr i : ℝ) : ℂ) * Complex.I)

private lemma exp_smul_Z (t : ℝ) : exp (t • Z) = Matrix.diagonal (phase t) := by
  have h : t • Z = Matrix.diagonal fun i => ((t * dr i : ℝ) : ℂ) * Complex.I := by
    unfold Z
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [h, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  simp only [phase, Complex.exp_eq_exp_ℂ]

/-- The U(1) subgroup passes through the generator of the centre of SU(3). -/
theorem centre_in_U1 :
    exp ((2 * Real.pi / 3 : ℝ) • Z) = Matrix.diagonal ![omega, omega, omega, 1] := by
  rw [exp_smul_Z]
  congr 1
  funext i
  have h1 : Complex.exp ((((2 * Real.pi / 3 * 1 : ℝ)) : ℂ) * Complex.I) = omega := by
    unfold omega
    congr 1
    push_cast
    ring
  have h3 : Complex.exp ((((2 * Real.pi / 3 * (-3) : ℝ)) : ℂ) * Complex.I) = 1 := by
    have e : (((2 * Real.pi / 3 * (-3) : ℝ)) : ℂ) * Complex.I = -(2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  fin_cases i
  · simpa [phase, dr] using h1
  · simpa [phase, dr] using h1
  · simpa [phase, dr] using h1
  · simpa [phase, dr] using h3

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [omega] using h

/-- Charge and triality agree modulo 3. -/
theorem charge_congruence (q t : ℤ) (h : omega ^ q = omega ^ t) : (3 : ℤ) ∣ q - t := by
  have h0 : omega ≠ 0 := omega_isPrimitiveRoot.ne_zero (by norm_num)
  have h1 : omega ^ (q - t) = 1 := by
    rw [zpow_sub₀ h0, h, div_self (zpow_ne_zero t h0)]
  exact_mod_cast (omega_isPrimitiveRoot.zpow_eq_one_iff_dvd (q - t)).mp h1

/-- A colour singlet (triality zero) has U(1) charge divisible by 3. -/
theorem singlet_charge (q : ℤ) (h : omega ^ q = 1) : (3 : ℤ) ∣ q := by
  have := charge_congruence q 0 (by simpa using h)
  simpa using this

end ReviewCharge


/-! Probe written for the independent review (not part of the submission).

The group S(U(3)×U(1)), realized as the elements of SU(4) that commute with
diag(1,1,1,-3), is a legitimate `GaugeGroup` of the public statement, and it
fails the hypothesis `IsSimple`: its Lie algebra contains the nonzero central
element i·diag(1,1,1,-3). This is the unbroken subgroup of SU(4) for an adjoint
vacuum value along diag(1,1,1,-3). -/
set_option autoImplicit false
noncomputable section
namespace ReviewBrokenSU4
open YM Matrix NormedSpace Function
open scoped Matrix.Norms.Frobenius

private abbrev M := Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℂ

/-- The real charges (1,1,1,-3). -/
def dr : Fin (3 + 1) → ℝ := ![1, 1, 1, -3]

/-- diag(1,1,1,-3). -/
def D : M := Matrix.diagonal fun i => (dr i : ℂ)

/-- i·diag(1,1,1,-3), the generator of the U(1) factor. -/
def Z : M := Matrix.diagonal fun i => (dr i : ℂ) * Complex.I

/-- S(U(3)×U(1)): the elements of SU(4) commuting with `D`. -/
abbrev SU3U1 : Gauge where
  n := 3
  imageGroup := {
    carrier := {X | X.val.det = 1 ∧ X.val * D = D * X.val}
    one_mem' := ⟨Matrix.det_one, by simp⟩
    mul_mem' {X Y} hx hy := by
      refine ⟨?_, ?_⟩
      · change (X.val * Y.val).det = 1
        rw [Matrix.det_mul, hx.1, hy.1, mul_one]
      · change X.val * Y.val * D = D * (X.val * Y.val)
        rw [mul_assoc, hy.2, ← mul_assoc, hx.2, mul_assoc]
    inv_mem' {X} hx := by
      have h1 : star X.val * X.val = 1 := Matrix.mem_unitaryGroup_iff'.mp X.property
      have h2 : X.val * star X.val = 1 := Matrix.mem_unitaryGroup_iff.mp X.property
      refine ⟨?_, ?_⟩
      · change (star X.val).det = 1
        rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx.1, star_one]
      · change star X.val * D = D * star X.val
        calc star X.val * D = star X.val * D * (X.val * star X.val) := by rw [h2, mul_one]
          _ = star X.val * (D * X.val) * star X.val := by simp only [mul_assoc]
          _ = star X.val * (X.val * D) * star X.val := by rw [hx.2]
          _ = (star X.val * X.val) * D * star X.val := by simp only [mul_assoc]
          _ = D * star X.val := by rw [h1, one_mul] }
  closed_imageGroup := by
    have h1 : IsClosed {X : GaugeU 3 | X.val.det = 1} :=
      isClosed_eq (show Continuous fun X : GaugeU 3 => X.val.det from by fun_prop) continuous_const
    have h2 : IsClosed {X : GaugeU 3 | X.val * D = D * X.val} :=
      isClosed_eq (show Continuous fun X : GaugeU 3 => X.val * D from by fun_prop)
        (show Continuous fun X : GaugeU 3 => D * X.val from by fun_prop)
    exact h1.inter h2

/-- The same group as a gauge group of the public statement. -/
abbrev su3u1 : YangMills.GaugeGroup :=
  ⟨SU3U1.n, SU3U1.imageGroup, SU3U1.closed_imageGroup, SU3U1.lie, fun _ => Iff.rfl⟩

/-- The one-parameter group generated by `Z`. -/
private def phase (t : ℝ) : Fin (3 + 1) → ℂ := fun i => Complex.exp (((t * dr i : ℝ) : ℂ) * Complex.I)

private lemma exp_smul_Z (t : ℝ) : exp (t • Z) = Matrix.diagonal (phase t) := by
  have h : t • Z = Matrix.diagonal fun i => ((t * dr i : ℝ) : ℂ) * Complex.I := by
    unfold Z
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [h, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  simp only [phase, Complex.exp_eq_exp_ℂ]

private lemma phase_norm (t : ℝ) (i : Fin (3 + 1)) : phase t i * star (phase t i) = 1 := by
  have h : ‖phase t i‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

private lemma phase_prod (t : ℝ) : ∏ i, phase t i = 1 := by
  unfold phase
  rw [← Complex.exp_sum, Fin.sum_univ_four]
  have : (((t * dr 0 : ℝ) : ℂ) * Complex.I + ((t * dr 1 : ℝ) : ℂ) * Complex.I +
      ((t * dr 2 : ℝ) : ℂ) * Complex.I + ((t * dr 3 : ℝ) : ℂ) * Complex.I) = 0 := by
    simp [dr]
    ring
  rw [this, Complex.exp_zero]

/-- `Z` generates a one-parameter subgroup of S(U(3)×U(1)). -/
theorem Z_mem : Z ∈ SU3U1.lie := by
  intro t
  have hu : Matrix.diagonal (phase t) ∈ Matrix.unitaryGroup (Fin (3 + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact phase_norm t i
  have hd : (Matrix.diagonal (phase t)).det = 1 := by
    rw [Matrix.det_diagonal]; exact phase_prod t
  have hc : Matrix.diagonal (phase t) * D = D * Matrix.diagonal (phase t) := by
    unfold D
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  exact ⟨⟨⟨Matrix.diagonal (phase t), hu⟩, ⟨hd, hc⟩⟩, (exp_smul_Z t).symm⟩

theorem Z_ne : Z ≠ 0 := by
  intro h
  have h0 := congr_fun (congr_fun h 0) 0
  simp [Z, dr] at h0

/-- Every element of the Lie algebra commutes with `D`. -/
theorem commutes_D {X : M} (hX : X ∈ SU3U1.lie) : X * D = D * X := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using! hasDerivAt_exp_smul_const X (0 : ℝ)
  have h1 : HasDerivAt (fun t : ℝ => exp (t • X) * D) (X * D) 0 := hd.mul_const D
  have h2 : HasDerivAt (fun t : ℝ => D * exp (t • X)) (D * X) 0 := hd.const_mul D
  have he : (fun t : ℝ => exp (t • X) * D) = fun t : ℝ => D * exp (t • X) := by
    funext t
    obtain ⟨u, hu⟩ := hX t
    calc exp (t • X) * D = SU3U1.mat u * D := congrArg (fun A : M => A * D) hu.symm
      _ = D * SU3U1.mat u := u.property.2
      _ = D * exp (t • X) := congrArg (fun A : M => D * A) hu
  rw [he] at h1
  exact h1.unique h2

/-- `Z` is central in the Lie algebra. -/
theorem Z_central {X : M} (hX : X ∈ SU3U1.lie) : X * Z - Z * X = 0 := by
  have hZ : Z = Complex.I • D := by
    unfold Z D
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp [mul_comm]
  rw [hZ, mul_smul_comm, smul_mul_assoc, commutes_D hX, sub_self]

/-- S(U(3)×U(1)) fails the hypothesis of `YangMills.JointExistence`. -/
theorem not_simple : ¬ su3u1.IsSimple := by
  rintro ⟨⟨X, hX, Y, hY, hne⟩, hideal⟩
  have hle : Submodule.span ℝ {Z} ≤ su3u1.lieAlgebra := by
    rw [Submodule.span_le]
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    exact Z_mem
  have hid : ∀ X ∈ su3u1.lieAlgebra, ∀ Y ∈ Submodule.span ℝ {Z},
      X * Y - Y * X ∈ Submodule.span ℝ {Z} := by
    intro X hX Y hY
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hY
    have h1 : X * (c • Z) - (c • Z) * X = c • (X * Z - Z * X) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [h1, Z_central hX, smul_zero]
    exact Submodule.zero_mem _
  rcases hideal _ hle hid with h | h
  · apply Z_ne
    have hmem : Z ∈ Submodule.span ℝ {Z} := Submodule.mem_span_singleton_self Z
    rw [h] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  · have hX' : X ∈ Submodule.span ℝ {Z} := by rw [h]; exact hX
    have hY' : Y ∈ Submodule.span ℝ {Z} := by rw [h]; exact hY
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hX'
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hY'
    apply hne
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_comm a b, sub_self]

/-- SU(4) in its defining representation: determinant one in U(4). -/
abbrev SU4 : Gauge where
  n := 3
  imageGroup := {
    carrier := {X | X.val.det = 1}
    one_mem' := Matrix.det_one
    mul_mem' {X Y} hx hy := by
      change (X.val * Y.val).det = 1
      rw [Matrix.det_mul, hx, hy, mul_one]
    inv_mem' {X} hx := by
      change (star X.val).det = 1
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one] }
  closed_imageGroup := isClosed_eq (show Continuous fun X : GaugeU 3 => X.val.det from by fun_prop)
    continuous_const

/-- S(U(3)×U(1)) is a subgroup of SU(4): the hypothesis `IsSimple` is lost on passing
to this subgroup. -/
theorem su3u1_le_su4 : SU3U1.imageGroup ≤ SU4.imageGroup := fun _ hX => hX.1

/-- The Lie algebra of S(U(3)×U(1)) sits inside that of SU(4). -/
theorem lie_le : SU3U1.lie ≤ SU4.lie := by
  intro X hX t
  obtain ⟨u, hu⟩ := hX t
  exact ⟨⟨u.val, su3u1_le_su4 u.property⟩, hu⟩

end ReviewBrokenSU4



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


/-! Variation written for the independent review (not part of the submission).

Notes 2 and 3: product gauge groups. For block-diagonal link matrices the plaquette is
block diagonal and the Wilson energy density of the single-trace action splits into the
energy densities of the two blocks, with weights `m₁/(m₁+m₂)` and `m₂/(m₁+m₂)`. A single
coupling β therefore gives the two factors couplings in the fixed ratio `m₁ : m₂`, and
two logarithmic slopes can both be met only if they stand in that same ratio. This is
the algebra behind the statement that a product group needs one coupling per factor.

The file is pure matrix algebra and analysis; it does not use the submission. -/
set_option autoImplicit false
noncomputable section
namespace ReviewProduct
open Matrix Filter Topology

variable {m₁ m₂ : ℕ}

/-- Block-diagonal matrices multiply blockwise: plaquettes of block-diagonal links are
block diagonal. -/
theorem block_mul (A₁ B₁ : Matrix (Fin m₁) (Fin m₁) ℂ) (A₂ B₂ : Matrix (Fin m₂) (Fin m₂) ℂ) :
    Matrix.fromBlocks A₁ 0 0 A₂ * Matrix.fromBlocks B₁ 0 0 B₂ =
      Matrix.fromBlocks (A₁ * B₁) 0 0 (A₂ * B₂) := by
  simp [Matrix.fromBlocks_multiply]

/-- The Wilson energy density of a block-diagonal plaquette is the weighted sum of the
energy densities of its blocks. -/
theorem energy_split (P₁ : Matrix (Fin m₁) (Fin m₁) ℂ) (P₂ : Matrix (Fin m₂) (Fin m₂) ℂ)
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    1 - ((Matrix.fromBlocks P₁ 0 0 P₂).trace).re / ((m₁ + m₂ : ℕ) : ℝ) =
      (m₁ : ℝ) / ((m₁ + m₂ : ℕ) : ℝ) * (1 - (P₁.trace).re / (m₁ : ℝ)) +
      (m₂ : ℝ) / ((m₁ + m₂ : ℕ) : ℝ) * (1 - (P₂.trace).re / (m₂ : ℝ)) := by
  have hm₁ : (m₁ : ℝ) ≠ 0 := by positivity
  have hm₂ : (m₂ : ℝ) ≠ 0 := by positivity
  have htr : (Matrix.fromBlocks P₁ 0 0 P₂).trace = P₁.trace + P₂.trace := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [htr, Complex.add_re]
  push_cast
  field_simp
  ring

/-- If one sequence of couplings β, weighted by `w₁` and by `w₂`, follows two logarithmic
laws with slopes `s₁` and `s₂`, the slopes are in the ratio of the weights. -/
theorem slope_ratio (β ℓ : ℕ → ℝ) (w₁ w₂ s₁ s₂ : ℝ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (h₁ : Tendsto (fun N => w₁ * β N / ℓ N) atTop (𝓝 s₁))
    (h₂ : Tendsto (fun N => w₂ * β N / ℓ N) atTop (𝓝 s₂)) :
    s₁ / w₁ = s₂ / w₂ := by
  have a : Tendsto (fun N => β N / ℓ N) atTop (𝓝 (s₁ / w₁)) := by
    refine (h₁.div_const w₁).congr (fun N => ?_)
    field_simp
  have b : Tendsto (fun N => β N / ℓ N) atTop (𝓝 (s₂ / w₂)) := by
    refine (h₂.div_const w₂).congr (fun N => ?_)
    field_simp
  exact tendsto_nhds_unique a b

end ReviewProduct

namespace CopySUN
open YM
open scoped Matrix.Norms.Frobenius
/-- Row and column indices of the defining representation of SU(m+2). -/
abbrev Idx (m : ℕ) := Fin (m + 1 + 1)
abbrev Mat (m : ℕ) := Matrix (Idx m) (Idx m) ℂ

/-- SU(m+2) in its defining representation: determinant one in U(m+2). -/
abbrev SUN (m : ℕ) : Gauge where
  n := m + 1
  imageGroup := {
    carrier := {X | X.val.det = 1}
    one_mem' := Matrix.det_one
    mul_mem' {X Y} hx hy := by
      change (X.val * Y.val).det = 1
      rw [Matrix.det_mul, hx, hy, mul_one]
    inv_mem' {X} hx := by
      change (star X.val).det = 1
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one] }
  closed_imageGroup :=
    isClosed_eq (show Continuous fun X : GaugeU (m + 1) => X.val.det from by fun_prop)
      continuous_const
end CopySUN
namespace CopySU4Skel
open YM
open scoped Matrix.Norms.Frobenius
/-- SU(4) in its defining representation: determinant one in U(4). -/
abbrev SU4 : Gauge where
  n := 3
  imageGroup := {
    carrier := {X | X.val.det = 1}
    one_mem' := Matrix.det_one
    mul_mem' {X Y} hx hy := by
      change (X.val * Y.val).det = 1
      rw [Matrix.det_mul, hx, hy, mul_one]
    inv_mem' {X} hx := by
      change (star X.val).det = 1
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one] }
  closed_imageGroup := isClosed_eq (show Continuous fun X : GaugeU 3 => X.val.det from by fun_prop)
    continuous_const
end CopySU4Skel

/-! ===== Verifier additions ===== -/
-- C: Z and dr of VariationCharge agree with BrokenSU4Probe
example : ReviewCharge.dr = ReviewBrokenSU4.dr := rfl
example : ReviewCharge.Z = ReviewBrokenSU4.Z := rfl
-- the SU(4) of BrokenSU4Probe and of SU4Skeleton is SUN 2 of VariationSUN
example : CopySUN.SUN 2 = ReviewBrokenSU4.SU4 := rfl
example : CopySUN.SUN 2 = CopySU4Skel.SU4 := rfl
-- moment_gaugeAct has exactly the shape of WilsonRegularity.invariant
example {g : YangMills.GaugeGroup} (C : YangMills.WilsonFamily g) (k : ℕ)
    (h : ∀ N p v x U, C.insertion N p v x U = ReviewNetwork.moment k U) :
    ∀ (N p : ℕ) (v : C.Token) (x : YangMills.Site (C.period p * C.denominator N))
      (t : YangMills.Site (C.period p * C.denominator N) → g.image) (U),
      C.insertion N p v x (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) =
        C.insertion N p v x U := by
  intro N p v x t U
  rw [h, h]
  exact ReviewNetwork.moment_gaugeAct k t U
-- slope_ratio: the hypotheses do not exclude ℓ N = 0; check the statement is still consistent
example : (0 : ℝ) / 1 = 0 / 2 :=
  ReviewProduct.slope_ratio (fun _ => 1) (fun _ => 0) 1 2 0 0 one_ne_zero two_ne_zero
    (by simp) (by simp)

#print axioms ReviewCharge.centre_in_U1
#print axioms ReviewCharge.omega_isPrimitiveRoot
#print axioms ReviewCharge.charge_congruence
#print axioms ReviewCharge.singlet_charge
#print axioms ReviewBrokenSU4.Z_mem
#print axioms ReviewBrokenSU4.Z_ne
#print axioms ReviewBrokenSU4.commutes_D
#print axioms ReviewBrokenSU4.Z_central
#print axioms ReviewBrokenSU4.not_simple
#print axioms ReviewBrokenSU4.su3u1_le_su4
#print axioms ReviewBrokenSU4.lie_le
#print axioms ReviewNetwork.hop_star
#print axioms ReviewNetwork.hop_gaugeAct
#print axioms ReviewNetwork.hop_pow_gaugeAct
#print axioms ReviewNetwork.moment_gaugeAct
#print axioms ReviewNetwork.link_gaugeAct
#print axioms ReviewProduct.block_mul
#print axioms ReviewProduct.energy_split
#print axioms ReviewProduct.slope_ratio
