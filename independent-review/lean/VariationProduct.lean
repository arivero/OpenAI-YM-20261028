import Mathlib

/-! Variation written for the independent review (not part of the submission).

Notes 2 and 3: product gauge groups. For block-diagonal link matrices the plaquette is
block diagonal and the Wilson energy density of the single-trace action splits into the
energy densities of the two blocks, with weights `m₁/(m₁+m₂)` and `m₂/(m₁+m₂)`. A single
coupling β therefore gives the two factors couplings in the fixed ratio `m₁ : m₂`, and
two logarithmic slopes can both be met only if they stand in that same ratio. Whether
the asymptotic-freedom slopes of two given factors stand in that ratio is a separate
computation, left to the prose: by the one-loop values of Note 2 it holds for
SU(m₁)×SU(m₂) exactly when `m₁ = m₂`.

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

#print axioms ReviewProduct.block_mul
#print axioms ReviewProduct.energy_split
#print axioms ReviewProduct.slope_ratio
