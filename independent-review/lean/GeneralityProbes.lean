import PublicTheory

/-! Probes written for the independent review (not part of the submission).
They import only the public definitions (Mathlib-only closure) and show which
gauge groups the hypothesis `GaugeGroup.IsSimple` of `YangMills.JointExistence`
excludes. -/
set_option autoImplicit false

namespace ReviewGenerality
open YangMills

/-- Probe F. A gauge group whose Lie algebra is abelian fails `IsSimple`.
Covers U(1), tori and finite groups (whose Lie algebra is zero). -/
theorem not_simple_of_abelian (g : GaugeGroup)
    (h : ∀ X ∈ g.lieAlgebra, ∀ Y ∈ g.lieAlgebra, X * Y - Y * X = 0) : ¬ g.IsSimple := by
  rintro ⟨⟨X, hX, Y, hY, hne⟩, -⟩
  exact hne (h X hX Y hY)

/-- Probe G. A nonzero central element of the Lie algebra rules out `IsSimple`.
Covers U(N), S(U(3)×U(1)) and every group with a U(1) factor. -/
theorem not_simple_of_central (g : GaugeGroup)
    (Z : Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ)
    (hZ : Z ∈ g.lieAlgebra) (hZ0 : Z ≠ 0)
    (hc : ∀ X ∈ g.lieAlgebra, X * Z - Z * X = 0) : ¬ g.IsSimple := by
  rintro ⟨⟨X, hX, Y, hY, hne⟩, hideal⟩
  have hle : Submodule.span ℝ {Z} ≤ g.lieAlgebra := by
    rw [Submodule.span_le]
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    exact hZ
  have hid : ∀ X ∈ g.lieAlgebra, ∀ Y ∈ Submodule.span ℝ {Z},
      X * Y - Y * X ∈ Submodule.span ℝ {Z} := by
    intro X hX Y hY
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hY
    have h1 : X * (c • Z) - (c • Z) * X = c • (X * Z - Z * X) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [h1, hc X hX, smul_zero]
    exact Submodule.zero_mem _
  rcases hideal _ hle hid with h | h
  · apply hZ0
    have hmem : Z ∈ Submodule.span ℝ {Z} := Submodule.mem_span_singleton_self Z
    rw [h] at hmem
    simpa using hmem
  · have hX' : X ∈ Submodule.span ℝ {Z} := by rw [h]; exact hX
    have hY' : Y ∈ Submodule.span ℝ {Z} := by rw [h]; exact hY
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hX'
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hY'
    apply hne
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_comm a b, sub_self]

/-- Probe H. A nonzero proper ideal rules out `IsSimple`.
Covers products such as SU(3)×SU(2) and SO(4). -/
theorem not_simple_of_proper_ideal (g : GaugeGroup)
    (I : Submodule ℝ (Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ))
    (hle : I ≤ g.lieAlgebra)
    (hid : ∀ X ∈ g.lieAlgebra, ∀ Y ∈ I, X * Y - Y * X ∈ I)
    (h0 : I ≠ ⊥) (h1 : I ≠ g.lieAlgebra) : ¬ g.IsSimple := by
  rintro ⟨-, hideal⟩
  rcases hideal I hle hid with h | h
  · exact h0 h
  · exact h1 h

end ReviewGenerality

#print axioms ReviewGenerality.not_simple_of_abelian
#print axioms ReviewGenerality.not_simple_of_central
#print axioms ReviewGenerality.not_simple_of_proper_ideal
