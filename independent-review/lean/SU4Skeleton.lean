import Solution
import YM.Gauge.Lie

/-! Skeleton written for the independent review (not part of the submission).

The public theorem applies to SU(4) as soon as a proof of `su4.IsSimple` is
supplied. That proof is the only missing piece; the submission instantiates
SU(2) only (`ConcreteSU2.lean`). -/
set_option autoImplicit false
noncomputable section
namespace ReviewSU4
open YM YangMills
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

/-- SU(4) as a gauge group of the public statement. -/
abbrev su4 : GaugeGroup :=
  ⟨SU4.n, SU4.imageGroup, SU4.closed_imageGroup, SU4.lie, fun _ => Iff.rfl⟩

/-- Conditional instance: the conclusions of the public theorem for SU(4),
given simplicity of su(4). -/
theorem su4Theory (h : su4.IsSimple) : ∃ C : WilsonFamily su4, WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) :=
  jointExistence su4 h

end ReviewSU4

#print axioms ReviewSU4.su4Theory
