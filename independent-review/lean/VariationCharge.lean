import PublicTheory
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

#print axioms ReviewCharge.centre_in_U1
#print axioms ReviewCharge.charge_congruence
#print axioms ReviewCharge.singlet_charge
