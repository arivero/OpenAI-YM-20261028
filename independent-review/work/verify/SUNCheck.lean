import Lean.Replay
import ConcreteSU2
import Solution
import YM.Gauge.Lie

/-! Variation written for the independent review (not part of the submission).

Simplicity of the real Lie algebra of SU(N) for every N ≥ 2, in the form required
by the hypothesis `GaugeGroup.IsSimple` of the public statement, and the resulting
instances of the public theorem `YangMills.jointExistence` for SU(N), in particular
SU(3), SU(4) and SU(5). The submission instantiates SU(2) only.

The simplicity proof (everything before the last section) uses only Mathlib, the
public definitions and `YM.Gauge.Lie`; the import of `Solution` is needed for the
instances at the end. -/
set_option autoImplicit false
noncomputable section
namespace ReviewSUN
open YM Matrix NormedSpace Function
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

variable {m : ℕ}

/-! ## A criterion for membership in the Lie algebra -/

/-- A skew-Hermitian matrix that is reversed by an involution generates a
one-parameter subgroup of SU(m+2). The determinant of `exp (s • X)` squares to one
by the involution, and `exp (t • X)` is the square of `exp ((t/2) • X)`. -/
theorem mem_lie_of_reflection (X R : Mat m) (hskew : star X = -X) (hR : R * R = 1)
    (hRX : R * X * R = -X) : X ∈ (SUN m).lie := by
  intro t
  have hinv : ∀ s : ℝ, exp (-(s • X)) * exp (s • X) = 1 := by
    intro s
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  have hinv' : ∀ s : ℝ, exp (s • X) * exp (-(s • X)) = 1 := by
    intro s
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_right), add_neg_cancel,
      NormedSpace.exp_zero]
  have hstar : star (exp (t • X)) = exp (-(t • X)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_smul, star_trivial, hskew, smul_neg]
  have hunit : exp (t • X) ∈ Matrix.unitaryGroup (Idx m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, hstar]
    exact hinv' t
  have hRinv : R⁻¹ = R := Matrix.inv_eq_right_inv hR
  have hRunit : IsUnit R := ⟨⟨R, R, hR, hR⟩, rfl⟩
  have hconj : ∀ s : ℝ, exp (-(s • X)) = R * exp (s • X) * R := by
    intro s
    have h := Matrix.exp_conj R (s • X) hRunit
    rw [hRinv] at h
    rw [← h]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, hRX, smul_neg]
  have hdet_sq : ∀ s : ℝ, (exp (s • X)).det * (exp (s • X)).det = 1 := by
    intro s
    have h1 := congrArg Matrix.det (hinv s)
    rw [Matrix.det_mul, Matrix.det_one, hconj s, Matrix.det_mul, Matrix.det_mul] at h1
    have hR2 : R.det * R.det = 1 := by rw [← Matrix.det_mul, hR, Matrix.det_one]
    calc (exp (s • X)).det * (exp (s • X)).det
        = (R.det * R.det) * ((exp (s • X)).det * (exp (s • X)).det) := by rw [hR2, one_mul]
      _ = R.det * (exp (s • X)).det * R.det * (exp (s • X)).det := by ring
      _ = 1 := h1
  have hhalf : exp (t • X) = exp ((t / 2) • X) * exp ((t / 2) • X) := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]
  have hdet : (exp (t • X)).det = 1 := by rw [hhalf, Matrix.det_mul, hdet_sq]
  exact ⟨⟨⟨exp (t • X), hunit⟩, hdet⟩, rfl⟩

/-! ## Generators -/

/-- `E_jk - E_kj`. -/
def A (j k : Idx m) : Mat m := Matrix.single j k 1 - Matrix.single k j 1
/-- `i (E_jk + E_kj)`. -/
def S (j k : Idx m) : Mat m := Matrix.single j k Complex.I + Matrix.single k j Complex.I
/-- `i (E_jj - E_kk)`. -/
def Hd (j k : Idx m) : Mat m := Matrix.single j j Complex.I - Matrix.single k k Complex.I

/-- The diagonal sign matrix with `-1` in position `k`. -/
def refl (k : Idx m) : Mat m := Matrix.diagonal fun a => if a = k then -1 else 1

theorem refl_mul_refl (k : Idx m) : refl k * refl k = (1 : Mat m) := by
  unfold refl
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : a = k <;> simp [h]

theorem refl_conj_apply (k : Idx m) (X : Mat m) (a b : Idx m) :
    (refl k * X * refl k) a b =
      (if a = k then -1 else 1) * X a b * (if b = k then -1 else 1) := by
  unfold refl
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem A_apply (j k a b : Idx m) :
    A j k a b = (if j = a ∧ k = b then 1 else 0) - (if k = a ∧ j = b then 1 else 0) := by
  simp [A, Matrix.single_apply]

theorem S_apply (j k a b : Idx m) :
    S j k a b = (if j = a ∧ k = b then Complex.I else 0) +
      (if k = a ∧ j = b then Complex.I else 0) := by
  simp [S, Matrix.single_apply]

theorem star_A (j k : Idx m) : star (A j k) = -A j k := by
  ext a b
  rw [Matrix.star_apply, Matrix.neg_apply, A_apply, A_apply]
  by_cases h1 : j = a <;> by_cases h2 : k = b <;> by_cases h3 : k = a <;> by_cases h4 : j = b <;>
    simp_all

theorem star_S (j k : Idx m) : star (S j k) = -S j k := by
  ext a b
  rw [Matrix.star_apply, Matrix.neg_apply, S_apply, S_apply]
  by_cases h1 : j = a <;> by_cases h2 : k = b <;> by_cases h3 : k = a <;> by_cases h4 : j = b <;>
    simp_all

theorem refl_A (j k : Idx m) (h : j ≠ k) : refl k * A j k * refl k = -A j k := by
  ext a b
  rw [refl_conj_apply, Matrix.neg_apply, A_apply]
  by_cases h1 : j = a <;> by_cases h2 : k = b <;> by_cases h3 : k = a <;> by_cases h4 : j = b <;>
    simp_all

theorem refl_S (j k : Idx m) (h : j ≠ k) : refl k * S j k * refl k = -S j k := by
  ext a b
  rw [refl_conj_apply, Matrix.neg_apply, S_apply]
  by_cases h1 : j = a <;> by_cases h2 : k = b <;> by_cases h3 : k = a <;> by_cases h4 : j = b <;>
    simp_all

theorem A_mem (j k : Idx m) (h : j ≠ k) : A j k ∈ (SUN m).lie :=
  mem_lie_of_reflection (A j k) (refl k) (star_A j k) (refl_mul_refl k) (refl_A j k h)

theorem S_mem (j k : Idx m) (h : j ≠ k) : S j k ∈ (SUN m).lie :=
  mem_lie_of_reflection (S j k) (refl k) (star_S j k) (refl_mul_refl k) (refl_S j k h)

/-! ## Commutators of the generators -/

/-- Product of two matrix units. -/
theorem EE (a b c d : Idx m) (x y : ℂ) :
    (Matrix.single a b x : Mat m) * Matrix.single c d y =
      if b = c then Matrix.single a d (x * y) else 0 := by
  by_cases h : b = c
  · subst h
    rw [if_pos rfl, Matrix.single_mul_single_same]
  · rw [if_neg h]
    exact Matrix.single_mul_single_of_ne x a b c h y

theorem comm_A_S (j k : Idx m) (h : j ≠ k) :
    A j k * S j k - S j k * A j k = (2 : ℝ) • Hd j k := by
  have h' := h.symm
  simp only [A, S, Hd, mul_add, add_mul, mul_sub, sub_mul, EE, if_neg h, if_neg h', if_true,
    one_mul, mul_one, two_smul]
  abel

theorem comm_Hd_A (j k : Idx m) (h : j ≠ k) :
    Hd j k * A j k - A j k * Hd j k = (2 : ℝ) • S j k := by
  have h' := h.symm
  simp only [A, S, Hd, mul_sub, sub_mul, EE, if_neg h, if_neg h', if_true,
    one_mul, mul_one, two_smul]
  abel

theorem comm_A_A (a b c : Idx m) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    A a b * A b c - A b c * A a b = A a c := by
  have hba := hab.symm
  have hcb := hbc.symm
  have hca := hac.symm
  simp only [A, mul_sub, sub_mul, EE, if_neg hab, if_neg hba, if_neg hbc, if_neg hcb, if_neg hac,
    if_neg hca, if_true, one_mul]
  abel

theorem Hd_mem (j k : Idx m) (h : j ≠ k) : Hd j k ∈ (SUN m).lie := by
  have h1 := (SUN m).bracket_mem (A_mem j k h) (S_mem j k h)
  rw [comm_A_S j k h] at h1
  have h2 := Submodule.smul_mem _ (1 / 2 : ℝ) h1
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h2

/-! ## Diagonal elements of the Lie algebra are traceless -/

private def ph (y : Idx m → ℝ) (t : ℝ) : Idx m → ℂ :=
  fun a => Complex.exp (((t * y a : ℝ) : ℂ) * Complex.I)

private lemma exp_smul_diag (y : Idx m → ℝ) (t : ℝ) :
    exp (t • Matrix.diagonal (fun a : Idx m => ((y a : ℝ) : ℂ) * Complex.I)) =
      Matrix.diagonal (ph y t) := by
  have h : t • Matrix.diagonal (fun a : Idx m => ((y a : ℝ) : ℂ) * Complex.I) =
      Matrix.diagonal fun a => ((t * y a : ℝ) : ℂ) * Complex.I := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext a
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [h, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext a
  simp only [ph, Complex.exp_eq_exp_ℂ]

private lemma ph_prod (y : Idx m → ℝ) (t : ℝ) :
    ∏ a, ph y t a = Complex.exp (((t * ∑ a, y a : ℝ) : ℂ) * Complex.I) := by
  unfold ph
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- If `i·diag(y)` lies in the Lie algebra of SU(m+2) then `∑ y = 0`. -/
theorem diag_sum_zero (y : Idx m → ℝ)
    (h : Matrix.diagonal (fun a : Idx m => ((y a : ℝ) : ℂ) * Complex.I) ∈ (SUN m).lie) :
    ∑ a, y a = 0 := by
  by_contra hs
  obtain ⟨u, hu⟩ := h (Real.pi / ∑ a, y a)
  have h1 : (exp ((Real.pi / ∑ a, y a) •
      Matrix.diagonal (fun a : Idx m => ((y a : ℝ) : ℂ) * Complex.I))).det = 1 := by
    rw [← hu]; exact u.property
  rw [exp_smul_diag, Matrix.det_diagonal, ph_prod, div_mul_cancel₀ _ hs, Complex.exp_pi_mul_I] at h1
  norm_num at h1

/-! ## The filter that isolates one pair of entries -/

/-- The diagonal entries of `Hd j k`, divided by `i`. -/
def rr (j k a : Idx m) : ℂ := (if a = j then 1 else 0) - (if a = k then 1 else 0)

theorem Hd_eq_diagonal (j k : Idx m) :
    Hd j k = Matrix.diagonal fun a => Complex.I * rr j k a := by
  ext a b
  simp only [Hd, Matrix.sub_apply, Matrix.single_apply, Matrix.diagonal_apply, rr]
  by_cases h1 : a = j <;> by_cases h2 : a = k <;> by_cases h3 : a = b <;> simp_all [eq_comm]

/-- The commutator with a fixed matrix. -/
def ad (H X : Mat m) : Mat m := H * X - X * H

theorem ad_Hd_apply (j k : Idx m) (X : Mat m) (a b : Idx m) :
    ad (Hd j k) X a b = Complex.I * (rr j k a - rr j k b) * X a b := by
  unfold ad
  rw [Hd_eq_diagonal, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- A polynomial in `ad (Hd j k)` that keeps the `(j,k)` and `(k,j)` entries only. -/
def filt (j k : Idx m) (X : Mat m) : Mat m :=
  (1 / 12 : ℝ) • (ad (Hd j k) (ad (Hd j k) (ad (Hd j k) (ad (Hd j k) X))) +
    ad (Hd j k) (ad (Hd j k) X))

theorem filt_apply (j k : Idx m) (hjk : j ≠ k) (X : Mat m) (a b : Idx m) :
    filt j k X a b = if (a = j ∧ b = k) ∨ (a = k ∧ b = j) then X a b else 0 := by
  have key : filt j k X a b =
      ((rr j k a - rr j k b) ^ 4 - (rr j k a - rr j k b) ^ 2) / 12 * X a b := by
    simp only [filt, Matrix.smul_apply, Matrix.add_apply, ad_Hd_apply, Complex.real_smul]
    push_cast
    linear_combination ((1 / 12 : ℂ) * ((Complex.I ^ 2 - 1) * (rr j k a - rr j k b) ^ 4 * X a b +
      (rr j k a - rr j k b) ^ 2 * X a b)) * Complex.I_sq
  rw [key]
  unfold rr
  by_cases h1 : a = j <;> by_cases h2 : a = k <;> by_cases h3 : b = j <;> by_cases h4 : b = k <;>
    simp_all <;> norm_num

theorem rr_left (j k : Idx m) (hjk : j ≠ k) : rr j k j = 1 := by
  simp [rr, hjk]

theorem rr_right (j k : Idx m) (hjk : j ≠ k) : rr j k k = -1 := by
  simp [rr, hjk.symm]

theorem A_swap (j k : Idx m) : A k j = -A j k := by
  unfold A
  abel

/-! ## Ideals -/

section Ideal
variable (I : Submodule ℝ (Mat m))
  (hid : ∀ X ∈ (SUN m).lie, ∀ Y ∈ I, X * Y - Y * X ∈ I)
include hid

theorem ad_mem {H Y : Mat m} (hH : H ∈ (SUN m).lie) (hY : Y ∈ I) : ad H Y ∈ I :=
  hid H hH Y hY

/-- An element of the ideal with a nonzero off-diagonal entry yields the generator `A j k`. -/
theorem extract (X : Mat m) (hX : X ∈ I) (hskew : star X = -X) (j k : Idx m) (hjk : j ≠ k)
    (hz : X j k ≠ 0) : A j k ∈ I := by
  have hH : Hd j k ∈ (SUN m).lie := Hd_mem j k hjk
  have hW : filt j k X ∈ I := by
    unfold filt
    exact I.smul_mem _ (I.add_mem
      (ad_mem I hid hH (ad_mem I hid hH (ad_mem I hid hH (ad_mem I hid hH hX))))
      (ad_mem I hid hH (ad_mem I hid hH hX)))
  have hT : ad (Hd j k) (filt j k X) ∈ I := ad_mem I hid hH hW
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, X j k = (x : ℂ) + (y : ℂ) * Complex.I :=
    ⟨_, _, (Complex.re_add_im _).symm⟩
  have hkj : X k j = -((x : ℂ) - (y : ℂ) * Complex.I) := by
    have h1 := congrFun (congrFun hskew k) j
    rw [Matrix.star_apply, Matrix.neg_apply] at h1
    have h2 : X k j = -star (X j k) := by rw [h1, neg_neg]
    rw [h2, hxy, Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have hN : x ^ 2 + y ^ 2 ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    apply hz
    rw [hxy, hx0, hy0]
    simp
  have e : A j k = (1 / (x ^ 2 + y ^ 2) : ℝ) •
      (x • filt j k X - (y / 2) • ad (Hd j k) (filt j k X)) := by
    ext a b
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, ad_Hd_apply,
      filt_apply j k hjk, A_apply, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    have hc : ((1 / (x ^ 2 + y ^ 2) : ℝ) : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) = 1 := by
      have h3 : (1 / (x ^ 2 + y ^ 2)) * (x ^ 2 + y ^ 2) = 1 := one_div_mul_cancel hN
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h3
    generalize ((1 / (x ^ 2 + y ^ 2) : ℝ) : ℂ) = c at hc ⊢
    by_cases hc1 : a = j ∧ b = k
    · rcases hc1 with ⟨ha, hb⟩
      rw [ha, hb, rr_left j k hjk, rr_right j k hjk, if_pos (Or.inl ⟨rfl, rfl⟩),
        if_pos ⟨rfl, rfl⟩, if_neg (fun h : k = j ∧ j = k => hjk h.2), hxy]
      push_cast
      linear_combination (-1 : ℂ) * hc + c * (y : ℂ) ^ 2 * Complex.I_sq
    · by_cases hc2 : a = k ∧ b = j
      · rcases hc2 with ⟨ha, hb⟩
        rw [ha, hb, rr_left j k hjk, rr_right j k hjk, if_pos (Or.inr ⟨rfl, rfl⟩),
          if_neg (fun h : j = k ∧ k = j => hjk h.1), if_pos ⟨rfl, rfl⟩, hkj]
        push_cast
        linear_combination hc - c * (y : ℂ) ^ 2 * Complex.I_sq
      · have h1 : ¬(j = a ∧ k = b) := fun h => hc1 ⟨h.1.symm, h.2.symm⟩
        have h2 : ¬(k = a ∧ j = b) := fun h => hc2 ⟨h.1.symm, h.2.symm⟩
        have h3 : ¬((a = j ∧ b = k) ∨ (a = k ∧ b = j)) := fun h => h.elim hc1 hc2
        rw [if_neg h1, if_neg h2, if_neg h3]
        simp
  rw [e]
  exact I.smul_mem _ (I.sub_mem (I.smul_mem _ hW) (I.smul_mem _ hT))

/-- From one generator to a neighbouring one. -/
theorem spread (a b c : Idx m) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (h : A a b ∈ I) :
    A a c ∈ I := by
  have h1 := hid (A b c) (A_mem b c hbc) (A a b) h
  have e : A b c * A a b - A a b * A b c = -A a c := by
    rw [← comm_A_A a b c hab hbc hac]
    abel
  rw [e] at h1
  simpa using I.neg_mem h1

/-- One generator `A j k` in the ideal gives all of them. -/
theorem all_A (j k : Idx m) (hjk : j ≠ k) (h : A j k ∈ I) : ∀ p q : Idx m, p ≠ q → A p q ∈ I := by
  have swap : ∀ p q : Idx m, A p q ∈ I → A q p ∈ I := by
    intro p q hpq
    rw [A_swap]
    exact I.neg_mem hpq
  have C1 : ∀ q : Idx m, q ≠ j → A j q ∈ I := by
    intro q hq
    by_cases hqk : q = k
    · rw [hqk]; exact h
    · exact spread I hid j k q hjk (Ne.symm hqk) (Ne.symm hq) h
  intro p q hpq
  by_cases hp : p = j
  · rw [hp]
    exact C1 q (fun hqj => hpq (hp.trans hqj.symm))
  · have h1 : A p j ∈ I := swap j p (C1 p hp)
    by_cases hq : q = j
    · rw [hq]; exact h1
    · exact spread I hid p j q hp (Ne.symm hq) hpq h1

theorem S_of_A (p q : Idx m) (hpq : p ≠ q) (h : A p q ∈ I) : S p q ∈ I := by
  have h1 := hid (Hd p q) (Hd_mem p q hpq) (A p q) h
  rw [comm_Hd_A p q hpq] at h1
  have h2 := I.smul_mem (1 / 2 : ℝ) h1
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h2

theorem Hd_of_A (p q : Idx m) (hpq : p ≠ q) (h : A p q ∈ I) : Hd p q ∈ I := by
  have h1 := hid (S p q) (S_mem p q hpq) (A p q) h
  have e : S p q * A p q - A p q * S p q = (-2 : ℝ) • Hd p q := by
    have := comm_A_S p q hpq
    rw [neg_smul, ← this]
    abel
  rw [e] at h1
  have h2 := I.smul_mem (-1 / 2 : ℝ) h1
  rwa [smul_smul, show (-1 / 2 : ℝ) * -2 = 1 by norm_num, one_smul] at h2

omit hid in
/-- Twice a skew-Hermitian matrix as a real combination of the generators. -/
theorem two_smul_skew (Y : Mat m) (hskew : star Y = -Y) :
    (2 : ℝ) • Y = ∑ i, ∑ j, ((Y i j).re • A i j + (Y i j).im • S i j) := by
  have hterm : ∀ i j : Idx m, (Y i j).re • A i j + (Y i j).im • S i j =
      Matrix.single i j (Y i j) + Matrix.single j i (Y j i) := by
    intro i j
    obtain ⟨x, y, hxy, hre, him⟩ : ∃ x y : ℝ, Y i j = (x : ℂ) + (y : ℂ) * Complex.I ∧
        (Y i j).re = x ∧ (Y i j).im = y := ⟨_, _, (Complex.re_add_im _).symm, rfl, rfl⟩
    have hji : Y j i = -((x : ℂ) - (y : ℂ) * Complex.I) := by
      have h1 := congrFun (congrFun hskew j) i
      rw [Matrix.star_apply, Matrix.neg_apply] at h1
      have h2 : Y j i = -star (Y i j) := by rw [h1, neg_neg]
      rw [h2, hxy, Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    rw [hre, him, hji, hxy]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, A_apply, S_apply, Matrix.single_apply,
      Complex.real_smul]
    by_cases h1 : i = a ∧ j = b
    · by_cases h2 : j = a ∧ i = b
      · simp only [if_pos h1, if_pos h2]
        ring
      · simp only [if_pos h1, if_neg h2]
        ring
    · by_cases h2 : j = a ∧ i = b
      · simp only [if_neg h1, if_pos h2]
        ring
      · simp only [if_neg h1, if_neg h2]
        ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [← Matrix.matrix_eq_sum_single Y, Finset.sum_comm, ← Matrix.matrix_eq_sum_single Y, two_smul]

/-- A nonzero ideal is the whole Lie algebra. -/
theorem ideal_eq_top (hle : I ≤ (SUN m).lie) (hne : I ≠ ⊥) : I = (SUN m).lie := by
  obtain ⟨X, hX, hX0⟩ := (Submodule.ne_bot_iff I).mp hne
  have hXskew : star X = -X := (SUN m).generates_skew (hle hX)
  have hA : ∃ j k : Idx m, j ≠ k ∧ A j k ∈ I := by
    by_cases hoff : ∃ j k : Idx m, j ≠ k ∧ X j k ≠ 0
    · obtain ⟨j, k, hjk, hz⟩ := hoff
      exact ⟨j, k, hjk, extract I hid X hX hXskew j k hjk hz⟩
    · push Not at hoff
      obtain ⟨d, hd⟩ : ∃ d : Idx m → ℝ, ∀ a, X a a = ((d a : ℝ) : ℂ) * Complex.I := by
        refine ⟨fun a => (X a a).im, fun a => ?_⟩
        have h1 := congrFun (congrFun hXskew a) a
        rw [Matrix.star_apply, Matrix.neg_apply] at h1
        have h2 := congrArg Complex.re h1
        simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h2
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
            Complex.I_im, mul_one, sub_self]
          linarith
        · simp
      have hXd : X = Matrix.diagonal (fun a => ((d a : ℝ) : ℂ) * Complex.I) := by
        ext a b
        by_cases hab : a = b
        · rw [hab, Matrix.diagonal_apply_eq, hd b]
        · rw [Matrix.diagonal_apply_ne _ hab]
          exact hoff a b hab
      have hsum : ∑ a, d a = 0 := diag_sum_zero d (by rw [← hXd]; exact hle hX)
      have hex : ∃ j, d j ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hX0
        rw [hXd]
        ext a b
        simp [Matrix.diagonal_apply, hall]
      obtain ⟨j, hj⟩ := hex
      have hex2 : ∃ k, d k ≠ d j := by
        by_contra hall
        push Not at hall
        have h3 : ∑ a : Idx m, d a = ((m + 1 + 1 : ℕ) : ℝ) * d j := by
          rw [Finset.sum_congr rfl (fun a _ => hall a)]
          simp
        rw [h3] at hsum
        have hpos : ((m + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        exact hj ((mul_eq_zero.mp hsum).resolve_left hpos)
      obtain ⟨k, hk⟩ := hex2
      have hjk : j ≠ k := fun h => hk (by rw [h])
      have hY : A j k * X - X * A j k ∈ I := hid _ (A_mem j k hjk) _ hX
      have hYskew := (SUN m).generates_skew (hle hY)
      have hentry : (A j k * X - X * A j k) j k ≠ 0 := by
        have h4 : (A j k * X - X * A j k) j k = (((d k - d j : ℝ)) : ℂ) * Complex.I := by
          rw [hXd, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, A_apply,
            if_pos ⟨rfl, rfl⟩, if_neg (fun h : k = j ∧ j = k => hjk h.2)]
          push_cast
          ring
        rw [h4]
        intro h0
        rcases mul_eq_zero.mp h0 with h5 | h5
        · exact hk (by have := Complex.ofReal_eq_zero.mp h5; linarith)
        · exact Complex.I_ne_zero h5
      exact ⟨j, k, hjk, extract I hid _ hY hYskew j k hjk hentry⟩
  obtain ⟨j, k, hjk, hAjk⟩ := hA
  have hallA := all_A I hid j k hjk hAjk
  refine le_antisymm hle (fun Y hY => ?_)
  have hYskew : star Y = -Y := (SUN m).generates_skew hY
  have h2Y := two_smul_skew Y hYskew
  -- split off the diagonal terms
  have hsplit : ∑ i, ∑ j, ((Y i j).re • A i j + (Y i j).im • S i j) =
      ∑ i, (Y i i).im • S i i +
        ∑ i, ∑ j ∈ Finset.univ.erase i, ((Y i j).re • A i j + (Y i j).im • S i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    simp [A]
  have hP : ∑ i, ∑ j ∈ Finset.univ.erase i, ((Y i j).re • A i j + (Y i j).im • S i j) ∈ I := by
    refine I.sum_mem (fun i _ => I.sum_mem (fun j hj => ?_))
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact I.add_mem (I.smul_mem _ (hallA i j hij))
      (I.smul_mem _ (S_of_A I hid i j hij (hallA i j hij)))
  -- the diagonal part lies in the Lie algebra, hence is traceless
  have hDgL : ∑ i, (Y i i).im • S i i ∈ (SUN m).lie := by
    have h5 : ∑ i, (Y i i).im • S i i = (2 : ℝ) • Y -
        ∑ i, ∑ j ∈ Finset.univ.erase i, ((Y i j).re • A i j + (Y i j).im • S i j) := by
      rw [h2Y, hsplit]
      abel
    rw [h5]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hY) (hle hP)
  have hDgd : ∑ i, (Y i i).im • S i i =
      Matrix.diagonal (fun a : Idx m => (((2 * (Y a a).im : ℝ)) : ℂ) * Complex.I) := by
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · rw [hab, Matrix.diagonal_apply_eq, Finset.sum_eq_single b]
      · rw [Matrix.smul_apply, S_apply, if_pos ⟨rfl, rfl⟩, Complex.real_smul]
        push_cast
        ring
      · intro i _ hi
        rw [Matrix.smul_apply, S_apply, if_neg (fun h => hi h.1), add_zero, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · rw [Matrix.diagonal_apply_ne _ hab]
      apply Finset.sum_eq_zero
      intro i _
      rw [Matrix.smul_apply, S_apply, if_neg (fun h => hab (h.1.symm.trans h.2)), add_zero,
        smul_zero]
  have hsum : ∑ a, 2 * (Y a a).im = 0 := diag_sum_zero _ (by rw [← hDgd]; exact hDgL)
  have hDgI : ∑ i, (Y i i).im • S i i ∈ I := by
    have h6 : ∑ i, (Y i i).im • S i i = ∑ i, (2 * (Y i i).im) • Hd i 0 := by
      have h7 : ∑ i : Idx m, (2 * (Y i i).im) • Hd i 0 =
          ∑ i : Idx m, (2 * (Y i i).im) • (Matrix.single i i Complex.I : Mat m) -
            (∑ i : Idx m, 2 * (Y i i).im) • (Matrix.single 0 0 Complex.I : Mat m) := by
        simp only [Hd, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      rw [h7, hsum, zero_smul, sub_zero]
      apply Finset.sum_congr rfl
      intro i _
      simp only [S, two_mul, add_smul, smul_add]
    rw [h6]
    refine I.sum_mem (fun i _ => I.smul_mem _ ?_)
    by_cases hi : i = 0
    · rw [hi]
      simp [Hd]
    · exact Hd_of_A I hid i 0 hi (hallA i 0 hi)
  have h8 : (2 : ℝ) • Y ∈ I := by
    rw [h2Y, hsplit]
    exact I.add_mem hDgI hP
  have h9 := I.smul_mem (1 / 2 : ℝ) h8
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h9

end Ideal

/-! ## The gauge group SU(m+2) of the public statement -/

/-- SU(m+2) as a gauge group of the public statement. -/
abbrev suN (m : ℕ) : YangMills.GaugeGroup :=
  ⟨(SUN m).n, (SUN m).imageGroup, (SUN m).closed_imageGroup, (SUN m).lie, fun _ => Iff.rfl⟩

/-- The Lie algebra of SU(N) is simple for every N ≥ 2, in the sense of the public statement. -/
theorem suN_simple (m : ℕ) : (suN m).IsSimple := by
  have h01 : (0 : Idx m) ≠ 1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  refine ⟨⟨A 0 1, A_mem 0 1 h01, S 0 1, S_mem 0 1 h01, ?_⟩, ?_⟩
  · rw [comm_A_S 0 1 h01]
    intro h
    have h1 := congrFun (congrFun h 0) 0
    simp [Hd] at h1
  · intro I hle hid
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · exact Or.inr (ideal_eq_top I hid hle hI)

/-! ## Instances of the public theorem -/

open YangMills in
/-- The conclusions of the public theorem for SU(m+2), for every m. -/
theorem suNTheory (m : ℕ) : ∃ C : WilsonFamily (suN m), WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) :=
  jointExistence (suN m) (suN_simple m)

open YangMills in
/-- SU(3). -/
theorem su3Theory : ∃ C : WilsonFamily (suN 1), WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) := suNTheory 1

open YangMills in
/-- SU(4). -/
theorem su4Theory : ∃ C : WilsonFamily (suN 2), WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) := suNTheory 2

open YangMills in
/-- SU(5). -/
theorem su5Theory : ∃ C : WilsonFamily (suN 3), WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) := suNTheory 3

/-- The matrix size of `suN m` is `m + 2`: the group is SU(m+2). -/
theorem suN_size (m : ℕ) : (suN m).n + 1 = m + 2 := rfl

end ReviewSUN

#print axioms ReviewSUN.suN_simple
#print axioms ReviewSUN.suNTheory
#print axioms ReviewSUN.su3Theory
#print axioms ReviewSUN.su4Theory
#print axioms ReviewSUN.su5Theory

/-! ===== Verifier additions (copy only; original file untouched) ===== -/
#print axioms ReviewSUN.mem_lie_of_reflection
#print axioms ReviewSUN.A_mem
#print axioms ReviewSUN.S_mem
#print axioms ReviewSUN.Hd_mem
#print axioms ReviewSUN.diag_sum_zero
#print axioms ReviewSUN.filt_apply
#print axioms ReviewSUN.extract
#print axioms ReviewSUN.spread
#print axioms ReviewSUN.all_A
#print axioms ReviewSUN.two_smul_skew
#print axioms ReviewSUN.ideal_eq_top
#print axioms ReviewSUN.suN_size

-- (iii) the statement is the public predicate, no weakening
#check (ReviewSUN.suN_simple : ∀ m : ℕ, YangMills.GaugeGroup.IsSimple (ReviewSUN.suN m))
#check @ReviewSUN.suN_simple
#check @ReviewSUN.ideal_eq_top
#check @ReviewSUN.extract

-- (v) m = 0 is literally the submission's SU(2)
example : ReviewSUN.SUN 0 = YM.Next.Foundations.SUtwo := rfl
example : ReviewSUN.suN 0 = YangMills.su2 := rfl

-- (ii) lieAlgebra field is the YM Lie algebra, and `generates` forces it
example (m : ℕ) : (ReviewSUN.suN m).lieAlgebra = (ReviewSUN.SUN m).lie := rfl
example (m : ℕ) (X : Matrix (Fin (m+2)) (Fin (m+2)) ℂ) :
    X ∈ (ReviewSUN.suN m).lieAlgebra ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈
      Set.range (fun u : (ReviewSUN.suN m).image => (u.1 : Matrix (Fin (m+2)) (Fin (m+2)) ℂ)) :=
  (ReviewSUN.suN m).generates X
-- the image is exactly {U ∈ U(m+2) | det U = 1}
example (m : ℕ) (U : Matrix.unitaryGroup (Fin (m+2)) ℂ) :
    U ∈ (ReviewSUN.suN m).image ↔ U.val.det = 1 := Iff.rfl

-- (iv) types of the instances are syntactically the instantiation of JointExistence
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let je ← getConstInfoDefn ``YangMills.JointExistence
  let check (thm : Name) (mkG : Array Expr → MetaM Expr) : MetaM Unit := do
    let ty := (← getConstInfo thm).type
    forallTelescope ty fun xs body => do
      let g ← mkG xs
      let .forallE _ _ b _ := je.value | throwError "unexpected JointExistence shape"
      let .forallE _ _ b2 _ := b.instantiate1 g | throwError "unexpected shape 2"
      if b2.hasLooseBVars then throwError "conclusion depends on hypothesis"
      let syn := b2 == body
      let dq ← withReducible (isDefEq b2 body)
      logInfo m!"{thm}: syntactically equal to JointExistence body at its group = {syn}; reducible defeq = {dq}"
  check ``ReviewSUN.suNTheory (fun xs => pure (mkApp (mkConst ``ReviewSUN.suN) xs[0]!))
  check ``ReviewSUN.su3Theory (fun _ => pure (mkApp (mkConst ``ReviewSUN.suN) (mkNatLit 1)))
  check ``ReviewSUN.su4Theory (fun _ => pure (mkApp (mkConst ``ReviewSUN.suN) (mkNatLit 2)))
  check ``ReviewSUN.su5Theory (fun _ => pure (mkApp (mkConst ``ReviewSUN.suN) (mkNatLit 3)))
  check ``YangMills.su2Theory (fun _ => pure (mkConst ``YangMills.su2))

-- Independent kernel replay of every declaration of this file reachable from the roots,
-- on top of a freshly imported copy of the same imports.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let k := env.checked.get
  let roots : Array Name := #[`ReviewSUN.suN_simple, `ReviewSUN.suNTheory, `ReviewSUN.su3Theory,
    `ReviewSUN.su4Theory, `ReviewSUN.su5Theory]
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut local_ : Std.HashMap Name ConstantInfo := {}
  let mut external : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := k.find? n | throwError "missing {n}"
    if (env.getModuleIdxFor? n).isSome then
      external := external.insert n
      continue
    local_ := local_.insert n ci
    let mut next := ci.getUsedConstantsAsSet
    match ci with
    | .inductInfo i => for c in i.ctors ++ i.all do next := next.insert c
    | .ctorInfo c => next := next.insert c.induct
    | .recInfo r => for c in r.all do next := next.insert c
    | _ => pure ()
    todo := todo ++ next.toArray
  let mut bad : Array Name := #[]
  for (n, ci) in local_.toList do
    if ci.isUnsafe || ci.isPartial || ci matches .axiomInfo _ then bad := bad.push n
  unless bad.isEmpty do throwError "unsafe/partial/axiom local dependencies: {bad}"
  let imports := env.header.modules.map fun m => ({module := m.module} : Import)
  let base ← liftIO <| importModules imports {}
  for n in external do
    unless (base.checked.get.find? n).isSome do throwError "external dependency missing: {n}"
  for (n, _) in local_.toList do
    if (base.checked.get.find? n).isSome then throwError "local name already in base: {n}"
  logInfo m!"SUN_REPLAY_START localDecls={local_.size} externalRefs={external.size} names={local_.toList.map (·.1)}"
  let checked ← liftIO <| base.replay local_
  for r in roots do
    let some (.thmInfo v) := checked.checked.get.find? r | throwError "root {r} not in replayed env"
    let some (.thmInfo s) := local_[r]? | throwError "root {r} not collected"
    unless v.type == s.type && v.value == s.value do throwError "replayed {r} differs"
  logInfo m!"SUN_REPLAY_PASS localDecls={local_.size}"
