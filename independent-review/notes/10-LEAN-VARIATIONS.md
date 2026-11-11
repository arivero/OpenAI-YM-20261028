# Note 10. Lean code for the variations judged feasible

**Independent review note by the fork owner (arivero), produced with Claude Fable 5.2 in Claude Code, 11 November 2026.** Separate from OpenAI's submission and from the Yang–Mills group's assessment.

| Kind of statement in this note | Basis |
|---|---|
| Every theorem named here | Compiled against the built submission with Lean 4.32.0 and the pinned Mathlib; logs `logs/40-…` to `logs/47-…`; each depends on `propext`, `Classical.choice`, `Quot.sound` only |
| Independent check | A Claude Opus subagent recompiled the eight files, checked the axioms of the named theorems, replayed the 65 declarations of `VariationSUN.lean` in the kernel, compared the statements with this prose and tested them for vacuity: `logs/50-opus-verification.md`, scratch files in `work/verify/`. A second pass on the repaired anisotropic file and the corrected prose is in `logs/51-opus-recheck.md`. Its remaining corrections are applied in this version; the last of them, a field `increasing` in `CompactifiedLimit`, was added after that pass and compiled by us only |
| "What stays open" | Our assessment |

## Summary

Notes 2 to 7 judged several variations of the theorem feasible. This note lists the Lean code written for them. The main addition: the hypothesis of the theorem is now proved for SU(N), every N ≥ 2, so the public theorem has machine-checked instances for SU(3), SU(4) and SU(5) beside the SU(2) instance of the submission. The theorem itself is unchanged.

| File | Lines | Variation | Main statements |
|---|---|---|---|
| `lean/VariationSUN.lean` | 615 | Instances beyond SU(2) (Notes 2, 3) | `suN_simple`, `suNTheory`, `su3Theory`, `su4Theory`, `su5Theory` |
| `lean/VariationCharge.lean` | 85 | Charge quantization for S(U(3)×U(1)) (Note 7) | `centre_in_U1`, `charge_congruence`, `singlet_charge` |
| `lean/VariationAnisotropic.lean` | 448 | Tori with unequal sides, compact directions (Note 4) | `converges_iff`, `CompactifiedLimit`, `compactified_of_public`, `eventually_suitable`, `no_token_of_compact`, `compactified_degenerate` |
| `lean/VariationGaugeNetwork.lean` | 132 | Lattice as finite spectral data (Note 6) | `hop_star`, `hop_gaugeAct`, `hop_pow_gaugeAct`, `moment_gaugeAct` |
| `lean/VariationProduct.lean` | 63 | Product groups (Notes 2, 3) | `block_mul`, `energy_split`, `slope_ratio` |

Earlier files of the same kind: `lean/GeneralityProbes.lean` (Note 2), `lean/BrokenSU4Probe.lean` and `lean/SU4Skeleton.lean` (Note 3), `lean/SpecProbes.lean` and `lean/ZeroInsertionProbe.lean` (`VERIFICATION.md`, section 4.2). Two theorems share the short name `su4Theory`: `ReviewSU4.su4Theory` in `SU4Skeleton.lean` is conditional on simplicity of su(4), and `ReviewSUN.su4Theory` in `VariationSUN.lean` is unconditional.

## 1. SU(N) for every N ≥ 2

```lean
-- lean/VariationSUN.lean
/-- SU(m+2) as a gauge group of the public statement. -/
abbrev suN (m : ℕ) : YangMills.GaugeGroup :=
  ⟨(SUN m).n, (SUN m).imageGroup, (SUN m).closed_imageGroup, (SUN m).lie, fun _ => Iff.rfl⟩

/-- The Lie algebra of SU(N) is simple for every N ≥ 2, in the sense of the public statement. -/
theorem suN_simple (m : ℕ) : (suN m).IsSimple

/-- The conclusions of the public theorem for SU(m+2), for every m. -/
theorem suNTheory (m : ℕ) : ∃ C : WilsonFamily (suN m), WilsonRegularity C ∧
    ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties (p ∘ q) :=
  jointExistence (suN m) (suN_simple m)
```

`SUN m` is the group of unitary matrices of size m+2 with determinant one, defined like the submission's SU(2). `su3Theory`, `su4Theory` and `su5Theory` are the cases m = 1, 2, 3.

**How the proof goes.**

1. *Membership criterion.* A skew-Hermitian X that is reversed by an involution R (R X R = −X, R² = 1) lies in the Lie algebra: the determinant of exp(sX) squares to one by the involution, and exp(tX) is the square of exp((t/2)X). This replaces the identity det exp = exp tr, which the pinned Mathlib lists as an open task.
2. *Generators.* A_jk = E_jk − E_kj and S_jk = i(E_jk + E_kj) satisfy the criterion with a diagonal sign matrix; H_jk = i(E_jj − E_kk) is half their commutator.
3. *A filter.* The operator (ad⁴ + ad²)/12 of H_jk keeps the entries (j,k) and (k,j) of any matrix and removes the others. Applied to an element of an ideal with a nonzero off-diagonal entry it yields A_jk in the ideal.
4. *Diagonal elements.* An element i·diag(y) of the Lie algebra has Σy = 0, by an explicit exponential. A nonzero diagonal element of an ideal therefore has two different entries, and one commutator with A_jk produces an off-diagonal entry.
5. *Spreading.* [A_ab, A_bc] = A_ac moves one generator to all pairs of indices; commutators with H and S give the other generators.
6. *Decomposition.* Twice a skew-Hermitian matrix is a real combination of the generators plus a diagonal part, and the diagonal part is traceless by step 4.

**What stays open.** The other classical groups (SO(N), Sp(N)) and the exceptional groups each need their own proof of the hypothesis.

## 2. Charge quantization

```lean
-- lean/VariationCharge.lean
theorem centre_in_U1 :
    exp ((2 * Real.pi / 3 : ℝ) • Z) = Matrix.diagonal ![omega, omega, omega, 1]
theorem charge_congruence (q t : ℤ) (h : omega ^ q = omega ^ t) : (3 : ℤ) ∣ q - t
theorem singlet_charge (q : ℤ) (h : omega ^ q = 1) : (3 : ℤ) ∣ q
```

The one-parameter group generated by Z = i·diag(1,1,1,−3) passes through diag(ω,ω,ω,1), the generator of the centre of SU(3). Equality of the two phases ω^q and ω^t forces q ≡ t modulo 3. **What stays open:** the identification of ω^t with the action of the centre on a representation of triality t is the argument of Note 7 and is stated there in words.

## 3. Tori with unequal sides

`lean/VariationAnisotropic.lean` repeats the lattice definitions of the public statement with one period per direction (`SiteA`, `wilsonLawA`, `WilsonFamilyA`, `ConvergesA`, `WilsonRegularityA`) and then treats compact directions.

```lean
theorem converges_iff {g : GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ)
    (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) :
    (ofIsotropic C).ConvergesA order u ↔ C.Converges order u := Iff.rfl

/-- The lattice-limit clause for tori whose directions in `K` keep circumference `Lc`. -/
structure CompactifiedLimit {g : GaugeGroup} (C : WilsonFamilyA g) (K : Finset Axis) (Lc : ℕ+)
    (order : ℕ → ℕ) (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop where
  increasing : StrictMono order
  regular : WilsonRegularityA C
  compact : ∀ p i, i ∈ K → C.period p i = Lc
  growing : ∀ i, i ∉ K → StrictMono fun p => (C.period p i).val
  converges : C.ConvergesK K Lc order unselected

theorem compactified_of_public … : CompactifiedLimit (ofIsotropic C) ∅ Lc order u
theorem eventually_suitable … : ∀ᶠ k : ℕ in atTop, C.suitable (order k) t
theorem no_token_of_compact … : ¬ C.ConvergesA order u
theorem compactified_degenerate (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) (order : ℕ → ℕ)
    (horder : StrictMono order) :
    ∃ (C : WilsonFamilyA g) (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ),
      IsEmpty C.Token ∧ CompactifiedLimit C K Lc order u
```

What the file establishes:

- With equal periods the new definitions are the public ones, by definitional unfolding.
- `CompactifiedLimit` formulates the lattice-limit clause for a set K of compact directions. Its convergence clause `ConvergesK` is asked of the test functions whose support fits inside the fixed box in those directions (`FitsCompact`).
- The family and the limit of the public theorem satisfy the clause when no direction is compact (`compactified_of_public`, `compactified_empty`).
- Some restriction of the test functions is forced. With a compact direction the unrestricted clause fails for every family that has an observable, since a test function supported outside the box is never admissible (`no_token_of_compact`). Support inside the fixed box is the restriction chosen here; test functions periodic in the compact directions would be another. With this choice, and along a strictly increasing order of volumes, every fitting test function is eventually inside the box (`eventually_suitable`).
- The clause alone is weak. A family with no observables satisfies it for every gauge group and every K (`compactified_degenerate`). The verifier proved the same for the lattice clauses of the public statement taken alone (`public_wilson_degenerate` in `work/verify/PublicDegenerate.lean`): in both cases the content comes from the other clauses. The verifier adds, without proof, that families whose observables ignore the gauge field very likely satisfy the clause as well.

**What stays open.** For a nonempty K no family with observables is constructed. A compactified theorem would also need the further clauses: reconstruction along a non-compact direction, and a non-triviality statement strong enough to exclude both empty families and observables that ignore the gauge field.

**History.** The first version of this file stated the target with the unrestricted clause. The Opus verifier proved that version degenerate in both senses above. The file was repaired, and the two calibration lemmas reuse the verifier's proofs.

## 4. The lattice as finite spectral data

```lean
-- lean/VariationGaugeNetwork.lean
def hop (U : Configuration g l) : Matrix (Site l) (Site l) (Blk g) := …
theorem hop_star (U : Configuration g l) : star (hop U) = hop U
theorem hop_gaugeAct (t : Site l → g.image) (U : Configuration g l) :
    hop (gaugeAct t U) = gaugeMat t * hop U * star (gaugeMat t)
theorem moment_gaugeAct (k : ℕ) (t : Site l → g.image) (U : Configuration g l) :
    moment k (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) = moment k U
```

Each configuration of the public statement carries a self-adjoint hopping operator on ℓ²(sites) ⊗ ℂ^{n+1}. A gauge transformation, written exactly as in `WilsonRegularity.invariant`, conjugates it by a block-diagonal unitary, so the moments Tr(hop U)^k are gauge invariant. **What stays open:** the hopping expansion that expresses the fourth moment through plaquette traces, which is the step that equates a spectral action with the Wilson energy.

## 5. Product groups

```lean
-- lean/VariationProduct.lean
theorem energy_split (P₁ : Matrix (Fin m₁) (Fin m₁) ℂ) (P₂ : Matrix (Fin m₂) (Fin m₂) ℂ)
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    1 - ((Matrix.fromBlocks P₁ 0 0 P₂).trace).re / ((m₁ + m₂ : ℕ) : ℝ) =
      (m₁ : ℝ) / ((m₁ + m₂ : ℕ) : ℝ) * (1 - (P₁.trace).re / (m₁ : ℝ)) +
      (m₂ : ℝ) / ((m₁ + m₂ : ℕ) : ℝ) * (1 - (P₂.trace).re / (m₂ : ℝ))
theorem slope_ratio … : s₁ / w₁ = s₂ / w₂
```

For block-diagonal links the single-trace energy splits with weights m₁/(m₁+m₂) and m₂/(m₁+m₂), so one coupling gives the factors couplings in a fixed ratio, and two logarithmic slopes can both hold only in that ratio. Whether the slopes of two given factors stand in that ratio is outside the Lean file. By the one-loop values of Note 2, unformalized, it holds for SU(m₁)×SU(m₂) exactly when m₁ = m₂: equal factors can share a coupling, unequal ones need one each. **What stays open:** a product gauge group inside the public statement, and the factorization of the measure.

## 6. Running the files

From the root of a built clone of the submission, with this directory checked out as `independent-review/`:

```sh
lake env lean independent-review/lean/VariationSUN.lean
lake env lean independent-review/lean/VariationCharge.lean
lake env lean independent-review/lean/VariationAnisotropic.lean
lake env lean independent-review/lean/VariationGaugeNetwork.lean
lake env lean independent-review/lean/VariationProduct.lean
```

`VariationSUN.lean` and `SU4Skeleton.lean` import the full solution and need about 11 GB of memory; the others need about 7 GB. Each file ends with `#print axioms` for its main statements.
