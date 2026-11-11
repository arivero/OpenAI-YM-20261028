# 51. Second pass: recheck of the changes made after log 50

Verifier: Claude Opus 5.5 subagent, 11 November 2026. Same constraints as log 50: nothing modified outside `review/work/verify/`, no rebuild. New logs are in `review/work/verify/logs2/`.

## Verdicts

| Item | Verdict |
|---|---|
| A. Compilation | Pass. All four files exit 0, no warnings, standard axioms only. Logs 45–47 in `review/logs/` were refreshed and match my runs |
| B. Repaired definitions | Pass. `ConvergesK` is free of the obstruction. `FitsCompact` is the right box. `eventually_suitable`, `convergesK_empty`, `compactified_of_public`, `compactified_empty` and `compactified_degenerate` state what their docstrings say. I found no further obstruction for a genuine construction. One gap: `CompactifiedLimit` does not require the order to be strictly increasing (B4) |
| C. Prose | Two inaccuracies remain ("no construction exists", "the restriction … is forced"), plus two small ones |
| D. New | The public analogue of `compactified_degenerate` is now machine-checked (`work/verify/PublicDegenerate.lean`), which supports the comparison in Note 10 §3 |

## A. Compilation

```sh
cd /path/to/ym-release/OpenAI-YM-20261028; export PATH=$HOME/.elan/bin:$PATH
for f in VariationAnisotropic VariationGaugeNetwork VariationProduct SU4Skeleton; do
  /usr/bin/time -f "WALL=%e s MAXRSS=%M KB" lake env lean ../review/lean/$f.lean ...; done
```

```
VariationAnisotropic (443 lines): converges_iff, regular_of_isotropic, convergesK_empty,
  compactified_of_public, compactified_empty, eventually_suitable, no_token_of_compact,
  compactified_degenerate -> [propext, Classical.choice, Quot.sound]   WALL=7.50 s  6.9 GB  EXIT=0
VariationGaugeNetwork (132): hop_star, hop_gaugeAct, hop_pow_gaugeAct, moment_gaugeAct -> same  EXIT=0
VariationProduct (63): block_mul, energy_split, slope_ratio -> same                            EXIT=0
SU4Skeleton (44): ReviewSU4.su4Theory -> same                                  11.0 GB  EXIT=0
```

The escape-hatch grep over the four files finds only `set_option autoImplicit false`.

Lines 1–118 of `VariationAnisotropic.lean` (the anisotropic copies of the public definitions, `ofIsotropic`, `converges_iff`, `regular_of_isotropic`) are identical to the version checked in log 50, apart from the header docstring (`diff` against my copy). The theorem bodies of `VariationGaugeNetwork.lean` and `VariationProduct.lean` are identical to the log-50 versions; only docstrings and `#print` lines changed.

## B. The repaired definitions

**B1. `ConvergesK` and `eventually_suitable` (`VariationAnisotropic.lean:138-145, 199-228`).**

- `ConvergesK` asks the old three conjuncts only of test functions with `FitsCompact K Lc t`.
- `eventually_suitable` assumes exactly the `compact` and `growing` fields plus `StrictMono order`, and proves `∀ᶠ k, C.suitable (order k) t` for every fitting `t`.
  - In a direction of `K`, the box of `suitable` with `period = Lc` is literally the box of `FitsCompact`.
  - In a growing direction, `k ≤ order k ≤ period (order k) a` together with `|x i a| ≤ ‖x‖ ≤ R` gives the bound once `k > 2R`.
- The hypotheses are the right ones and none is superfluous. For `K = univ`, `growing` is vacuous and the proof uses only the `K` branch. The docstring says "satisfiable by every family"; the lemma proves more, namely that the conjunct holds for every such family along every strictly increasing order.

**B2. `FitsCompact` (`:131-134`).** The box is `(-Lc/2, Lc/2)` in every direction `a ∈ K`, for every point `i`. Units are the same as in the public `suitable` (`PublicWilson.lean:75-77`): periods are physical side lengths in units of the coarsest lattice, because `mesh N = 1/denominator N` and the lattice side is `period · denominator`. `place` sends the lattice coordinate to `mesh · valMinAbs y ∈ (-Lc/2, Lc/2]`, so the open box lies inside the sampled region.

**B3. Could a genuine compactified construction satisfy `CompactifiedLimit`?** I see no remaining obstruction.

- Two distinct points of the open box stay distinct on the torus, so `separated` agrees with separation on ℝ^{4−k} × T^k for fitting supports.
- Test functions whose support touches the seam `±Lc/2` are excluded. That restriction loses information but contradicts nothing.
- For `K = univ` all periods are fixed. The volume limit then reduces to convergence of `row (order k)`, which a `p`-independent family meets trivially.

This is an argument; existence of a genuine construction is unproved.

**B4. Gap: no monotonicity of `order` in `CompactifiedLimit`** (`:150-156`). The structure takes `order` as a free parameter, while `eventually_suitable` needs `StrictMono order`. The public statement supplies a strictly increasing `p ∘ q`, and `compactified_empty` uses it, so nothing is wrong. But the clause on its own is meant for strictly increasing orders and does not say so. `compactified_degenerate` holds for every `order`, including constant ones. Suggest a field `ordered : StrictMono order`, or a sentence in the docstring.

**B5. `convergesK_empty` (`:148-152`)** proves `ConvergesK ∅ Lc order u ↔ ConvergesA order u`, because `FitsCompact ∅` is trivially true. It says what is claimed.

**B6. `compactified_of_public`, `compactified_empty` (`:160-180`).** These are correct. `compactified_empty` now returns the hierarchy `T`, its `Properties`, and `CompactifiedLimit` for the unselected correlations of the same `T`, so its hypotheses are used.

**B7. `compactified_degenerate` (`:411-420`):**

```lean
∃ (C : WilsonFamilyA g) (u : …), IsEmpty C.Token ∧ CompactifiedLimit C K Lc order u
```

It holds for every `g`, `K`, `Lc` and `order`. Statement and docstring are accurate. Beyond the Lean code: field-blind insertions (constant in `U`, nonempty `Token`) very likely satisfy the clause too, by Riemann-sum convergence of `smear`. I have not proved this. A non-triviality clause therefore has to exclude field-blind observables, not only empty token types, as `ZeroInsertionProbe.lean` and `SpecProbes.lean` (Probe B) show for the public statement.

## C. Prose versus code (passages of item 3)

1. **"No construction exists"** appears in three places:
   - Note 10 §3, line 34: "No construction exists for a nonempty K."
   - Note 4, line 59: "No construction exists for a compact direction."
   - README line 56: "no construction exists there".

   `compactified_degenerate` constructs a witness for every nonempty `K`. Correction: "No family with observables is constructed for a nonempty K" (README: "no construction with observables exists there").

2. **Note 10 §3, line 31, and Note 4, line 59:** "The restriction to fitting test functions is forced." The Lean code proves less. `no_token_of_compact` shows that the unrestricted clause fails for every family with a token, so *some* change of the admissible test functions is forced. `FitsCompact` is one choice; test functions periodic in the directions of K, which also allow supports across the seam, would be another.

   Correction: "Some restriction of the test functions is forced: with a compact direction the unrestricted clause fails for every family with an observable (`no_token_of_compact`). The file uses the simplest one, support inside the box (`FitsCompact`); along any strictly increasing volume order every such test function is then eventually admissible (`eventually_suitable`)."

   The same sentence of line 31 omits "along a strictly increasing order".

3. **Note 2 §7:** "With the slopes of section 5 this means, for SU(m₁)×SU(m₂) in block form, m₁ = m₂". The arithmetic is right. With s_i = 11 m_i²/(12π²) and w_i = m_i/(m₁+m₂), the condition s₁/w₁ = s₂/w₂ reduces to m₁ = m₂ (my check). The sentence lacks the in-place "one-loop, unformalized" marker that Note 10 §5 and `VariationProduct.lean:10-13` carry; add it. Optional: the first sentence's "With one coupling per factor" is unnecessary. By `energy_split` the single-trace action of block-diagonal links is already a sum, so the measure factorizes with a single β, at the effective couplings β·m_i/(m₁+m₂).

4. **`SU4Skeleton.lean:7-8`:** "The hypothesis is proved … in `VariationSUN.lean`". It is proved for `ReviewSUN.suN 2`, which is definitionally equal to `ReviewSU4.su4` (the `rfl` check of log 50, `MiscChecks.lean`). Adding "for the definitionally equal `ReviewSUN.suN 2`" makes the sentence exact.

Checked and accurate:

- Note 10: header row 7 (logs 45–47 now contain the new theorems); summary line 13; table line counts 443/132/63; line 23 on the two `su4Theory`; §3 lines 28–30, 32 and 36; §5; §6, including the memory figures, measured at 6.7–6.9 GB and 11.0 GB.
- Note 4, line 59: the parts other than items 1–2.
- Note 2, §4 ("a single bare coupling can follow only in special cases").
- Note 3, basis table and lines 13, 21, 44–46.
- README line 55 and the memory note on line 75.
- `VariationProduct.lean:4-13`.

The placeholder `CHECK2` (Note 10, line 8) remains, as intended.

## D. New

**D1. The comparison in Note 10 §3, line 32** ("exactly as the clause `wilson` of the public statement has content only together with the other clauses") is now machine-checked. `work/verify/PublicDegenerate.lean` contains:

```lean
theorem public_wilson_degenerate (g : GaugeGroup) (order : ℕ → ℕ) :
    WilsonRegularity (trivialPublic g) ∧ (trivialPublic g).Converges order (fun _ _ => 1)
```

It holds for every gauge group, simple or not; `trivialPublic` has `Token := Empty`. The file uses only `ChallengeSpec` and Mathlib, plus a copy of `ZeroInsertionProbe.wilsonLaw_isProbability`.

```
'ReviewVerify2.public_wilson_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
WALL=3.97 s MAXRSS=6775304 KB  EXIT=0
```

Citing it (or this log) would back the sentence.

**D2.** See B4 (monotonicity of `order`) and B7 (field-blind observables).
