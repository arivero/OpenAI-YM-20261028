# 50. Independent verification of the review's Lean files

Verifier: Claude Opus 5.5 subagent, 11 November 2026. Every result below comes from a run made for this report, from the clone root `/path/to/ym-release/OpenAI-YM-20261028` (Lean 4.32.0, pinned Mathlib, prebuilt `.lake`, no rebuild). No file under `review/lean/`, `review/notes/` or the clones was modified. Scratch files and logs are in `review/work/verify/`.

## Verdict table

| File | Compiles (my run) | Axioms (my run) | Statement faithful | Issues |
|---|---|---|---|---|
| `VariationSUN.lean` (615 lines) | Yes, exit 0, no warnings, 5.1 s, 11.06 GB | `propext, Classical.choice, Quot.sound` for all 5 printed and 12 further lemmas | Yes. `SUN 0 = SUtwo` and `suN 0 = YangMills.su2` hold by `rfl`; instance types are syntactically the instantiation of `JointExistence`; independent kernel replay of the 65 local declarations passes | Prose only: minor (D3, D7, D8) |
| `VariationCharge.lean` (85) | Yes, exit 0, no warnings | standard 3 (4 theorems) | Yes, as elementary lemmas. `Z`, `dr` equal those of `BrokenSU4Probe.lean` by `rfl` | The content is the arithmetic of ω; the representation-theoretic step stays informal (the prose says so) |
| `VariationAnisotropic.lean` (151) | Yes, exit 0, no warnings | standard 3 (3 theorems, incl. `regular_of_isotropic` checked in copy) | `converges_iff` faithful: the copies match the public definitions up to the intended changes. **`CompactifiedWilsonLimit` is defective** | **Serious (C1):** provable for every `g`, `K`, `Lc` by an empty-token family; for `K ≠ ∅` every witness has an empty token type. Prose calls it "a statement without proof" |
| `VariationGaugeNetwork.lean` (131) | Yes, exit 0, no warnings | standard 3 (5 theorems) | Yes. The gauge action is the expression of `ChallengeSpec.lean:17`, checked by plugging `moment_gaugeAct` into the `invariant` field | `#print axioms` missing for `hop_pow_gaugeAct` (checked in copy) |
| `VariationProduct.lean` (60) | Yes, exit 0, no warnings | standard 3 (3 theorems) | True statements, elementary | Prose overstates what follows ("needs one coupling per factor"), see C5 |
| `GeneralityProbes.lean` (68) | Yes, exit 0, no warnings | standard 3 | Yes | None |
| `BrokenSU4Probe.lean` (203) | Yes, exit 0, no warnings | standard 3 (7 theorems checked) | Yes | None |
| `SU4Skeleton.lean` (43) | Yes, exit 0, no warnings, 10.95 GB | standard 3 | Yes (conditional). Its `SU4` equals `SUN 2` by `rfl` (copies), so `ReviewSUN.suN_simple 2` discharges its hypothesis | Same name `su4Theory` as the unconditional `ReviewSUN.su4Theory` |

## A. Compilation, axioms, escape hatches

Commands (all from the clone root, `export PATH=$HOME/.elan/bin:$PATH`):

```sh
for f in VariationSUN VariationCharge VariationAnisotropic VariationGaugeNetwork \
         VariationProduct GeneralityProbes BrokenSU4Probe SU4Skeleton; do
  /usr/bin/time -f "WALL=%e s MAXRSS=%M KB" lake env lean ../review/lean/$f.lean \
    > ../review/work/verify/logs/$f.log 2>&1; echo "EXIT=$?" >> ../review/work/verify/logs/$f.log
done
```

Trimmed output (`review/work/verify/logs/*.log`); every file printed nothing besides its axiom lines:

```
VariationSUN:   suN_simple, suNTheory, su3Theory, su4Theory, su5Theory
                -> [propext, Classical.choice, Quot.sound]   WALL=5.07 s MAXRSS=11062108 KB EXIT=0
VariationCharge: centre_in_U1, charge_congruence, singlet_charge -> same 3   WALL=2.64 s EXIT=0
VariationAnisotropic: converges_iff, compactified_empty -> same 3           WALL=2.75 s EXIT=0
VariationGaugeNetwork: hop_star, hop_gaugeAct, moment_gaugeAct -> same 3    WALL=2.67 s EXIT=0
VariationProduct: energy_split, slope_ratio -> same 3                       WALL=2.68 s EXIT=0
GeneralityProbes: not_simple_of_abelian/_central/_proper_ideal -> same 3    WALL=2.60 s EXIT=0
BrokenSU4Probe: lie_le, Z_mem, not_simple -> same 3                         WALL=3.06 s EXIT=0
SU4Skeleton: su4Theory -> same 3                     WALL=3.82 s MAXRSS=10951388 KB EXIT=0
```

These agree with the reviewer's logs 40–47.

Extra `#print axioms`, in copies (the originals are untouched):

- `work/verify/SUNCheck.lean`: `mem_lie_of_reflection, A_mem, S_mem, Hd_mem, diag_sum_zero, filt_apply, extract, spread, all_A, two_smul_skew, ideal_eq_top, suN_size`. All give the same 3 axioms.
- `work/verify/MiscChecks.lean`: `omega_isPrimitiveRoot, Z_ne, commutes_D, Z_central, su3u1_le_su4, hop_pow_gaugeAct, link_gaugeAct, block_mul`, plus the already printed ones. All 19 lines give the same 3 axioms.
- `work/verify/AnisoVacuity.lean`: `regular_of_isotropic`, `converges_iff`, `compactified_empty`. All give the same 3 axioms.

Escape-hatch grep over the eight files (`sorry|admit|axiom|native_decide|unsafe|implemented_by|opaque|partial|macro|elab|notation|set_option|include|omit|extern|attribute|instance|run_cmd|#eval`):

```
set_option autoImplicit false     (all eight files, line 7–14)
VariationSUN.lean:285-287  variable (I ...) (hid : ∀ X ∈ (SUN m).lie, ∀ Y ∈ I, X * Y - Y * X ∈ I)
                           include hid
VariationSUN.lean:393      omit hid in   (two_smul_skew)
private defs/lemmas:       VariationSUN.lean:194,197,212; VariationCharge.lean:16,27,30; BrokenSU4Probe.lean:17,65,67,80,85
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `opaque`, `partial`, custom `macro`/`elab`/`notation`, `instance` or `#eval` occurs. The only option set is `autoImplicit false`.

## B. Does `suN_simple` say what is claimed?

**(i) Carrier.** `VariationSUN.lean:25-38`:

```lean
abbrev SUN (m : ℕ) : Gauge where
  n := m + 1
  imageGroup := { carrier := {X | X.val.det = 1} ... }
  closed_imageGroup := isClosed_eq (show Continuous fun X : GaugeU (m + 1) => X.val.det from by fun_prop) continuous_const
```

`GaugeU (m+1) = Matrix.unitaryGroup (Fin (m+2)) ℂ` (`YM/Gauge/MatrixGroup.lean:20`), so the carrier is exactly {U ∈ U(m+2) | det U = 1} = SU(m+2), and closedness is proved. Checked in the copy:

```lean
example (m : ℕ) (U : Matrix.unitaryGroup (Fin (m+2)) ℂ) :
    U ∈ (ReviewSUN.suN m).image ↔ U.val.det = 1 := Iff.rfl      -- accepted
```

**(ii) Same construction as the submission's SU(2).** `ConcreteSU2.lean:8-10` builds `su2 := ⟨G.n, G.imageGroup, G.closed_imageGroup, G.lie, fun _ => Iff.rfl⟩` from `SUtwo` (`YM/Next/FOUNDATIONS/SU2.lean:36-46`). `VariationSUN.lean:561-562` uses the same tuple. The carrier and closedness proof of `SUN` are textually those of `SUtwo` with `1` replaced by `m + 1`. `lieAlgebra := (SUN m).lie` has carrier `Generates`, `∀ t, exp (t • X) ∈ range G.mat` (`YM/Gauge/Lie.lean:26,121-130`), and the `generates` field closes by `Iff.rfl`. Because `generates` is an `↔` against the image, any `GaugeGroup` with this image has this Lie algebra, so the field is the true Lie algebra of SU(m+2).

**(iii) No weakening.** `#check (ReviewSUN.suN_simple : ∀ m : ℕ, YangMills.GaugeGroup.IsSimple (ReviewSUN.suN m))` is accepted, and `#check @ReviewSUN.suN_simple` prints `∀ (m : ℕ), (ReviewSUN.suN m).IsSimple`. The theorem takes no hypotheses. The section variable `hid` (`VariationSUN.lean:286-287`) becomes an explicit argument of the section's lemmas:

```
@ReviewSUN.ideal_eq_top : ∀ {m : ℕ} (I : Submodule ℝ (ReviewSUN.Mat m)),
  (∀ X ∈ (ReviewSUN.SUN m).lie, ∀ Y ∈ I, X * Y - Y * X ∈ I) →
    I ≤ (ReviewSUN.SUN m).lie → I ≠ ⊥ → I = (ReviewSUN.SUN m).lie
```

`suN_simple` supplies it from the ideal hypothesis of `IsSimple` (`VariationSUN.lean:574-577`). The `abbrev`s (`Idx`, `Mat`, `SUN`, `suN`) are plain reducible aliases and hide nothing.

**(iv) Instance types.** A `run_cmd` in the copy takes the body of `YangMills.JointExistence`, instantiates `g`, checks that the conclusion does not depend on the hypothesis, and compares it with the declared types:

```
ReviewSUN.suNTheory: syntactically equal to JointExistence body at its group = true; reducible defeq = true
ReviewSUN.su3Theory: ... = true; ... = true
ReviewSUN.su4Theory: ... = true; ... = true
ReviewSUN.su5Theory: ... = true; ... = true
YangMills.su2Theory: ... = true; ... = true
```

**(v) m = 0.** Both are accepted:

```lean
example : ReviewSUN.SUN 0 = YM.Next.Foundations.SUtwo := rfl
example : ReviewSUN.suN 0 = YangMills.su2 := rfl
```

So `suN_simple 0` is a second proof of `su2Simple` for the same object, and `suNTheory 0` has the type of `su2Theory`.

**Mathematical sense of the key lemmas** (read and checked by hand):

- `mem_lie_of_reflection` (`:47-85`). From `R X R = -X` and `R² = 1`, `exp(-sX) = R exp(sX) R`, so `det(exp sX)² = det(exp(-sX))·det(exp sX) = 1`. Then `det exp(tX) = det(exp(tX/2))² = 1`. Unitarity comes from skew-Hermiticity. Sound. It avoids `det exp = exp tr`, which is listed under TODO at `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:57-59` (I confirmed this).
- `diag_sum_zero` (`:223-232`). If `Σy ≠ 0`, take `t = π/Σy`: `det exp(t·i·diag y) = e^{iπ} = -1 ≠ 1`. Sound.
- `filt_apply` (`:259-270`). `ad(H_jk)` acts on `E_ab` by `i(r_a - r_b)` with `r ∈ {1,-1,0}`. `(ad⁴ + ad²)/12` gives `(d⁴ - d²)/12`, which equals 1 for `|d| = 2`, i.e. `(a,b) ∈ {(j,k),(k,j)}`, and 0 for `d ∈ {0,±1}`. Correct.
- `extract` (`:293-345`). The filtered element keeps `x+iy` at `(j,k)` and `-(x-iy)` at `(k,j)`. One more `ad(H_jk)` and a real 2×2 inversion with determinant `x²+y² ≠ 0` gives `A_jk`. Correct.
- `two_smul_skew` (`:395-425`). The `(i,j)` term `Re Y_ij·A_ij + Im Y_ij·S_ij` equals `Y_ij E_ij + Y_ji E_ji` because `Y_ji = -conj Y_ij`. Summing over all ordered pairs gives `2Y`. Correct, and the diagonal terms `S_ii = 2i E_ii` are kept.
- `ideal_eq_top` (`:428-554`). A nonzero element yields some `A_jk`, either directly or, for a diagonal element, after one bracket with `A_jk`, using `diag_sum_zero` to find two distinct entries. Spreading then gives every `A_pq`, `S_pq` and `H_p0`. The diagonal part of an arbitrary `Y` is traceless by `diag_sum_zero` and is written through `H_i0`. Correct.

The simplicity proof uses the project lemmas `YM.Gauge.bracket_mem` and `generates_skew` from `YM/Gauge/Lie.lean` (`VariationSUN.lean:187,430,474,490`). The file header states this. Those lemmas are covered by the reviewer's whole-project replay (log 33).

**Independent kernel replay.** In `work/verify/SUNCheck.lean` I collected every declaration of the current file reachable from `suN_simple, suNTheory, su3Theory, su4Theory, su5Theory`. The run rejects unsafe, partial and axiom declarations, re-imports the same module set into a fresh environment, and calls `Lean.Environment.replay`:

```
SUN_REPLAY_START localDecls=65 externalRefs=818 names=[ReviewSUN.Hd_of_A, ReviewSUN.filt._proof_1, ...]
SUN_REPLAY_PASS localDecls=65
WALL=22.11 s MAXRSS=25837976 KB  EXIT=0
```

The replayed `type` and `value` of each root are compared with the originals. Together with the reviewer's replay of the project (log 33, 93,999 declarations), this covers the full dependency cone of `su4Theory` apart from Lean core, Batteries and Mathlib.

## C. Vacuity and strength of the other statements

**C1. `CompactifiedWilsonLimit` (`VariationAnisotropic.lean:127-133`): degenerate as formalized.** I proved both of the following in `work/verify/AnisoVacuity.lean`, a verbatim copy of lines 1–148 of the file followed by my additions. It compiles with exit 0, no warnings, 8.2 s, and all three theorems depend on `[propext, Classical.choice, Quot.sound]`:

```lean
-- AnisoVacuity.lean:325
theorem compactified_trivial (g : GaugeGroup) (K : Finset Axis) (Lc : ℕ+) :
    CompactifiedWilsonLimit g K Lc

-- AnisoVacuity.lean:338
theorem no_token_of_compact (C : WilsonFamilyA g) (i : Axis) (Lc : ℕ+)
    (hK : ∀ p, C.period p i = Lc) (v : C.Token) (order : ℕ → ℕ)
    (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : ¬ C.ConvergesA order u

-- AnisoVacuity.lean:362
theorem compactified_forces_empty (g : GaugeGroup) (K : Finset Axis) (hK : K.Nonempty) (Lc : ℕ+)
    (C : WilsonFamilyA g) (hper : ∀ p i, i ∈ K → C.period p i = Lc)
    (hconv : ∃ order : ℕ → ℕ, ∃ u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ,
      C.ConvergesA order u) : IsEmpty C.Token
```

How the witness of `compactified_trivial` works (`trivialFamily`, `:274`):

- `Token := Empty`;
- `period p i := if i ∈ K then Lc else p+1`, `denominator N := N+2`, `beta N _ := log(N+2)`, so the running ratio is exactly 1;
- the Haar probability measure is built from Mathlib alone, after proving U(k+1) compact (`isCompact_unitary`, `:156`);
- regularity holds vacuously over `Empty`;
- in `ConvergesA` the only surviving case is `n = 0`. There `smear = t 0 · (wilsonLawA …)(univ) = t 0`, by an anisotropic copy of the reviewer's `wilsonLaw_isProbability`. The right side is `∫ t·1 = t 0`, because the volume of `Points 0` is 1 (`volume_points_zero`, `:262`).

No simplicity and no use of `JointExistence` is needed.

The obstruction has this source. `ConvergesA` (`VariationAnisotropic.lean:76-81`) keeps the public form `(∀ᶠ k, C.suitable (order k) t) ∧ …` as a *conjunct* for every test function `t`. With a fixed period `Lc` in direction `i`, a bump function centred at a point with coordinate `Lc` is never suitable. So any family with one token fails `ConvergesA`. In the public statement the same conjunct is harmless because every period grows (`periodStrict`).

Consequences:

- For `K ≠ ∅` the proposition is equivalent to the existence of a token-free family with the period constraints, which always exists. It carries no information about Yang–Mills theory and would be false for any genuine compactified construction with insertions.
- `compactified_empty` (`:136`) is true, but its hypotheses `JointExistence` and `g.IsSimple` are superfluous.
- A usable target needs at least two changes. First, make suitability in the compact directions a hypothesis on `t` (support in `|x_a| < Lc/2` for `a ∈ K`), or use test functions periodic in those directions. Second, add a non-triviality clause, such as a nonempty token type with a non-constant insertion, or the reconstruction and trace clauses.

**C2. `converges_iff := Iff.rfl`: meaningful.** I renamed the `…A` identifiers and diffed `VariationAnisotropic.lean:22-96` against `PublicWilson.lean:20-91` plus `ChallengeSpec.lean:12-22`. The bodies of `plaquette`, `wilsonEnergy`, `wilsonLaw`, `mesh`, `place`, `finiteMoment`, `smear`, `Converges` and `WilsonRegularity` are identical. The differences are the intended ones:

- `period : ℕ → Axis → ℕ+`;
- the `side` abbreviation;
- `suitable` reading `C.period p a` per direction;
- `periodStrict` dropped from the structure;
- `ZMod (C.side N p i).val` in `localSupport`.

`SeparatedTest` and `separated` are reused from the public namespace. With `period := fun p _ => C.period p`, everything β-reduces to the public terms, so the `rfl` checks a real definitional identity. `regular_of_isotropic` closes by the same reduction.

**C3. `moment_gaugeAct`.** `VariationGaugeNetwork.lean:111` uses `fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹`, character for character the expression of `ChallengeSpec.lean:17`. Checked in Lean (`MiscChecks.lean`): for any `C : WilsonFamily g` whose insertions equal `moment k U`, the exact proposition of the `invariant` field follows from `moment_gaugeAct`. `hop U` is a block matrix `Matrix (Site l) (Site l) (Blk g)`, and the `star` of such a matrix is the full conjugate transpose, so `hop_star` is genuine self-adjointness. `hop_gaugeAct` plus `gaugeMat_mul_star` and `star_mul_gaugeMat` give conjugation by a block-diagonal unitary. Contents are as claimed. The hopping expansion is absent, as stated.

**C4. `centre_in_U1` and `charge_congruence`.** `VariationCharge.lean:19,22` and `BrokenSU4Probe.lean:20,26` are textually identical, and the copy checks `ReviewCharge.dr = ReviewBrokenSU4.dr := rfl` and `ReviewCharge.Z = ReviewBrokenSU4.Z := rfl`.

- `centre_in_U1` is a correct computation: `exp((2π/3)Z) = diag(ω,ω,ω,1)`.
- `charge_congruence` and `singlet_charge` are facts about a primitive cube root of unity, with no group or representation in them.
- The file does not show that `Z` lies in the Lie algebra of S(U(3)×U(1)); that is `BrokenSU4Probe.Z_mem`. It also does not show that `diag(ω,ω,ω,1)` is central in the SU(3) block.

The prose of Note 10, section 2, already says that the link to triality is argued in words.

**C5. `energy_split` and `slope_ratio`.**

- `energy_split` needs `0 < m₁, m₂`, and with those hypotheses the identity is correct. It concerns arbitrary block-diagonal matrices, not unitaries or groups.
- `slope_ratio` has no hypothesis on `ℓ`. Under Lean's `x/0 = 0` the statement stays correct, because `(w·β/ℓ)/w = β/ℓ` holds also at `ℓ = 0`. A check in the copy: `ReviewProduct.slope_ratio (fun _ => 1) (fun _ => 0) 1 2 0 0 … : (0:ℝ)/1 = 0/2` is accepted.
- The lemmas show that one coupling fixes the ratio of the two effective couplings. They do not show that a product group needs two couplings.
- With the note's own one-loop slopes (Note 2, section 5: slope 11N²/(12π²) for SU(N) in the defining representation) and weights `m_i/(m₁+m₂)`, the condition `s₁/w₁ = s₂/w₂` reads `m₁ = m₂`. That is my hand computation, unformalized. So for SU(N)×SU(N) in N ⊕ N the single coupling is consistent at one loop, and the need for a second coupling arises only for unequal factors.

## D. Prose versus code

Most serious first.

1. **Note 10, line 83:** "the target for a nonempty set K of compact directions is a statement without proof. By itself it constrains little, like the clause `wilson` of the public statement taken alone". The same claim appears in `VariationAnisotropic.lean:124` ("It is a statement, offered without proof for `K ≠ ∅`") and in **Note 4, line 59** ("For a nonempty set of compact directions it is a statement without proof"). **README line 56** has "the anisotropic target is stated, with no proof beyond the isotropic case".
   - Correction: the proposition is proved for every `g`, `K`, `Lc` by a token-free family (`compactified_trivial`). For `K ≠ ∅`, every witness has an empty token type (`compactified_forces_empty`), because `ConvergesA` demands eventual suitability of every test function while the compact period stays fixed.
   - The definition needs repair (C1) before it can be called a target.
   - "Follows from the public theorem" (Note 10, line 83; Note 4, line 59) should read "holds outright; `compactified_empty` derives it from the public theorem as well".
2. **Note 2, section 7** ("The algebra behind the need for one coupling per factor is checked in `lean/VariationProduct.lean`") and **`VariationProduct.lean:10`** ("This is the algebra behind the statement that a product group needs one coupling per factor").
   - Correction: the file checks that one coupling fixes the ratio `m₁ : m₂` of the factor couplings, and that two slopes are compatible only in the ratio of the weights. Whether that fails depends on the slopes. For equal factors it holds (C5).
3. **Note 10, line 13:** "One item changes the formal status of the theorem". The theorem is unchanged. The review adds corollaries: unconditional instances for every SU(N), N ≥ 2 (`suNTheory`), in particular SU(3), SU(4), SU(5). Suggested wording: "One item adds formal instances: …".
4. **Note 10, line 7:** "Every theorem named here | Compiled … logs `logs/40-…` to `logs/47-…`; each depends on `propext`, `Classical.choice`, `Quot.sound` only". The logs contain no axiom line for `regular_of_isotropic`, `hop_pow_gaugeAct` or `block_mul`, and `CompactifiedWilsonLimit` is a definition. My copies confirm the three theorems use the standard axioms. Fix: add their `#print axioms` lines, or cite this report.
5. **Note 10, line 125:** "Each file ends with `#print axioms` for its main statements". Same gap as item 4. `VariationAnisotropic.lean:150-151` omits `regular_of_isotropic`, `VariationGaugeNetwork.lean:129-131` omits `hop_pow_gaugeAct`, and `VariationProduct.lean:59-60` omits `block_mul`, although Note 10's table lists all three as main statements.
6. **Note 10, line 8:** "Independent check | VERIFICATION_STATUS". No file of that name exists in `review/`. Point it at this report or at `VERIFICATION.md`.
7. **Note 3, line 7** (basis table): it lists `BrokenSU4Probe.lean`, `SU4Skeleton.lean` and logs 41–42 for "Lean statements about SU(4)". The unconditional SU(4) instance that the note now cites (lines 13, 21, 55) lives in `VariationSUN.lean`, log 43. Add it.
8. **Note 3, section 1 code block** shows `theorem su4Theory (h : su4.IsSimple)` from `SU4Skeleton.lean`. Lines 13 and 21 cite the unconditional `su4Theory` in `VariationSUN.lean`. The two theorems share a short name; write `ReviewSU4.su4Theory` (conditional) and `ReviewSUN.su4Theory` (unconditional). The link is now machine-checked: `CopySUN.SUN 2 = CopySU4Skel.SU4 := rfl` in `MiscChecks.lean`.
9. **Note 10, section 6** and README lines 69–72 give paths `independent-review/lean/…`. In this tree the files are in `review/lean/`, and the command from the clone root is `lake env lean ../review/lean/<File>.lean`. README line 19 explains `review/…` but not `independent-review/…`. Also state that `VariationSUN.lean` and `SU4Skeleton.lean` need about 11 GB of RAM.
10. **README line 55:** "A classical fact, newly formalized here". Supported relative to the pinned Mathlib: I found `LieAlgebra.IsSimple` and `isSimple_of_isAtom`, and nothing for sl(N) or su(N), in `Mathlib/Algebra/Lie`. It is also supported relative to the submission. It is unsupported beyond those. Suggested: "new relative to the submission and the pinned Mathlib".

Checked and accurate:

- Note 10: line counts 615/85/151/131/60; the theorem names; the six-step proof outline; the Mathlib TODO on `det exp = exp tr`.
- Note 10, line 43: "defined like the submission's SU(2)". It is stronger than stated, since `rfl` holds at m = 0.
- Note 2: line 13; the table row "SU(N), N ≥ 2 … machine-checked here as `suN_simple`"; section 6, including the 112 lines of `YM/Examples/SU2.lean` (confirmed with `wc -l`).
- Note 3: answer in brief, table row SU(4), section 2.
- Note 6, section 2: the description of `VariationGaugeNetwork.lean`.
- Note 7: basis table and section 2, which mark the triality step as informal.
- README line 45.

## E. Other points for a reader

- The SU(N) instances inherit exactly the strength of the public theorem. The reviewer's own probes (`SpecProbes.lean`, `ZeroInsertionProbe.lean`) bear on what `Properties` constrains. Nothing in `VariationSUN.lean` changes that.
- The simplicity proof does not need `Solution`. Moving the last section (instances) to a separate file would let a reader check `suN_simple` with about 6.7 GB instead of 11 GB.
- Four definitions of the same SU(4) exist: `ReviewSUN.SUN 2`, `ReviewSU4.SU4`, `ReviewBrokenSU4.SU4`, and `SUtwo` for m = 0 in the SU(2) case. All are definitionally equal to `SUN` at the matching m (`rfl` checks above).
- `VariationCharge.lean` and `BrokenSU4Probe.lean` duplicate `dr`, `Z`, `phase` and `exp_smul_Z`. They agree today; any edit must touch both.

## Scratch files

| File | Content | Result |
|---|---|---|
| `review/work/verify/SUNCheck.lean` (718 lines) | Copy of `VariationSUN.lean` plus `import ConcreteSU2`, `import Lean.Replay`; axiom prints, `rfl` comparisons with `SUtwo`/`su2`, instance-type comparison, kernel replay | Exit 0, 22.1 s, 25.8 GB; log `work/verify/logs/SUNCheck.log` |
| `review/work/verify/AnisoVacuity.lean` (377 lines) | Copy of `VariationAnisotropic.lean:1-148` plus `compactified_trivial`, `no_token_of_compact`, `compactified_forces_empty` and supporting lemmas (`isCompact_unitary`, `haarP`, `wilsonLawA_isProbability`, `volume_points_zero`, `trivialFamily`) | Exit 0, 8.2 s; standard axioms; log `work/verify/logs/AnisoVacuity.log` |
| `review/work/verify/MiscChecks.lean` (547 lines) | Bodies of `VariationCharge`, `BrokenSU4Probe`, `VariationGaugeNetwork`, `VariationProduct`, plus copies of `SUN` and the skeleton's `SU4`; cross-file `rfl` checks, the `invariant`-shape check, 19 axiom prints | Exit 0, 3.4 s; log `work/verify/logs/MiscChecks.log` |
| `review/work/verify/public_defs.txt`, `aniso_defs.txt` | Inputs of the definition diff in C2 | — |

## What I could not check

- I did not re-run the project's own replay (log 33). The SU(N) instances rely on it for `YangMills.jointExistence` and for `YM.Gauge.bracket_mem` and `generates_skew`.
- The physics in the notes (constants, one-loop slopes, Kaluza–Klein and spectral-triple remarks) lies outside the Lean files and was read only where it bears on claims about the code.
