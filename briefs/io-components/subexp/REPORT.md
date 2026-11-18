# Foundations: subexponential smallness (report)

- **Branch:** `foundations/subexp`, pushed to origin. No PR opened.
- **Head:** `cbce64d1c135c710b7c036968ed9d4f21414aa72`
  - Parent: `a2bf4bac0d545fce1fcb4014ef12b44f9651a658`.
  - One commit, SSH-signed (`gpgsig` present). Message `Foundations: subexponential smallness of advantage functions`
    plus the two required trailer lines.
- **Files:**
  - New: `TCSlib/Cryptography/Foundations/Subexponential.lean`, 300 lines, 16,665 bytes, all lines ≤ 100 characters.
  - Facade `TCSlib/Cryptography/Foundations.lean`, +3 lines: the import and one `## Contents` entry. No other file was
    edited.

## Declarations (`namespace TCSlib.Cryptography`)

| Declaration | Statement |
|---|---|
| `SubexpSmall c μ` (def) | `∃ n₀ : ℕ, ∀ n ≥ n₀, \|μ n\| ≤ (2:ℝ) ^ (-((n:ℝ) ^ c))` (rpow); [JLS26, Def 2.1] |
| `subexpSmall_iff` | the reader for the definition, by `Iff.rfl` (the `negligible_iff` convention) |
| `subexpSmall_iff_eventually` | `SubexpSmall c μ ↔ ∀ᶠ n in atTop, \|μ n\| ≤ 2^(-n^c)` (glue, for `filter_upwards`) |
| `tendsto_rpow_mul_two_rpow_sub` (**private**) | `0 < c → c' < c → Tendsto (fun x:ℝ => x^s * 2^(x^c' - x^c)) atTop (𝓝 0)` |
| `eventually_const_mul_rpow_mul_two_rpow_neg_le` | `0 < c → c' < c → ∀ A s, ∀ᶠ n:ℕ in atTop, A * n^s * 2^(-n^c) ≤ 2^(-n^c')` |
| `SubexpSmall.mono` | `SubexpSmall c μ → (∃ n₀, ∀ n ≥ n₀, \|ν n\| ≤ \|μ n\|) → SubexpSmall c ν` |
| `SubexpSmall.mono_exponent` | `SubexpSmall c μ → c' ≤ c → SubexpSmall c' μ`. No sign condition on `c'`. |
| `SubexpSmall.add` | `SubexpSmall c μ → SubexpSmall c ν → 0 < c → c' < c → SubexpSmall c' (μ + ν)` |
| `SubexpSmall.const_mul` | `SubexpSmall c μ → 0 < c → c' < c → ∀ a, SubexpSmall c' (fun n => a * μ n)` |
| `SubexpSmall.mul_pow` | `SubexpSmall c μ → 0 < c → c' < c → ∀ k:ℕ, SubexpSmall c' (fun n => (n:ℝ)^k * μ n)` |
| `SubexpSmall.negligible` | `SubexpSmall c μ → 0 < c → Negligible μ` |
| `SubexpSmall.comp_of_rpow_le` | `SubexpSmall c μ → 0 ≤ c → 0 < a → (∃ n₀:ℕ, ∀ n ≥ n₀, (n:ℝ)^a ≤ ℓ n) → SubexpSmall (a*c) (μ ∘ ℓ)`; [JLS26, Rem 2.1] |
| `subexpSmall_zero` | `∀ c, SubexpSmall c (fun _ => 0)` |
| `subexpSmall_two_pow_neg` | `SubexpSmall 1 (fun n => (2:ℝ)⁻¹ ^ n)` |
| `SubexpHard adv` (def) | `{α : Type*} (adv : α → ℕ → ℝ)`: `∃ c : ℝ, 0 < c ∧ ∀ D, SubexpSmall c (adv D)`; [JLS26, §1.1, Def 2.1] |
| `subexpHard_iff` | the reader for the definition, by `Iff.rfl` |
| `SubexpHard.negligible` | `SubexpHard adv → ∀ D, Negligible (adv D)` |
| `SubexpHard.comp_of_rpow_le` | the family version of the re-indexing: `SubexpHard adv → 0 < a → (n^a ≤ ℓ n eventually) → SubexpHard (fun D n => adv D (ℓ n))` |

The closure hypotheses are `0 < c` and `c' < c`, not `0 < c' < c`.
- This is weaker than the brief asked for, and it is what lets `SubexpSmall.negligible` be proved through
  `mul_pow` at `c' = 0`.
- `0 < c` is needed: at `c = 0` the factor 2 is not absorbed.

**Adversary type.** `SubexpHard` is generic in `α` and does not use `NUPPT`.
- The `Foundations/*.lean` files import only Mathlib, plus `InformationTheory.StatisticalDistance` (`Experiments`).
- `Complexity.NUPPT` (`Complexity/Randomized/PPT.lean`) brings in the TM layer. It meets `Foundations` only downstream,
  in `Asymptotic/Adversary.lean`, which imports both.
- Assumption files instantiate `α := NUPPT`. The module docstring says so.

## Helpers and duplication searches

The one new helper beyond the requested API is the private `tendsto_rpow_mul_two_rpow_sub`, with the public
eventual bound built on it.
- No Mathlib lemma states this composite.
- It is assembled from the Mathlib lemmas in the first row of the table below.
- Every other proof uses the eventual bound, the file's own lemmas, or Mathlib lemmas directly.

| Searched in `.lake/packages/mathlib` | Result |
|---|---|
| `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop` (`Pow/Asymptotics.lean`) | **used** |
| `isLittleO_rpow_exp_pos_mul_atTop`, `isLittleO_pow_exp_pos_mul_atTop`, `isLittleO_exp_neg_mul_rpow_atTop`, `tendsto_pow_mul_exp_neg_atTop_nhds_zero` | read; subsumed by the `rpow_mul_exp` lemma, which is the one used |
| `isLittleO_rpow_rpow*`, `exp_neg_rpow` decay lemmas | none at `atTop` (only integrals and Gaussian files) |
| `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` | does not exist in this Mathlib (029db123); not needed |
| `Real.rpow_le_rpow_of_exponent_le`, `rpow_le_rpow`, `rpow_mul`, `rpow_add`, `rpow_def_of_pos`, `rpow_neg`, `rpow_natCast`, `rpow_one`, `rpow_zero`, `rpow_neg_one`, `rpow_nonneg`, `rpow_pos_of_pos` | **used** |
| `Filter.eventually_atTop`, `tendsto_natCast_atTop_atTop`, `Tendsto.eventually_ge_atTop`, `gt_mem_nhds`, `ge_mem_nhds`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'` | **used** |

Reuse and checks in TCSlib:
- From `Negligible.lean`, the proofs use `negligible_iff` as the reader, never unfolding `Negligible`.
- `grep -i subexp` over TCSlib finds only `Randomness.subexpBound` (a `⌈2^{n^ε}⌉` time bound with no smallness lemmas)
  and `Derand.seed_time_le_subexp` (`Derandomization/TimeBound.lean`).
- `seed_time_le_subexp` is related but is not the same statement. It gives a natural-number upper bound for
  `2^{ceilRoot} · (n+1)^e`, using `ceilRoot`, in the log domain. Importing it would pull Derandomization into
  `Foundations`.
- **Disclosed:** no re-proof of a TCSlib or Mathlib lemma.
- No existing declaration uses any of the new names. The facade's only downstream modules are root `TCSlib.lean`
  and `audits/garg-ch1-3/Checks.lean`.

## Checks

The checks ran through `scripts/lean_check_tree.sh` with `TCSLIB_OLEANS` set to a `cp -al` copy of snapshot #10
(T `cf6a2266`, map SHA-256 `84d88738…`).
- `a2bf4bac` is Lean-equal to T: `git diff --name-only` over `*.lean`, the toolchain and the manifest is empty, and
  the `TCSlib` trees are identical (`849ee945`).
- I ran one Lean process at a time.

| Module | rc | `error:` | Output |
|---|---|---|---|
| `TCSlib/Cryptography/Foundations/Subexponential` | 0 | 0 | empty (no warnings) |
| `TCSlib/Cryptography/Foundations` (facade) | 0 | 0 | empty |
| `audits/garg-ch1-3/Checks` (opens `TCSlib.Cryptography`; clash check) | 0 | 0 | axiom prints only, no `sorryAx` |

- **Sorry count:** 0. There is no `sorry`, `admit`, `native_decide` or `axiom` in the file.
- **Axioms**, from `#print axioms` in a scratch file outside the tree: all 15 public theorems depend only on
  `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `python3 -I scripts/style_lint.py` on the new file gives 0 findings.
- **Snapshot untouched:**
  - Its `Foundations.olean` and `Negligible.olean` still match the #10 map.
  - It contains no `Subexponential.olean`.
  - The rebuilt facade olean in the copy has link count 1.

## Housekeeping

The following are deleted: the scratch worktree, the olean copy and the scratch logs. The local branch
`foundations/subexp` is kept, and the main checkout's branch is unchanged.

For the merge replay, the downstream to rebuild is the new module, the facade, root `TCSlib` and
`audits/garg-ch1-3/Checks`.
