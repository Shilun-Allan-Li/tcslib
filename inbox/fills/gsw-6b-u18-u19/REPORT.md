# gsw-6b-u18-u19 · final

**Head: `4672ed30d036feb624ca84b4199af19d77f5768f`** (`fill/gsw-6b-u18-u19`, local only).
**Base:** B6 `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc982fd8f79aba755796bb13188922c4655d`.
**Records pin read:** `27e53754d28703907571cacbaf905b441e03c393` (`rulings.md` of the folder, then `COMMON.md`,
`U18-U19/brief.md`, `dup-sweep.md`, the addendum).

**All five targets are proved:** G16 `bootRatio_le_poly`, G17 `decrypt_fheEval_of_ratio` and
`decrypt_leveledEval_of_ratio`, A1 `indCPA_of_dlweAssumption`, A3 `leveledINDCPA_of_dlweAssumption`. So is the one
public helper the brief names, `Parameters.ofFamily_columns_le`. A1 and A3 are proved **from their frozen `heff`
hypotheses**; nothing proves or removes `heff` (EF-R1's job). Neither owned file contains `sorry`. No statement
changed, no hypothesis was added, no efficiency claim was added, and no scope request is open.

Checkpoint 1 (the same head, `4672ed30`, all five targets already proved) was delivered as exchange commit
`5fb0d4b8324f1c5e8d1e64e013f083f0bd154e20`. The final adds nothing to the source. It re-runs every check under the tag
`final` and keeps the checkpoint's evidence beside it (`*-cp1*`).

No sub-agent was used. The brief allows one (`ratio`, for `PolyRatio.lean`), but the unit was small enough for the
lead alone, so the lead wrote both files and all the tooling.

## 1. Inputs, base, records tip, commits

- **Inputs** (`evidence/base/inputs-check.log`). All 17 COMMON §1 files at the records pin `27e53754` match their
  SHA-256 values, so there is no E-INPUT. The folder's `SHA256SUMS` gives **52/52 OK**. `rulings.md` is present.
  It rules Q-6BF-1 to Q-6BF-7 all "A", and this delivery follows those rulings: A1/A3 are filled from `heff` (Q-6BF-1 A),
  and `Parameters.ofFamily_columns_le` is the one public helper (Q-6BF-3 A). The addendum was read: Part 1 and the
  *Lean parallelism* text.
- **Base** (`evidence/logs/base-check.log`). `git rev-parse` gives `bff0567b…` and `845bdc98…`, as expected. The base
  is an ancestor of `cryptography/pass-shelat-ch2-4`.
  - The clone is separate: `/work/tcslib`, cloned without checkout from the host mirror, with `origin` set to GitHub.
  - The base was fetched by hash and by branch name, and `fill/gsw-6b-u18-u19` was branched from it. I stayed on the base.
- **Records tip at delivery:** `eddf183f84fb7ead32236ff26dbf7281979b2f9e`.
  - `git merge-tree --write-tree 4672ed30 eddf183f` is clean: rc 0, tree `6d263c01386ecd48e1bba417c089da0547039289`
    (`evidence/git-merge-tree-final.txt`).

| # | Commit | File |
|---|---|---|
| 1 | `479f6a880a75ba558c8667027070e45963911419` | `GSW/PolyRatio.lean`: `Parameters.ofFamily_columns_le`, G16, G17 ×2, one private glue lemma, three refreshed sketches, the module sentence and a *Main results* entry |
| 2 | `4672ed30d036feb624ca84b4199af19d77f5768f` | `GSW/Asymptotic.lean`: A1, A3, the module sentence |

Both commits are unsigned (`git -c commit.gpgsign=false`; `%G?` = `N`; `gpgsig` count 0). Each touches exactly one
owned file. Author and committer are `Claude <noreply@anthropic.com>`.

## 2. Preflight, cache, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`).
  - `nproc` 4. There is no cgroup memory limit (`memory.limit_in_bytes` = 2^63 − 4096, cgroup v1), so the headroom is
    `MemAvailable` = 16,103,900 kB = **15.36 GiB** (floor 4): pass.
  - **Disk:** 27,930,083,328 B = **26.01 GiB** free on ext4 (floor 12): pass. The re-check before the cache step
    (after installing the toolchain with `elan`) gave 18.05 GiB (floor 8): pass.
- **Packages** (`evidence/logs/packages.log`): 11 present, each matching the manifest's URL and revision; 4 ABSENT
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`); nothing in the order imports them. Last line:
  `package check: PASS`.
- **Cache.**
  - The roots computed from `order.txt` equal `roots.txt`'s **102** (`mathlib-roots.txt`).
  - The store was absent before the fetch (`cache-store.log`), so every archive was downloaded by this session.
  - The narrowed `lake exe cache get` (102 roots) exited 0: "Attempting to download 2339", then 2,339 decompressed,
    with no failed download (`cache-get.log`).
  - There are 0 empty oleans (`cache-check.log`). The cache probe (`import Mathlib.Algebra.BigOperators.Field`) compiles
    through `lean_check_tree.sh` (`cache-probe.log`).
- **Pool** (`evidence/logs/pool.log`; runner `tools/sweep.py`).
  - **3** Lean processes at most, in dependency order, each module through `scripts/lean_check_tree.sh`, one olean tree
    (`/work/oleans`). 3 = `min(nproc 4, 15.4 GiB / 4 GiB)`. The pool was never resized.
  - Seals, liveness runs and base seals ran as at most three parallel processes, each with its own probe directory.
  - Peak RSS of a Lean process: 2,941,712 kB (`NumberTheory/Primality`, bootstrap). There was no shortage: no OOM,
    no exit 137, and `MemAvailable` was ≥ 15 GiB whenever sampled.
- **Bootstrap incidents** (pool.log; both happened before any check):
  1. **Attempt 1 aborted.** My runner hit a bug: Python's `subprocess` reaped children the runner no longer referenced.
     - I had also started editing `PolyRatio.lean` in the working tree during that run.
     - So I discarded every log and olean of attempt 1, restored the owned files to the base, fixed the runner, and
       restarted from scratch.
  2. **Attempt 2's runner disappeared** after 145 modules, with no output. It was a plain background job.
     - I resumed it under `setsid` from its TSV, keeping the modules with rc 0 and an olean.
     - During the resume the host showed heavy I/O pressure: `/proc/pressure/io` avg10 94, 1–4 MB/s reads after the
       page cache emptied. Lean waited on page reads for a few minutes, then finished.
  - The final bootstrap record is one row per module, 224 rows.
- **Who did what.** One worker, the lead, wrote everything. No sub-agent.

## 3. The owned files

| File | Base | Head | Fill | Max width (base → head) |
|---|---|---|---|---|
| `GSW/PolyRatio.lean` | 179 | 245 | +66 (helper 11, glue 13) | 98 → 98 |
| `GSW/Asymptotic.lean` | 340 | 458 | +118 | 99 → 99 |

The fill is 184 lines, below the brief's estimate of 290–500. The frozen statements G12, L3, G13 and L5, and phase 5's
`distAdv_encrypt_le_of_width`, carry all the analysis, so the fill is glue and bookkeeping. `Asymptotic.lean` is 458
lines, under the 604 projected (G6B-F07) and under 600 and 1,000.

## 4. Per target

### Helper `Parameters.ofFamily_columns_le` (public, `PolyRatio.lean:106`)

`(Parameters.ofFamily F κ).columns ≤ (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ`, exactly as the brief
states it (the `Nat` form; the `PolyExpr` alternative was not needed: U18-U19-W1).

**Proof:** `rw [Parameters.columns_eq, Parameters.ofFamily_lwe, Parameters.ofFamily_width]`, then
`Nat.mul_le_mul_right _ (Nat.add_le_add_right (F.dimension_le κ) 1)`.

The docstring has the words, the formula and "Glue.". It is a pure insertion after `pBoot_eq` and before G16, with a
*Main results* entry. It is standard-only (`[propext, Quot.sound]`) and sealed with its own liveness pair (§5, C6).

### G16 `bootRatio_le_poly`

**Route.**
- **Readers.** `ℓ = r(κ)` (`Parameters.ofFamily_width`); `m ≤ s(κ)` (`Parameters.ofFamily_lwe`, then `F.samples_le`);
  `N ≤ N̂` (the helper).
- **`⌈log₂ N⌉ ≤ N ≤ N̂`:** `(Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le`, then the helper.
- **G13** `bootNoise_le` at `β = m·B`.
- **`pBoot`** is read through `pBoot_eq` and `PolyExpr.eval_mul/_pow/_add/_const`.
- **A three-step `calc`:** `gcongr` with G13; `ring` for `8·4^33·2 = 2^70` and the regrouping; then `gcongr` with
  `hw`, `hN`, `hlog` and `hm`.

### Private glue `two_mul_width_lt_of_ratio` (`PolyRatio.lean:158`)

Glue: if `(pBoot F).eval κ * B κ < (F.parameters κ).modulus` and `y ≤ bootNoise P (m·B κ)` (`P = ofFamily F κ`), then
`2 * (P.width * y) < P.lwe.modulus / 2`.

**Proof:** G16, `Nat.mul_le_mul_left`, `modulus_ge_two`, `rw [Parameters.ofFamily_lwe]`, then `omega`. This is the
sketch's "`8·y ≤ pBoot·B < q` gives `2y < ⌊q/2⌋`".

It is used three times: once by G17 pure, and twice by G17 leveled (at `y = bootNoise P (m·B)` and at `y = m·B`).
That is why it is a lemma and not inlined.

### G17 `decrypt_fheEval_of_ratio`

`exact decrypt_keygen_fheEvalCircuit P (F.noise κ) rg (B κ) hχ R Cc hC x R' (two_mul_width_lt_of_ratio F B κ hq le_rfl)`.
G12 (U14-U16) is applied as stated.

### G17 `decrypt_leveledEval_of_ratio`

**Route.**
- **`hin`:** `m·B ≤ bootNoise P (m·B)`, by `bootNoise_eq` and a two-step `calc`:
  - `N ≥ 1` from `Nat.pos_of_neZero` with the instance `Parameters.neZero_columns`, and `Nat.le_mul_of_pos_left` twice;
  - `1 ≤ 4^(decDepth P + 1)` from `Nat.one_le_pow`.
- **Then L3** `decrypt_keygen_leveledEvalCircuit` (U14-U16), with `hsep` and `hin` both from the glue.

### A1 `indCPA_of_dlweAssumption`

**Route.**
1. `reductionEfficient_iff` on `heff` at `μ = false` and `μ = true` gives `D₀` and `D₁`. Their advantages are
   negligible by `LWE.dlweAssumption_iff`.
2. `EnsembleLemmas.negligible_polyExpr_mul` (`EnsemblesLemmas.lean:377`) at `N̂ = (d + 1)·r`, with
   `negligible_two_pow_neg`. Then `Negligible.add` twice and `Negligible.mono` with `n₀ = 0`.
3. At each `κ`, `distAdv_encrypt_le_of_width` with `w = F.residueBits.eval κ`.
   - `q ≤ 2^w` comes from `F.modulus_le_pow`.
   - `hm κ` is read through `Parameters.ofFamily_lwe`.
4. `N·2^{−κ} ≤ N̂·2^{−κ}` comes from the helper (`exact_mod_cast`), after `PolyExpr.eval_mul/_add/_const`.
5. `distAdv ≥ 0` from `distAdv_def` and `abs_nonneg`, then `abs_of_nonneg` and `le_abs_self`. `linarith only` finishes.

**Standard-only** (`[propext, Classical.choice, Quot.sound]`): it uses phase 5's proved bound.

### A3 `leveledINDCPA_of_dlweAssumption`

**Route.**
1. `leveledReductionEfficient_iff` on `heff` at `μ = false` and `μ = true` gives `D₀` and `D₁`, each with a level part
   and a challenge part.
2. The negligible majorant is `(2·L·N̂ + 1)·(2·(adv D₀ + adv D₁) + N̂·2^{−κ})`. It is
   `negligible_polyExpr_mul (.add (.mul (.mul (.const 2) L) N̂) (.const 1))` applied to
   `((hneg₀.add hneg₁).const_mul 2).add hstat`, then `Negligible.mono`.
3. At each `κ`:
   - **L5** `distAdv_leveledView_le` (U15-U17) at `(false, true)`;
   - **`Regev.two_extractionError_le`** with `q ≤ 2^r` and `hm` (read through `ofFamily_lwe`), so `2·(N·ε) ≤ N·2^{−κ}`;
   - **each level pair** is at most `2·(a₀ + a₁) + 2·N·t` (`levelTerm_eq` twice, the four level dominations,
     `linarith only`);
   - **the double sum** is at most `L·(N·(…))` (`Finset.sum_le_sum` twice, then `Finset.sum_const`,
     `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`);
   - **the challenge term** is at most `2·a₀ + N·t` (`challengeTerm_eq`, `D₀`'s challenge part for both `μ'`);
   - `aᵢ ≥ 0` via the challenge domination and `LWE.decisionAdvantage_eq`, `distAdv_def`, `abs_nonneg`.
4. With `N ≤ N̂` (the helper, cast), one monotonicity step (`mul_le_mul`) and `linarith only` finish. The slack is
   `2·L·N̂·(a₀ + a₁) + 2·a₁ + (N̂ − N)·t ≥ 0`.

### Readers used

`evidence/rule10/reader-census.txt` lists every foreign definition read, with its reader's `path:line`: **MISSING 0**.

`Parameters.ofFamily`'s body is never read. Only `ofFamily_lwe` and `ofFamily_width` are used, in both files
(type-level Rule 10, Gate 46).

### Imports

None added.

### Sketches refreshed (statement prose before `**Proof sketch.**` untouched; the frozen check passes)

- **G16.**
  - Old: "`bootNoise_le` (G13) at `β = m·B`. Read `P` through `Parameters.ofFamily_lwe`, `Parameters.ofFamily_width`,
    `Parameters.columns_eq`, and `pBoot` through `pBoot_eq` and `PolyExpr.eval` (notation). Bound `n ≤ d(κ)` and
    `m ≤ s(κ)` by the family's `dimension_le` and `samples_le`, so `N = (n + 1)·ℓ ≤ N̂`; `⌈log₂ N⌉ ≤ N`
    (`Nat.clog_le_iff_le_pow` with `N < 2^N`, `Nat.lt_two_pow_self`), so `X ≤ ℓ + N̂ + 3`; then monotonicity of
    products and powers (`Nat.mul_le_mul`, `Nat.pow_le_pow_left`) and `8·4^33·2 = 2^70` (`norm_num`)."
  - New: "`bootNoise_le` (G13) at `β = m·B`. Read `P` through `Parameters.ofFamily_lwe`, `Parameters.ofFamily_width`,
    and `pBoot` through `pBoot_eq` and the `PolyExpr.eval_*` equations. Bound `m ≤ s(κ)` by the family's
    `samples_le`, and `N = (n + 1)·ℓ ≤ N̂` by `Parameters.ofFamily_columns_le` (`Parameters.columns_eq` with
    `dimension_le`); `⌈log₂ N⌉ ≤ N` (`Nat.clog_le_iff_le_pow` with `N < 2^N`, `Nat.lt_two_pow_self`), so
    `X ≤ ℓ + N̂ + 3`; then `8·4^33·2 = 2^70` (`ring`) and monotonicity of products and powers (`gcongr`:
    `Nat.mul_le_mul`, `Nat.pow_le_pow_left`)."
- **G17 pure.** "…follows from G16 (`bootRatio_le_poly`) and `hq`:" became "…follows from G16 (`bootRatio_le_poly`)
  and `hq` (the private glue `two_mul_width_lt_of_ratio`):". The rest of the paragraph is unchanged in wording,
  re-wrapped to width 100.
- **G17 leveled.** "(`two_mul_width_lt_of_ratio` at `y = bootNoise P (m·B)` and at `y = m·B`)" was inserted after
  "as in `decrypt_fheEval_of_ratio`".
- **A1, A3:** unchanged; they describe the delivered proofs.
- **Module docstrings.**
  - `PolyRatio.lean`: "All three are admitted statement-phase targets." became "All three are proved here.", and the
    helper's *Main results* entry was added (brief).
  - `Asymptotic.lean`: "Both are admitted statement-phase targets." became "Both are proved here.".

## 5. Checks (runner `tools/lead/checks.sh`, log `evidence/checks-final.log`; checkpoint 1's run: `checks-cp1.log`)

- **C1 Bootstrap and sweep.**
  - Bootstrap of `order.txt` at the base: **224/224 rc 0, 0 errors** in both forms, and 42 `sorry` warnings
    (`evidence/build/bootstrap/sweep.tsv`, logs beside it).
  - The census equals `base-sorries.txt` name by name, **42 in 16** (`build/sorry-census-base.txt`).
  - All 224 sources equal `SOURCE-SHA256SUMS` (`build/source-binding-base.txt`).
  - Head sweep of the 5 `UNIT-DOWN` modules (PolyRatio, Asymptotic, `GSW`, `Homomorphic`, `AdvancedEncryption`):
    these are the changed modules and everything downstream of them. **5/5 rc 0, 0 errors** in both forms. Each source
    is bound to `git show HEAD` (`build/summary-final.txt`: `RESULT modules=5 bad=0`).
  - The root `TCSlib` is not built.
- **C2 Admissions.** At the head: **37 declarations in 14 modules** = `base-sorries.txt` minus the 5 targets. The diff is
  exactly the PolyRatio and Asymptotic rows (`build/admissions-final-vs-base.txt`). The owned files contain 0 tokens of
  `sorry`, `admit`, `native_decide`, `axiom` or `opaque`.
- **C3 Statements.**
  - decls2 gives: `PolyRatio.lean` **ADDED 1** (`…GSW.Parameters.ofFamily_columns_le`), 0 CHANGED, 0 REMOVED;
    `Asymptotic.lean` 0/0/0 (`stmt/decls2-final-summary.txt`).
  - The StmtDumps of the five targets (full names, `pp.fullNames`) are **identical** at base and head
    (`stmt/StmtDump-diff-final.txt`). The helper's dump is `stmt/StmtDump-helper-head-final.log`.
  - §4 maps every target to its proof.
- **C4 Frozen check** (`tools/lead/frozen_owned.py`). This is the gsw-6b-u12 tool plus an allow kind `PUBLIC` for the
  brief's one helper: its block is removed at the head, and it must be absent at the base.
  - **PASS, 0 differences** in both files against `headers/allow.tsv`: the two module sentences, the *Main results*
    entry and the helper.
  - In each file the seven controls FAIL as stated: header 1, prose spill 1, definition body 1, reader 1, unpermitted
    import 1, deleted target 2, unlisted new public declaration 1.
  - The base passes against itself (`headers/frozen-base-vs-base.txt`). `git diff --stat` lists only the two owned files.
- **C5 Axioms** (`axioms/AxiomProbe-final.log`, check `axioms/axcheck-final.txt`). The census covers all 37 stored
  constants of the two modules.
  - **32 use only `propext`, `Classical.choice`, `Quot.sound`**, among them A1 and the helper (the helper uses
    `[propext, Quot.sound]`).
  - **5 reach `sorryAx`**, each only through allowed frozen targets of other units:

    | Constant | Reaches `sorryAx` through |
    |---|---|
    | G16 | `bootNoise_le` |
    | G17 pure | `bootNoise_le`, `decrypt_keygen_fheEvalCircuit` |
    | G17 leveled | `bootNoise_le`, `decrypt_keygen_leveledEvalCircuit` |
    | A3 | `distAdv_leveledView_le` |
    | the private glue | `bootNoise_le` |

  - No trace names a declaration of `PolyRatio.lean` or `Asymptotic.lean`. `RESULT bad=0`.
- **C6 Rule 10** (`evidence/rule10/`).
  - **Seals.** Whole-file seals strict-A, strict-B, coe-A and coe-B, `-DmaxErrors=0`, over the full import closure.
    Requests: PolyRatio 1,395 / 1,396 / 1,394 / 1,395; Asymptotic 1,654 / 1,655 / 1,653 / 1,654.
    - At the head (`final/`) and at the base (`base/`, sources `git archive` of B6): **all 16 probes rc 0, 0 errors,
      no failing declaration**, each with its install and verify records.
    - The request sets were built at the base from its oleans. The only change at the head is that PolyRatio adds
      theorems, and no definition, so the sets are equal.
  - **Liveness pairs** (`live-PolyRatio-final/`, `live-Asymptotic-final/`, sources `live-src/`), appended to each
    owner's own probe:

    | Pair | unsealed | strict-A, strict-B, coe-A, coe-B |
    |---|---|---|
    | PolyRatio: NEG `bootNoise` by `rfl` / POS `bootNoise_eq` | 0 / 0 errors | exactly 1 / 0 each |
    | Asymptotic: NEG `levelTerm` by `rfl` / POS `levelTerm_eq` | 0 / 0 | 1 / 0 each |
    | helper: NEG `ofFamily` columns by `rfl` / POS through `columns_eq`, `ofFamily_lwe`, `ofFamily_width` / POS `Parameters.ofFamily_columns_le` used sealed | 0 / 0 / 0 | 1 / 0 / 0 each |

  - **Explicit-unfold scan:** **0 foreign definitions** (`unfold-final/explicit-unfold-scan.txt`). Every identifier
    given to `rw`/`simp` is a theorem, and one is a local hypothesis (`hw`).
  - **Reader census:** MISSING 0.
- **C7 Lint.**
  - `style_lint` on the two owned files: **0 findings** at both base and head.
  - `campaign_style_lint TCSlib/Cryptography --check8b`: **92 FAIL / 103 WARN** at both base and head, matching the
    maintainer's B6 figures. The line sets are identical: 0 new, 0 gone (`lint/campaign-diff-final.txt`).
- **C8 Sizes:** §3 (`sizes/sizes-final.txt`). No line over 100 and no file over 1,000.
- **C9 Hygiene** (`docs/hygiene-final.txt`).
  - The new public helper and the private glue each have a formula and "Glue.".
  - G16 (28 lines), G17 leveled (31), A1 (45) and A3 (96) have sketches, with step comments at their major `have`s.
    G17 pure (18) also has one.
  - **flagged = 0**.
- **C10 Clashes** (`clash/clash-final.txt`). There are two new names: `Parameters.ofFamily_columns_le` (public) and
  `two_mul_width_lt_of_ratio` (private).
  - Each has 0 hits at the base, on `iO/phase-a-base` (`5ed465f6…`), on `cleanup/stage2-s2a` (origin
    `9f7f409c2e09749428db75b9ddd324f92695e4af`) and at the records tip `c63ee44f` (the scan's run). A re-check at the
    later tip `eddf183f` also gives 0 hits.
  - Neither short name exists elsewhere, so no unqualified use in a `UNIT-DOWN` module can change its resolution. The
    head sweep is clean.
- **C11 Reuse and overlap:** §6.
- **C12 Probe U18-P1** (`probes/U18-P1.log`, source `probe-sources/probes/U18P1.lean`).
  - `8 * 4 ^ 33 * 2 = 2 ^ 70` holds by `norm_num` and by kernel `decide`.
  - `#eval` of G16's two sides at three constant toy families gives `lhs ≤ rhs` = `true` each time:
    - `(n, m, q, ℓ, B) = (1, 8, 4, 2, 1)`: 1.8·10^19 ≤ 3.4·10^37;
    - `(2, 20, 16, 4, 3)`: 3.6·10^30 ≤ 1.2·10^49;
    - `(3, 40, 257, 9, 2)`: 8.6·10^39 ≤ 1.7·10^60.
  - Evidence only; no `native_decide`.
- **C13 Reproduction** (`evidence/reproduce-final.log`). In a scratch clone (sparse: the owned files) reset to the
  base, `git am` of `patches/` with `COMMITS.tsv`'s committer data reproduces both hashes, and `src/` equals the head's
  files byte for byte.
- **Unit checks.**
  - C2 count: 37 in 14.
  - C3: PolyRatio ADDED exactly the helper; Asymptotic 0/0/0.
  - C12: U18-P1 above.
  - Split: not used (one worker; §2).

## 6. Overlap and reuse

**Searches** (`evidence/overlap/searches.txt`, script `tools/dup_search.sh`). There were 16 `grep -rnE` searches over
TCSlib and `audits/` and over Mathlib, Batteries and core. Hit counts at the head:

| Search | Hits |
|---|---|
| `ofFamily_columns_le` | 7, all the new lemma and its uses |
| `\.columns ≤` | 11, SIS and `Eval.lean`, unrelated |
| `columns_le` | 12: the SIS family field `columns_le` (`SIS/Assumption.lean:80`), unrelated, and the new lemma |
| `dimensionBound.eval … + 1)` | 3 |
| `Nat.clog 2 … ≤` in TCSlib | 4, none `clog ≤ n` |
| `clog_le` in Mathlib | 1, `clog_le_iff_le_pow` only |
| `≤ bootNoise` and the like | 3: docstrings and my glue |
| `distAdv_nonneg`, `decisionAdvantage_nonneg`, `advantageAt_nonneg` | 0 |
| `negligible_polyExpr_mul` | 6, the three known copies |
| `two_extractionError_le` | 5 |
| `distAdv_encrypt_le_of_width` | 4 |
| `< ….modulus / 2` | 18, separation hypotheses only, no lemma |
| `singleBitSecure_of_dlweAssumption` and EF-R1's names | 0 |
| `negligible_collisions_of_SIS` | 3 |
| `two_mul_width_lt_of_ratio` | 6, mine |

**`exact?` probes** (`overlap/DupProbe.log`, source `probe-sources/dup/DupProbe.lean`, at the head): **8 probes, none
closed**:
- P1: the helper, for any `P` with the two reader equations;
- P2: `Nat.clog 2 n ≤ n`;
- P3: `β ≤ bootNoise P β`;
- P4: the decryption-condition glue;
- P5: `0 ≤ decisionAdvantage`;
- P6: `0 ≤ distAdv`;
- P7: polynomial × negligible + negligible;
- P8: a constant double sum over `Fin a × Fin b`.

**`dup-sweep.md` §U18-U19 must-reuse items:**

| Item | Where used |
|---|---|
| G12 `decrypt_keygen_fheEvalCircuit` | G17 pure |
| G13 `bootNoise_le` | G16 |
| L3 `decrypt_keygen_leveledEvalCircuit` | G17 leveled |
| L5 `distAdv_leveledView_le` | A3 |
| `Parameters.ofFamily_lwe` | helper, G16, glue, A1, A3 |
| `Parameters.ofFamily_width` | helper, G16 |
| `Parameters.columns_eq` | helper |
| `pBoot_eq` | G16 |
| `bootNoise_eq` | G17 leveled |
| instance `Parameters.neZero_columns` | G17 leveled (`Nat.pos_of_neZero`) |
| `PolyExpr.eval_const`, `eval_add`, `eval_mul`, `eval_pow` | G16; `const`/`add`/`mul` in A1, A3 |
| `PolyExpr.eval_var` | not needed: no `var` occurs in `pBoot` or the A3 polynomial |
| precedent `LWE.Family.encodeChallenge_length_le` (`LWE/Assumption.lean:102`) | its pattern (`dimension_le` + `Nat.mul_le_mul_right`) is the helper's proof; a different conclusion, not restated |
| `distAdv_encrypt_le_of_width` | A1 |
| `Regev.two_extractionError_le` | A3 |
| `reductionEfficient_iff` | A1 |
| `leveledReductionEfficient_iff` | A3 |
| `levelTerm_eq`, `challengeTerm_eq` | A3 |
| `LWE.dlweAssumption_iff` | A1, A3 |
| `LWE.Family.advantageAt_eq` | not needed: `advantageAt` is never opened. The dominations and the assumption are both stated in its terms |
| `EnsembleLemmas.negligible_polyExpr_mul` (`EnsemblesLemmas.lean:377`) | A1, A3 (twice) |
| `negligible_two_pow_neg` | A1, A3 |
| `Negligible.add` | A1, A3 |
| `Negligible.mono` | A1, A3 |
| `Negligible.const_mul` | A3 (A1 has no constant factor) |
| `Nat.clog_le_iff_le_pow`, `Nat.lt_two_pow_self` | G16 |
| `Nat.mul_le_mul`, `Nat.pow_le_pow_left` | G16, applied by `gcongr` (its tagged monotonicity lemmas), not re-derived |
| `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin` | A3 |

**The *Do not* list is respected:**
- `ofFamily`'s body is never read: seals, liveness and the unfold scan all confirm it;
- no helper has an efficiency hypothesis;
- no `distAdv_nonneg` is added (nonnegativity is `distAdv_def` with `abs_nonneg`, as §0.5 says);
- neither of the two other `negligible_polyExpr_mul`s is used.

**Near relatives and inline steps (disclosed):**
- **`m·B ≤ bootNoise P (m·B)`.** G17 leveled proves this inline: three lines on `bootNoise_eq`, as its frozen sketch
  prescribes.
  - The same fact is an inline step of G12's proof in U14-U16's delivery (`GSW/Bootstrap.lean` at their head
    `9852429e`, not at B6), and its sketch is at `Bootstrap.lean:320` at B6.
  - No public lemma exists (P3; search). This is a promotion request (§7).
- **`2·(N·ε_LHL) ≤ N·2^{−κ}`** (A3's `hNε`, two lines: `mul_left_comm`, `mul_le_mul_of_nonneg_left`) is the same step as
  the `have hN` inside phase 5's `distAdv_encrypt_le_of_width` (`GSW/Security.lean:299`). There it is not a stated
  lemma, and `distAdv_encrypt_le_of_width` does not apply to `levelTerm`/`challengeTerm`. A1 uses the phase-5 lemma
  itself.
- **`distAdv ≥ 0`** (A1, A3) and **`decisionAdvantage ≥ 0`** (A3, twice) are inline `distAdv_def`/`decisionAdvantage_eq`
  with `abs_nonneg`, per §0.5 (P5, P6: no lemma exists). This is a promotion request (§7).
- `Hashing/SIS/Asymptotic.lean:71` `negligible_collisions_of_SIS` has the same `Negligible` bookkeeping
  (`negligible_polyExpr_mul`, `.mono`). Nothing is copied.
- **EF-R2-R3's `singleBitSecure_of_dlweAssumption`** (Regev PKE, the same width condition) has **not landed**: 0 hits at
  the records tip `eddf183f`. It sits in the exchange delivery `inbox/fills/ef-r23-regev/`. Its analogy with A1 is the
  per-`κ` concrete bound from the width lemma, then `negligible_polyExpr_mul`. Nothing is reused.
- The private glue `two_mul_width_lt_of_ratio` has no library counterpart (P4). It is private, in one file, and used
  three times.

## 7. Promotion requests, scope requests, statement changes

- **Promotion requests** (optional; after U14-U16 and this unit land):
  - **(a)** A public `le_bootNoise : β ≤ bootNoise P β` in `GSW/Bootstrap.lean` (owner U14-U16), to replace the inline
    steps in G12 and G17 leveled.
  - **(b)** A public `distAdv_nonneg` in `Foundations/Experiments.lean` (and its corollary for `decisionAdvantage`),
    as `dup-sweep.md` §0.5 foresees.
- **Scope requests:** none.
- **Statement changes:** none.

## 8. Questions for Seyoon

- **U18-U19-W1 (the helper's form).**
  - (A, recommended) Accept the `Nat` form the brief states. A1/A3 cast it with `exact_mod_cast` after
    `PolyExpr.eval_*`, so the `PolyExpr` form would not shorten anything.
  - (B) Restate it in the `PolyExpr` form, `≤ ((F.dimensionBound.add (.const 1)).mul F.residueBits).eval κ`.
- **U18-U19-W2 (promotion requests §7).**
  - (A, recommended) Record (a) and (b) as promotion requests for after landing.
  - (B) Leave the inline steps as they are.

## 9. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS`. Their paths equal the delivered
files.

- `base/`: inputs check.
- `logs/`: preflight, base check, packages, cache store, cache get, cache check and probe, pool, order and roots.
- `build/`: bootstrap (logs and TSV), sorry census, source binding, the sweep per tag with its summary, and the
  admissions.
- `stmt/`: decls2 and the StmtDumps.
- `headers/`: allow list, targets, the frozen check with controls.
- `axioms/`: the probe log and the check.
- `rule10/`: seals at the head and the base, liveness runs with sources, unfold scan, reader census, and the probe
  sources of every seal.
- `lint/`, `sizes/`, `docs/`, `clash/`, `overlap/`, `probes/`.
- `git-diff-stat-*.txt`, `git-merge-tree-*.txt`, `reproduce-*.log`, `checks-*.log`. `checks-cp1-attempt1.log` is a first
  run that stopped after the seals on a `tail` syntax error in the runner; it was re-run whole.
- `tools/`: the runners, the gsw-6b-u12 tools as adapted here, and the records copy of `decls2.py`.
- `probe-sources/`: the Lean sources of every probe, the cache probe included.
