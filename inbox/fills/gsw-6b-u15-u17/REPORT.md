# gsw-6b-u15-u17 · final

**Head: `619d202992b026ab7464595884d9b1b77736d8ab`** (`fill/gsw-6b-u15-u17`, local only).
**Base:** B6 `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc982fd8f79aba755796bb13188922c4655d`.

**All three targets are proved:**
- G15 `distAdv_fheView_noEvk_le` (`GSW/Circular.lean`);
- L4 `distAdv_levelHybrid_le` and L5 `distAdv_leveledView_le` (`GSW/LeveledSecurity.lean`).

There is no `sorry` in either owned file. No statement changed, no hypothesis was added, no public declaration was added (seven private helpers), and no scope request is open. Every check C1–C13 and the unit checks were run at this head (§5), and C5's trace is empty.

Checkpoint 1 (head `56fe8e9a`: G15 and L4 proved, L5 outlined) was delivered as exchange commit `2e6cddf0f`. Since then the final adds one commit: L5 and its two helpers, as outlined there, and the module sentence. Checkpoint 1's evidence is kept beside the final's (`*-cp1*`).

## 1. Inputs, base, records tip, commits

- **Inputs** (`evidence/base/inputs-check.log`), read at the records pin `27e53754d28703907571cacbaf905b441e03c393`:
  - all 17 COMMON §1 files equal their SHA-256 values, so there is no E-INPUT;
  - the folder's `SHA256SUMS` gives 52/52 OK (`base/folder-sha256sums-check.log`);
  - `rulings.md` is present: Q-6BF-1 to Q-6BF-7 are all ruled A. Q-6BF-2 A puts U15 and U17 in this one unit, and Q-6BF-3 A allows no other public helper.
  - Between the pin and the records tip at delivery, the folder changed only in the three dispatch prompts, where the `<RECORDS>` placeholder was filled in. Nothing that binds this unit changed.
- **Base** (`evidence/logs/base-check.log`). `git rev-parse HEAD HEAD^{tree}` gives `bff0567b…` and `845bdc98…`, as expected.
  - The clone is separate: `git init`, then `git fetch --depth=1 file:///workspace/tcslib <B6>`, then the local branch `fill/gsw-6b-u15-u17`.
- **Records tip at delivery:** `eddf183f84fb7ead32236ff26dbf7281979b2f9e` (`cryptography/pass-shelat-ch2-4`).
  - `git merge-tree --write-tree 619d2029 eddf183f` is clean: rc 0, tree `ffbea202ac0366f38473d354bd241b2749a2018c` (`evidence/git-merge-tree-final.txt`).
  - At checkpoint 1 the tip was `f46a2ae4`, also clean.
  - I stayed on the base.

| # | Commit | File |
|---|---|---|
| 1 | `f4219a24c3bd37759e67f94948b4f46811808123` | `GSW/Circular.lean`: G15, its refreshed sketch |
| 2 | `56fe8e9ad5c414088ebed7bb2d77022f6eb97eb6` | `GSW/LeveledSecurity.lean`: L4, five private helpers, L4's refreshed sketch, the module sentence (checkpoint form) |
| 3 | `619d202992b026ab7464595884d9b1b77736d8ab` | `GSW/LeveledSecurity.lean`: L5, two private helpers, L5's refreshed sketch, the module sentence (final form) |

All three commits are unsigned (`git -c commit.gpgsign=false`), and each touches exactly one owned file.

## 2. Preflight, cache, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4. There is no cgroup memory limit, so the headroom is `MemAvailable` = 15.49 GiB (floor 4): pass.
  - **Disk: 17.48 GiB free (floor 12): pass.** To get there I first freed space from my own finished jobs on this host:
    - I made the exchange worktree `/workspace/exchange` sparse to the delivery path (`git sparse-checkout`; no file was removed from git);
    - I deleted my delivered gsw-6b-u12 clone `/workspace/gsw/repo` and its scratch clone `/workspace/gsw/amclone`. That job's head `afdaa9e2` is kept as a ref in `/workspace/tcslib`.
    - Nothing was copied, moved or deduplicated.
  - Before the cache step the re-check gave 13.92 GiB (floor 8): pass.
  - For C7 I later made a temporary full base worktree, used it to lint the base, and removed it. I kept only the two owned files' base text, under `/workspace/gsw2/basesrc`, for the base seals.
- **Packages.** `.lake/packages` is a symlink to this host's populated tree at exactly the manifest's pins (the addendum's alternative): 11 match, 0 mismatch, 4 absent (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`). Nothing in the order imports the absent ones (`evidence/logs/packages-check.log`).
- **Cache.**
  - The roots computed from `order.txt` are the 102 of `roots.txt`.
  - Before the fetch, the store held 2,402 files (120,571,432 B).
  - The narrowed `lake exe cache get` (102 roots) exited 0: "No files to download", 2,339 decompressed.
  - There are 0 empty oleans, and the cache probe compiles.
- **Pool** (`evidence/logs/pool.log`, `tools/pool.py`): **3** Lean processes, in dependency order, each module through `scripts/lean_check_tree.sh`.
  - 3 = `min(nproc 4, MemAvailable 15.5 GiB / 4 GB)`, which is also the local-host cap. It was never resized, and there was no shortage.
  - Bootstrap: peak RSS per module 2,948,484 KiB (`BonehBoyenMachine/Handler`), peak host memory in use 1.98 GB above idle. Head sweeps: 0.89 GB (checkpoint 1) and 0.87 GB (final).
- **Lean from the shell.** The repository's `AGENTS.md` and `.claude/CLAUDE.md` say not to run Lean from the shell and to use an editor infoview. COMMON §3 overrides that for this campaign: compile each module with `scripts/lean_check_tree.sh`. I followed COMMON. `lake build` was never run, and `lake exe cache get` ran only narrowed.
- **Who did what.** One worker. The brief allows one sub-agent (`circ`: `Circular.lean`, then the seals and controls of both owners). I used none, so the lead wrote both files and ran every check.

## 3. The owned files

| File | Base | Head | Fill | Max width |
|---|---|---|---|---|
| `GSW/Circular.lean` | 149 | 161 | +12 | 98 |
| `GSW/LeveledSecurity.lean` | 362 | 681 | +319 | 100 |
| **Total** | | | **+331** | |

The brief estimates 290–490 fill lines in total: U15 60–120, U17 230–370. U17 is inside its range, and `LeveledSecurity.lean` is under the projected 721 lines (G6B-F07). U15 is below its range: G15 needs 12 lines, because `acceptProb_fst` and phase 5's `distAdv_encrypt_le` carry it.

## 4. Per target

### G15 `distAdv_fheView_noEvk_le`

**Route.**
1. Regroup the seeds `(rg, R, R₀)` as `((rg, R₀), R)` with `e := (Equiv.refl _).prodCongr (Equiv.prodComm _ _) |>.trans (Equiv.prodAssoc _ _ _).symm`.
2. For each bit `μ`, the projected view at `r` equals `realView P χ μ (e r).1`: rewrite with `fheView_fst`, `fheView_snd`, `realView_eq`, `view_eq` and `Regev.keygen_fst`, then `rfl` (the `rfl` only reduces the `Equiv` application and the pair projections).
3. `acceptProb_comp_equiv e`, then **`acceptProb_fst`**, which drops the evaluation-key coins `R`. So both acceptance probabilities are those of `realView`.
4. `distAdv_def`, then phase 5's `distAdv_encrypt_le`.

No restatement over `realView` is added (G45-01).

**Sketch refreshed** (statement prose untouched):
- Old: "Through `fheView_fst`, `fheView_snd` (or `fheView_eq`), `Regev.keygen_fst` and `realView_eq`, `view_eq`, the projected view at a seed `(rg, R, R₀)` is `realView P χ μ (rg, R₀)`: it does not read the evaluation-key coins `R`. Through `acceptProb_def` and `acceptProb_comp_equiv`, regroup the seed-and-coin space so that the unused coins `R` form the second factor, `((KeySeed P χ × Coins P) × ρ) × (Fin N → Coins P)` (`Equiv.prodComm`, `Equiv.prodAssoc`); the marginalization lemma `uprob_fst` (`Foundations/Probability.lean`) then drops that factor, so each `acceptProb` equals that of `realView P χ μ`. Then `distAdv_def` and phase 5's `distAdv_encrypt_le`."
- New: "Regroup the seeds `(rg, R, R₀)` as `((rg, R₀), R)`, the bijection `Seeds P χ ≃ (KeySeed P χ × Coins P) × (Fin N → Coins P)` built from `Equiv.prodComm` and `Equiv.prodAssoc`. Through `fheView_fst`, `fheView_snd`, `Regev.keygen_fst`, `realView_eq` and `view_eq`, the projected view at `(rg, R, R₀)` is `realView P χ μ (rg, R₀)`, the first factor only: it does not read the evaluation-key coins `R`. So `acceptProb_comp_equiv` and `acceptProb_fst` (the unused factor dropped) make each `acceptProb` that of `realView P χ μ`. Then `distAdv_def` and phase 5's `distAdv_encrypt_le`."

### L4 `distAdv_levelHybrid_le`

**Route.**
1. **Position hybrids.** `G t := acceptProb (levelPosHybrid P χ L μ e t) D`, where the private glue `levelPosHybrid` is `H_{e+1}` with the first `t` ciphertexts of the level key `e` encrypting `0` (same coins).
   - `levelPosHybrid_zero`: `G_0` is `H_{e+1}`.
   - `levelPosHybrid_columns`: `G_N` is `H_e`. For `e' ≠ e`, the conditions `e + 1 ≤ e'` and `e ≤ e'` agree.
   - Then `abs_sub_le_sum_hybrids`, `Fin.sum_univ_eq_sum_range` and `Finset.sum_le_sum` over the position gaps.
2. **Real key** (`acceptProb_sample_levelReduction`). On `LWE.sample`, `levelReduction P χ L μ e j b D` accepts exactly as `D` accepts `G_j` (`b = true`) or `G_{j+1}` (`b = false`).
   - The proof is one explicit bijection `Ψ` of the reduction's seed-and-coin space `KeySeed × (Coins × ((Fin (N−1+1) → Coins) × (LeveledSeeds × ρ)))` onto `(LeveledSeeds × ρ) × (KeySeed × ((Fin N → Coins) × Coins))`.
   - `Ψ` plants the LWE seed as the key seed of `pk_{e+1}` (`Function.update … e.succ`), and the coins `R₀` at position `j` and the others elsewhere as the coins of the level key `e`. It keeps the three replaced coordinates as the second factor.
   - Then `uprob_comp_equiv Ψ` and `uprob_fst`, and a pointwise identity of the views through `levelReduction_eq`, `reduction_eq`, `view_eq`, `hybridPlant_eq`, `levelAssemble_eq`, `levelMsgs_eq`, `levelHybrid_eq`, `levelKey_eq`, `evalKey_eq` and `Regev.keygen_fst`, with the cases `i < j`, `i = j`, `j < i`.
   - The secret of `pk_{e+1}` is never read: in `H_{e+1}` the level key `e + 1` encrypts `0` (the top-down order).
3. **Uniform key** (`abs_acceptProb_id_levelReduction_sub_le`). On a uniform key, sides `true` and `false` differ by at most `2·(N·ε_LHL)`.
   - Regroup with `uprob_comp_equiv` and `uprob_prod`. Each side becomes the average over the reduction's own seeds `ω` of `acceptProb (uniformKeyView P m) (T ω)`, by `levelReduction_eq`, `reduction_eq` and `uniformKeyView_eq`. One test `T ω` serves both sides; the bit `m` is the key bit (`true`) or `0` (`false`).
   - For each `ω`, `uniformKey_uniform_advantage_le` twice and the triangle inequality through the uniform view give `2·(N·ε_LHL)`.
   - `abs_uexp_sub_le` (`Asymptotic/Sampling.lean:239`) averages, with `0 ≤ 2·(N·ε_LHL)` read off the same lemma.
4. **One position.** `|G_j − G_{j+1}|` is at most two exact DLWE advantages (`LWE.decisionAdvantage_eq`, `distAdv_def`) plus the uniform-key gap. This uses `abs_sub_le` twice and `linarith`, which gives `levelTerm P χ L μ e j D` (`levelTerm_eq`).

**Why not `real_uniformKey_advantage`, `distAdv_multi_le_sum` or `exists_fixSeed`.** The bit that `levelReduction` plants at position `j` (side `true`) and its other messages are bits of `s_e`, drawn from the reduction's own coins. So `levelReduction` is not `reduction P μ D'` for a fixed `μ` and `D'`.
- `real_uniformKey_advantage` (fixed `μ`) does not apply. The DLWE terms are read directly through `LWE.decisionAdvantage_eq`.
- Fixing the other seeds first (`exists_fixSeed`) or bounding per value of them would not give the stated bound: the DLWE terms of `levelTerm` are `|E_ω(real − uniform)|`, and a per-value bound only yields `E_ω|real − uniform|`, which can be larger.
- So, as the brief allows, I followed `distAdv_multi_le_sum`'s proof with those seeds in the coins, and averaged only the statistical gap.

**Sketch refreshed** (statement prose untouched):
- Old: "Position hybrids `G_i` (`i ≤ N`) between `H_{e+1}` (`G_0`) and `H_e` (`G_N`): the first `i` ciphertexts of the level key `e` encrypt `0`. `abs_sub_le_sum_hybrids` reduces to the gaps …, as in `distAdv_multi_le_sum` (…, so the multi-ciphertext lemma is applied per value of the other seeds or its proof is followed with them in the coins). The gap at `i = j` is the gap of `levelReduction P χ L μ e j b D` between a real LWE key and a uniform key, plus the gap between `b = true` and `b = false` under a uniform key: … and the seed regrouping (`acceptProb_comp_equiv`, `OneWay.uprob_update`). As in phase 5's `distAdv_encrypt_le`: the two DLWE gaps are the exact advantages (`real_uniformKey_advantage`, `LWE.decisionAdvantage_eq`), and the uniform-key gap is at most `2·(N·ε_LHL)` for each value of the reduction's own seeds (`uniformKey_uniform_advantage_le`, twice), averaged. Sum over `j` (`levelTerm_eq`)."
- New: the text in `src/…/LeveledSecurity.lean`, above L4. It describes the route above: the private `levelPosHybrid`; following `distAdv_multi_le_sum`'s proof (the lemma itself does not apply); the seed bijection (`uprob_comp_equiv`, `uprob_fst`); `LWE.decisionAdvantage_eq`; the uniform-key gap averaged by `uprob_prod` and `abs_uexp_sub_le`.

### L5 `distAdv_leveledView_le`

**Route** (the brief's, and checkpoint 1's outline, unchanged).
1. **`leveledView_eq_levelHybrid`** (private): `leveledView P χ L μ = levelHybrid P χ L μ L`, by `leveledView_eq` and `levelHybrid_eq`. No `e : Fin L` has `L ≤ e` (`not_le.mpr e.isLt`).
2. **The chains.** For each `μ`, `abs_sub_le_sum_hybrids` over `H_0(μ), …, H_L(μ)`, `Fin.sum_univ_eq_sum_range`, `Finset.sum_le_sum` and L4 at every level (through `abs_sub_comm` and `distAdv_def`) bound `|Pr[H_0(μ)] − Pr[H_L(μ)]|` by `∑ e, ∑ j, levelTerm P χ L μ e j D`.
3. **The middle step.** **`acceptProb_levelHybrid_zero_realView`** (private): `acceptProb (levelHybrid P χ L μ 0) D = acceptProb (realView P χ μ) (challengeDist P χ L D)`.
   - `challengeDist_eq` writes the distinguisher as `D` after a map reading its own seeds, and **`acceptProb_bind`** moves those seeds into the sampler.
   - A bijection `(KeySeed × Coins) × LeveledSeeds ≃ LeveledSeeds × (KeySeed × Coins)` plants `realView`'s key seed and challenge coins as those of `pk_0` (`Function.update … 0`) and of the challenge. Through `realView_eq`, `view_eq`, `levelHybrid_eq` and `Regev.keygen_fst`, the sampler is `H_0` of the first factor. In `H_0` every level key encrypts `0`, so no secret is read.
   - **`acceptProb_comp_equiv`** and **`acceptProb_fst`** drop the replaced coordinates.
   - Then `distAdv_encrypt_le P χ μ₀ μ₁ (challengeDist P χ L D)` and `challengeTerm_eq` bound `|Pr[H_0(μ₀)] − Pr[H_0(μ₁)]|` by `challengeTerm P χ L μ₀ μ₁ D`.
4. `distAdv_def`, `leveledView_eq_levelHybrid`, `Finset.sum_add_distrib`, `abs_sub_le` twice, `abs_sub_comm` and `linarith`.

**Sketch refreshed** (statement prose untouched):
- Old: "`leveledView P χ L μ = levelHybrid P χ L μ L` (`leveledView_eq`, `levelHybrid_eq`: no `e : Fin L` has `L ≤ e`). The chain `H_L(μ₀), …, H_0(μ₀), H_0(μ₁), …, H_L(μ₁)`: `abs_sub_le_sum_hybrids` (or the triangle inequality, `abs_sub_le`) on each side with L4 (`distAdv_levelHybrid_le`) for `e = L − 1, …, 0` (`Fin.sum_univ_eq_sum_range`). The middle step: `H_0(μ)` is `challengeDist P χ L D` run on phase 5's `realView P χ μ`, after the seed regrouping (`challengeDist_eq`, `realView_eq`, `view_eq`, `Regev.keygen_fst`, and `acceptProb_comp_equiv`; the seed of `pk_0` and the unused coordinates are integrated out), so phase 5's `distAdv_encrypt_le` bounds it by `challengeTerm P χ L μ₀ μ₁ D` (`challengeTerm_eq`). `linarith`."
- New: the text in `src/…/LeveledSecurity.lean`, above L5. It is the route above, naming the two private helpers and `acceptProb_bind`, `acceptProb_comp_equiv` and `acceptProb_fst`.

**Module docstring sentence** (the permitted edit): "Both are admitted statement-phase targets." became "Both are proved here." The P6-Q19 B reconstruction disclosure is unchanged.

### Helpers (seven, all private, in `LeveledSecurity.lean`)

| Helper | Statement | Used by |
|---|---|---|
| `levelPosHybrid` (def) | `levelPosHybrid P χ L μ e t r = (H.1, fun e' i => if e' = e ∧ i < t then encrypt P (pk e.succ) false (r.2.1 e i) else H.2.1 e' i, H.2.2)` with `H = levelHybrid P χ L μ (e + 1) r` | L4 |
| `levelPosHybrid_zero` | `levelPosHybrid P χ L μ e 0 = levelHybrid P χ L μ (e + 1)` | L4 |
| `levelPosHybrid_columns` | `levelPosHybrid P χ L μ e P.columns = levelHybrid P χ L μ e` | L4 |
| `acceptProb_sample_levelReduction` | `acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e j b D) = acceptProb (levelPosHybrid P χ L μ e (if b then j else j + 1)) D` | L4 |
| `abs_acceptProb_id_levelReduction_sub_le` | `\|acceptProb id (levelReduction … j true D) − acceptProb id (levelReduction … j false D)\| ≤ 2 * (P.columns * Regev.extractionError P.lwe)` | L4 |
| `leveledView_eq_levelHybrid` | `leveledView P χ L μ = levelHybrid P χ L μ L` | L5 |
| `acceptProb_levelHybrid_zero_realView` | `acceptProb (levelHybrid P χ L μ 0) D = acceptProb (realView P χ μ) (challengeDist P χ L D)` | L5 |

Each has a docstring with its formula. The three long ones have their own proof sketches. G15 needs no helper.

### Imports

None added. In particular `ColZKLemmas` (`exists_fixSeed`) is not imported: it is not needed (§4 L4).

## 5. Checks (runner `tools/lead/checks.sh final`, log `evidence/checks-final.log`; checkpoint 1's run: `checks-cp1.log`)

- **C1 Bootstrap and sweep.**
  - Bootstrap of `order.txt` at the base: **224/224 rc 0, 0 errors** in both forms (`build/bootstrap.tsv`, logs `build/bootstrap/`).
  - The sorry census equals `base-sorries.txt` name by name: **42 in 16** (`sorry-census-base.txt`).
  - All 224 sources equal `SOURCE-SHA256SUMS` (`source-binding-base.txt`: 0 mismatches).
  - Head sweep of the 6 `UNIT-DOWN` modules: Circular, LeveledSecurity, Asymptotic and the three facades. These are the changed modules and their downstream. **6/6 rc 0, 0 errors**, each source bound to `git show HEAD` (`build/summary-final.txt`: `RESULT modules=6 bad=0`).
  - The root `TCSlib` is not built.
- **C2 Admissions.** **39 declarations in 14 modules** = `base-sorries.txt` minus G15, L4 and L5, the brief's count. The diff is exactly the Circular and LeveledSecurity rows (`admissions-final-vs-base.txt`). Both owned files have 0 `sorry` tokens.
- **C3 Statements.** decls2 on both files gives **0 ADDED, 0 CHANGED, 0 REMOVED** (`stmt/decls2-final-summary.txt`). The StmtDump of the three targets (full names, `pp.funBinderTypes`) is identical at base and head, apart from the dropped `sorry` warnings (`stmt/StmtDump-diff-final.txt`).
- **C4 Frozen check** (`tools/lead/frozen_owned.py`). Both files **PASS, 0 differences**, against `headers/allow.tsv`, which licenses only the module sentence.
  - The seven controls each fail as stated, in each file: header 1, prose spill 1, definition body 1, reader 1, unpermitted import 1, deleted target 2, unlisted new public declaration 1.
  - The base compared with itself passes (`frozen-base-vs-base.txt`).
  - `git diff --stat` lists only the two owned files (`git-diff-stat-final.txt`).
- **C5 Axioms** (`axioms/AxiomProbe-final.log`). All **67** stored constants of the two modules (targets, the seven private helpers and every auxiliary) use only `propext`, `Classical.choice` and `Quot.sound`, or a subset.
  - **No `sorryAx`**: `SORRY-REACHING 0`, so the dependency trace is empty, as the brief requires.
- **C6 Rule 10** (`evidence/rule10/`).
  - Whole-file seals strict-A, strict-B, coe-A and coe-B, `-DmaxErrors=0`, over each owner's full import closure (requests: Circular 465/465/464/464, LeveledSecurity 1562/1563/1561/1562), at the head (`final/`) and at the base (`base/`). **All 16 probes rc 0, 0 errors, no failing declaration**, each with its install and verify records.
  - The request sets were rebuilt at the base from the base imports.
  - **Notation exemptions.** `PolyExpr.eval` is in `LeveledSecurity`'s closure (A ≠ B there) but not in `Circular`'s. The `FinDist` coercion is in both (strict ≠ coe).
  - **Liveness pair per owner** (`live-final/`, sources `live-src/`), appended to the owner's own probe:

    | Owner | Pair | unsealed | strict-A, strict-B, coe-A, coe-B |
    |---|---|---|---|
    | Circular | NEG `realView` by `rfl` / POS `realView_eq` | 0 / 0 | **1** / 0 each |
    | LeveledSecurity | NEG `levelKey` by `rfl` / POS `levelKey_eq` | 0 / 0 | **1** / 0 each |

  - There is no new public definition, so no further pair is needed.
  - Explicit-unfold scan: **0 foreign definitions** (`unfold-final/explicit-unfold-scan.txt`).
  - Reader census: **MISSING 0** (`rule10/reader-census.txt`, with `path:line` for each reader).
  - During development I also compiled L4 and L5 in a scratch file with the GSW, LWE and probability definitions locally irreducible. The seals above are the check of record.
- **C7 Lint.**
  - `style_lint` on both files: 0 findings at base and head.
  - `campaign_style_lint TCSlib/Cryptography --check8b`: **92 FAIL / 103 WARN over 540 files** at base and head, the maintainer's B6 figures. The line sets are identical: 0 new, 0 gone (`lint/campaign-diff-final.txt`).
- **C8 Sizes:** §3 (`sizes/sizes-final.txt`). No line over 100, no file over 1,000.
- **C9 Hygiene** (`docs/hygiene-final.txt`).
  - Every new private helper has a formula.
  - Every block of 20 lines or more has a sketch: G15 22 lines, L4 37, L5 39; the helpers `acceptProb_sample_levelReduction` (93), `abs_acceptProb_id_levelReduction_sub_le` (48) and `acceptProb_levelHybrid_zero_realView` (38).
  - The long proofs carry step comments. **flagged = 0**.
- **C10 Clashes** (`clash/clash-final.txt`). The seven new names, all private (§4), have 0 hits each:
  - at the base;
  - on `iO/phase-a-base` (`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`);
  - on `cleanup/stage2-s2a` (`9f7f409c2e09749428db75b9ddd324f92695e4af`);
  - at the records tip (`eddf183f`).

  No new short name exists elsewhere. Being private, none can change a resolution in a `UNIT-DOWN` module.
- **C11 Reuse and overlap:** §6.
- **C12 Probe U17-P1** (optional, run; `evidence/probes/U17-P1.log`, source `probe-sources/probes/U17P1.lean`).
  - Toy instance `n = 1`, `m = 1`, `q = 4`, `ℓ = 2` (`N = 4`), `L = 1`, two-seed noise.
  - `#eval` of decidable equality: `levelHybrid P χ 1 μ 1 r = leveledView P χ 1 μ r` is **true on all 16 seeds for both bits**.
  - As a control, `levelHybrid … 0 r` differs from `leveledView` on all 32.
  - Evidence only; no `native_decide`.
- **C13 Reproduction** (`evidence/reproduce-final.log`). In a scratch clone sparse to the two owned files, reset to the base, `git am` of `patches/` with `COMMITS.tsv`'s committer data reproduces all three hashes, and `src/` equals the head's files byte for byte.

## 6. Overlap and reuse

**Searches:** `evidence/overlap/searches-final.txt` (12 `rg` searches at the head, with hit counts; tool `tools/lead/searches.sh`; checkpoint 1's in `searches-cp1.txt`). Results:
- No lemma outside the file states a leveled hybrid. `levelReduction`, `challengeDist` and `leveledView` occur elsewhere only as consumers, in `GSW/Asymptotic.lean:239–335` (U18-U19's A3).
- No lemma averages a coin-dependent message under a uniform key.
- The averaging step is `abs_uexp_sub_le` (`Asymptotic/Sampling.lean:239`), used.

**`exact?` probes** (`evidence/overlap/DupProbe.log`, source `probe-sources/dup/DupProbe.lean`, `maxHeartbeats 4000000`):

| Probe | Statement | Result |
|---|---|---|
| P2 | `leveledView_eq_levelHybrid` | no lemma |
| P4 | the uniform-key helper's statement | no lemma |
| P6 | the averaging step | `abs_uexp_sub_le`, the lemma used |
| P1 | G15's inner identity | timed out in `isDefEq` (the candidates' unification unfolds the views); P1 also stops at a universe constraint |
| P3 | `acceptProb_levelHybrid_zero_realView`'s statement | timed out, as P1 |
| P5 | the real-key identity at `j = 0` against `H_{e+1}` | timed out, as P1 |

For P1, P3 and P5 the `rg` searches decide: no lemma mentions `fheView`'s projections, `levelHybrid … 0` or `levelReduction` except this file and its consumer `Asymptotic.lean`.

**`dup-sweep.md` §U15-U17 must-reuse items:**

| Item | Where used |
|---|---|
| `distAdv_encrypt_le` (`Security.lean:248`) | G15, L5 |
| `real_uniformKey_advantage` (`:156`) | not applicable: the planted bit depends on the reduction's coins (§4 L4). Its content is used through `LWE.decisionAdvantage_eq` |
| `uniformKey_uniform_advantage_le` (`:189`) | L4, uniform-key helper, twice |
| `reduction_eq` (`:122`) | L4, both helpers |
| `view_eq` (`:68`) | G15, L4, L5 |
| `realView_eq` (`:86`) | G15, L5 |
| `uniformKeyView_eq` (`:104`) | L4, uniform-key helper |
| simps readers of `view`/`realView`/`uniformKeyView` | not needed: the `_eq` readers rewrite whole applications |
| `distAdv_multi_le_sum` (`EnsembleSecurity.lean:146`) | not applicable (coin-dependent messages); its proof's structure is followed (§4 L4) |
| `hybridPlant` (`:110`), `hybridPlant_eq` (`:121`) | L4, through `levelReduction`; `hybridPlant_eq` in the real-key helper |
| `distAdv_tuple_le_sum` (`Hybrid.lean:88`) | not applicable, as `distAdv_multi_le_sum` |
| `abs_sub_le_sum_hybrids` (`Foundations/Probability.lean:218`) | L4, L5 |
| `exists_hybrid_gap` (`:230`) | not needed: the bound sums the gaps |
| `acceptProb_fst` | G15, L5 |
| `acceptProb_snd` | not needed: the dropped factor is always second |
| `acceptProb_bind` (`:91`) | L5 |
| `distAdv_comp` (`:141`) | not needed: no deterministic post-processing between two samplers |
| `acceptProb_coins_fst` (`EnsemblesLemmas.lean:92`) | not needed: no ignored coin factor |
| `acceptProb_comp_equiv` (`Experiments.lean:107`) | G15, L5 |
| `uprob_fst` (`:175`) | L4, real-key helper (used, not re-derived) |
| `uprob_prod` (`:153`) | L4, uniform-key helper |
| `uprob_comp_equiv` (`:165`) | L4, both helpers |
| `OneWay.uprob_update` (`OneWayFunctions/Basic.lean:131`) | not needed: the explicit bijection plants all three coordinates at once |
| `acceptProb_def`, `distAdv_def` | G15, L4 |
| `LWE.decisionAdvantage_eq` (`LWE/Experiments.lean:53`) | L4 |
| `Regev.keygen_fst` (`Regev/Basic.lean:53`) | G15, L4, L5 |
| own readers | `fheView_fst`/`_snd` (G15); `levelHybrid_eq`, `levelMsgs_eq`, `levelAssemble_eq`, `levelReduction_eq`, `levelTerm_eq` (L4); `leveledView_eq`, `challengeDist_eq`, `challengeTerm_eq` (L5). `fheView_eq` and `Seeds_eq` are not needed |

**Near relatives (not copied):**

| Relative | Relation |
|---|---|
| `Symmetric.lean:154` `distAdv_symEncrypt_le` with the private `exists_equiv_symEncrypt` (`:110`) | the same "transport a phase-5 bound along a seed equivalence" pattern on other seed types |
| `Regev/Experiments.lean:301` `distAdv_encrypt_le` | the Regev analogue of phase 5's bound |
| `Hybrid.lean:52` private `acceptProb_plant` | the planting step of `distAdv_tuple_le_sum`. It is private and plants one coordinate; `acceptProb_sample_levelReduction` plants three, under a seed type that also carries the key |

None of these is restated. The private helpers are specific to the leveled seed types; the brief notes that "the seed types differ, so the private glue of the two files is not a copy". G15 needs no glue at all.

## 7. Promotion requests, scope requests

- **Promotion requests:** none. The leveled-hybrid helpers are specific to `LeveledSecurity`'s seed types, and `abs_uexp_sub_le` already exists publicly.
- **Scope requests:** none.

## 8. Questions for Seyoon

- **U15-U17-W1 (L4's route; unchanged from checkpoint 1).** The brief and `dup-sweep.md` §U15-U17 suggest `real_uniformKey_advantage` and, as one option, `distAdv_multi_le_sum` per value of the other seeds (`exists_fixSeed`). Neither fits the frozen `levelTerm`, for two reasons:
  - the bit planted at position `j` is drawn from the reduction's own coins;
  - a per-seed bound would give `E|real − uniform|`, where `levelTerm` has the DLWE advantage `|E(real − uniform)|`.

  Options:
  - (A, recommended) Accept the delivered route: the brief's other option, following `distAdv_multi_le_sum`'s proof with the seeds in the coins. The DLWE terms are read through `LWE.decisionAdvantage_eq`, and only the statistical gap is averaged (`abs_uexp_sub_le`).
  - (B) As (A), and also amend the sweep's wording for later units: "`real_uniformKey_advantage` applies only to a fixed bit; with coin-dependent messages read `LWE.decisionAdvantage_eq` directly".

## 9. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS`. Their paths equal the delivered files.

- `base/`: inputs and folder checks.
- `logs/`: preflight, base check, packages, cache, pool, order and roots.
- `build/`: bootstrap with census and source binding; sweeps, summaries and admissions for `cp1` and `final`.
- `stmt/`: decls2 and StmtDump.
- `headers/`: the frozen checks, allow lists (`allow-cp1.tsv`, `allow.tsv`, `allow-empty.tsv`) and targets.
- `axioms/`.
- `rule10/`: seals at base, `cp1` and `final`; liveness pairs; unfold scans; reader census. Seal probe sources are in `rule10/probe-sources/`.
- `lint/`, `sizes/`, `docs/`, `clash/`, `overlap/`, `probes/`.
- `git-diff-stat-{cp1,final}.txt`, `git-merge-tree-{cp1,final}.txt`, `reproduce-{cp1,final}.log`, `checks-{cp1,final}.log`.
- `tools/`: the pool, census, StmtDump, check runner, seals and their loop, frozen check, unfold scan, lint diff, sizes and hygiene, searches, clash, delivery, the development check script `dev.sh`, and the records copy of `decls2.py`.
- `probe-sources/`: the AxiomProbe, StmtDump, unfold-scan, DupProbe and U17-P1 sources, and the cache probe.
