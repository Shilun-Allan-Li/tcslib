# Gate 51 · io-phfe checkpoint 0 · in-house Lean verification r1

**Verdict: PASS, with one disclosed deviation (a note).**
- **Source.** The 25 delivered patches reproduce **every one of the worker's 25 commit hashes**
  on the base, up to `70b85f9b`, and `src/` equals that tree byte for byte.
- **Build.** The 285-module closure and its downstream elaborate on the base: rc 0, 0 errors, and
  exactly the 144 expected `sorry` warnings.
- **Agreement with the worker.** All 85 rebuilt oleans that the worker also lists are
  **hash-identical** to the worker's build. The census matches the worker's self-report in
  every count, and only the three standard axioms appear, plus `sorryAx` on the obligations.
- **Deviation.** The new modules also carry **34 non-`sorry` linter warnings**: 33 unused
  variables and 1 automatically included section variable. REPORT does not disclose them. They
  are not errors and do not touch any statement.
- **Environment, not delivery.** The pinned Mathlib package build lacked two Mathlib modules
  that the delivery imports. They were compiled into the replay tree with the recipe's
  `mathlibextra.sh`.

Run on 2026-11-18, 22:19–22:35 UTC, after Gate 52's run on the same host. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work
directory is `$SP/io-c0/`.
- **Evidence:** `verification-r1.zip`, beside this file. Its SHA-256 is in
  `verification-SHA256SUMS`, and it holds an inner `SHA256SUMS`.
- **Constraints observed:**
  - no `lake build`, no cache get;
  - one Lean process of this job at a time;
  - Lean ran only through the recipe tools (`runner.py`, `runner_full.py`, `mathlibextra.sh`),
    on `cp -al` copies;
  - nothing was written into `$SP/olean-snapshot`, `$SP/olean-snapshot-10` or any existing
    `$SP/olean-replay-*` tree;
  - nothing was committed, pushed or branched in the repository. The scratch git work used a
    private bare repository, `$SP/io-c0/git.git`, with the records objects as alternates.
- **Host slots.** There were 0 other `lean` processes at every build start. At the probe start
  (22:32:58Z) there was **one foreign `lean`**, another job's
  `G6bProbe/Ctl/Sealed_DecryptFormula.lean`. The total was 2 of 3. It was not touched.

## Expectations against results

| # | Check | Expected | Result |
|---|---|---|---|
| 1a | Delivered patches | intact | 26 files (25 patches + `COMMITS.tsv`) verify against the delivery's `SHA256SUMS`. `REPORT.md` = `d1208741…6577` as listed. There is no bundle in this delivery |
| 1b | base + patches | source HEAD `70b85f9b` | `tools/replay_patches.sh`: per patch, `git mailinfo`, `git apply --cached` on a private index, `write-tree`, then `commit-tree` with committer = author and committer date = author date. It reproduces **all 25 commit hashes of `COMMITS.tsv` exactly**, ending at **`70b85f9ba83f27393d98fa5bf88505aea3d22a8d`**, tree `9f63507ee63074c913fa61f1be57bd1a96a5ad1d` |
| 1c | `src/` vs tree | byte for byte | **76/76** `src/` blobs equal the blobs at `70b85f9b`; path sets equal |
| 1d | Changed paths | 74 new modules + facade edits to `Pairing.lean`, `AdvancedEncryption.lean` | **74 A + 2 M** (`TCSlib/Cryptography/Pairing.lean`, `TCSlib/Cryptography/AdvancedEncryption.lean`), nothing else |
| 1e | Static census | 144 `sorry`, 13,745 lines | **144** `sorry` tokens (144 outside comments), **13,745** lines. The gate's `source-head.json` `src_files`: **76/76** SHA-256 match the export and the runner's records |
| 2a | Closure | 285 = delivered `evidence/logs/order.txt` | `downorder.py` `order-noroot`: **285**, byte-identical to the delivered `order.txt` |
| 2b | Build | every module rc 0, 0 errors | **95/95 rc 0** in the final records; `error:` 0, `error(` 0, substring "error" 0. Attempt 1 stopped on a missing Mathlib olean (§2) |
| 2c | `sorry` warnings | 144 (direct) | **144**, all in the 74 new modules, **per file equal** to the static counts |
| 2c' | Other warnings in new modules | none (sorry only) | **34 linter warnings** (deviation; §2) |
| 2d | State check | RESULT OK | `stateplan update` 95/95 taken; `check` **1532/1532 OK** (full order: root and both `Checks`) and **285/285 OK** (closure) |
| 2e | Link counts | rebuilt oleans have 1 link | **95/95 link count 1**; exactly 95 non-Mathlib files with link count 1. Tree: 1577 files (1501 + 74 + the 2 Mathlib extras) and 3346 symlinks |
| 2f | Agreement with the worker's build | — | The worker's `evidence/build/summary.tsv` lists 285 rows. For the **85 rows rebuilt here**, source and **olean SHA-256 are all equal** (74/74 new modules, 11/11 others) |
| 2g | Source trees | rehash 0/0/0 | Snapshot #11 **0/0/0** at the end. The EF-D1 tree rehashes **0/0/0** and its state check gives 1469/1469 OK, after this build and at the end |
| 3 | Axioms | only the three standard axioms, plus `sorryAx` on obligations | **0 non-standard** over all 2225 stored constants. Headlines: 20 via `sorryAx`; `Correct.correctExcept_zero` standard-only. The control is flagged |
| 3' | Worker self-report | 2225 constants; 1933 standard-only; 292 `sorryAx`-dependent; 144 direct; 0 other | **2225; 1933; 292; 144; 0**, all equal |
| 4 | Headline `#check`s | elaborate | `Heads`: rc 0, 0 errors; the only warning is the control's `sorry` |
| 5 | Duplication probes | intake F07/F08, dup-sweep §3 | S3 (`foldr pairEncode []`) **is** `encodeList`. S2: both GT laws are one-line copies of the base proofs. No §3 statement is closed by an existing lemma. `Layered.forward_root` closes by `exact rfl` |

## 1. Source reconstruction

- **Inputs.** The delivery commit is `1e77173a7032b57aa22260787711c6c7a1b7596e` at
  `inbox/fills/io-phfe/`, on base `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`.
- **The rebuilt commits** exist only in the scratch bare repository and are on no ref. Because
  all 25 hashes match, every commit message, author and date in the series is bound too.
  `replay-am.txt` lists commit and tree per patch.

## 2. Replay (snapshots.md job recipe, on the EF-D1 kept tree)

**Start tree.** It is the same as Gate 52's: `$SP/olean-replay-efd1`.
- Before use: state check 1469/1469 OK and rehash baseline `efa200d3…`.
- Gate 52's evidence holds both. Both were re-checked after this build and at the end.

**Copy.**
- `cp -al $SP/olean-replay-efd1 $SP/olean-replay-ioc0-phfe`: 1501 files and 3346 symlinks, 0
  with link count 1.
- Free disk before the copy was 2,927 MB. Gate 52's tree, 8.1 MB of its own, was kept (see the
  end).

**Export.** `git archive` of `70b85f9b` (same paths as Gate 52), 1684 files, with
`.lake/packages` symlinked.

**Plan.**
- `downorder.py`: 76 changed, 77 down, order 1530, `order-noroot` 285.
- `fullorder.py`: 1532.
- `stateplan plan` against EF-D1's state: **95 to build, 1437 reused.** The 95 are:
  - the 74 new modules;
  - the `Pairing` and `AdvancedEncryption` facades;
  - root `TCSlib`;
  - 18 base-delta modules whose key at `5ed465f6` differs from the merge tree: `LWE/BitEncoding`,
    `LWE`, `SIS`, 9 Regev/`Encryption` modules, 5 `GSW` modules and `Homomorphic`.
- Of the 285 closure modules, **85 were built and 200 reused** under identical closure keys.

**Build, attempt 1** (22:19:34–22:19:54).
- 12 modules rc 0, then `Pairing/Exponents` failed with rc 1:
  `object file …/Mathlib/LinearAlgebra/Matrix/Hadamard.olean … does not exist`.
- **Cause.** The shared pinned Mathlib build (`029db123`) has no oleans for
  `Mathlib.LinearAlgebra.Matrix.Hadamard` and `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card`.
  The delivery imports both, and the base closure imports neither.
- `tools/mlmissing.py` confirmed that these two are the only Mathlib roots of the closure
  missing from the package build. Every import of theirs is present. Gate 52's closure misses
  none.

**Mathlib extras.** The recipe's `mathlibextra.sh` was run once per module, into
`$SP/olean-replay-ioc0-phfe` only. It uses the pinned sources, `lean -o`, and no lake or cache.

| Module | Source SHA-256 | rc | Olean SHA-256 |
|---|---|---|---|
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card` | `93147a66…84c8e` | 0 | `6426942334cf178f3e7a6949c9e94e41fd3281532a00a3136f208adf465429e9` |
| `Mathlib/LinearAlgebra/Matrix/Hadamard` | `810850fd…2d824d` | 0 | `a2800eb7113c5eca749f601d668c59c99b9a81ea50556fb0519a40e69b785a12` |

**Resume** (`runner.py … Pairing/Exponents`), 22:20:50–22:23:47.
- All remaining modules rc 0. Peak maxrss 4.59 GB, for root `TCSlib`.
- The 21 base modules give 0 `sorry` and 3 pre-existing base warnings: `Regev/Basic` 1 and
  `Regev/Experiments` 2. These are the same as in Gate 52's run.

**Deviation: 34 linter warnings in the new modules.** They are warnings, not errors (rc 0, and
the checker's `error:` test is clean).

| File (under `AdvancedEncryption/FunctionalEncryption/`) | Warnings |
|---|---|
| `Wee20/PHFE/Simulator.lean` | 14 unused variables (`κ` ×6, `pp` ×6, `f` ×2) |
| `Wee20/PHFE/Raw.lean` | 14 unused variables (`κ` ×6, `pp` ×6, `f` ×2) |
| `Wee20/Targets/MatrixDH.lean` | 1 unused variable `f` |
| `SemiAdaptive/Games.lean` | 1 unused variable `S` |
| `SemiAdaptive/Data.lean` | 1 unused variable `S` |
| `PartialGarbling/Layered.lean` | 1 unused variable `C` |
| `Classes.lean` | 1 unused variable `i` |
| `PartialGarbling/Defs.lean` | 1 automatically included section variable unused in a theorem |

- REPORT's checks table (style, sketch and width) and its four campaign-lint warning lines do
  not mention them.
- Grade suggestion: **note**. Clean them at the next checkpoint. Either use `_`-prefixed binders,
  or drop the unused binders where the statement allows.

## 3. Axioms

Every probe ran through `runner_full.py`, with no `-o`.

**`Heads.lean`** (rc 0). It holds 21 `#print axioms` and a `sorry` control.
- `FEScheme.Raw.Correct.correctExcept_zero` is `[propext, Classical.choice, Quot.sound]`.
- 20 are `[propext, sorryAx, Classical.choice, Quot.sound]`:
  - `expect_simGame_eq_saGame`, `simAdv_eq_saSimAdv`, `pad_one`;
  - `wee20PHFE_raw_correct`, `_raw_correctExcept_zero`;
  - the four `…Adv_le`/`…_dlin_le`;
  - the four `wee20PHFE_raw_*SecureWith`;
  - `wee20PHFE_correct`, `_correctExcept_zero`, `_simSecure`, `_saSimSecure`,
    `_subexpSimSecure`, `_subexpSASimSecure`, `_gjls21`.
- The control is `[sorryAx]`.

**`Census2.lean`** (memoized collector, validated byte-identical to core `collectAxioms` on Gate
52's 1036 constants): every constant whose module is one of the 74.

| Population | Constants | Standard-only | Via `sorryAx` | Other axiom |
|---|---:|---:|---:|---:|
| All stored constants | **2225** | **1933** | **292** | **0** |
| Public (non-private, non-internal, non-auxiliary) | 1736 | 1481 | 255 | 0 |
| — with a source declaration range | 1475 | 1220 | 255 | 0 |
| — public theorems | 902 | 677 | 225 | 0 |
| — public definitions, structures, constructors | 834 | 804 | 30 | 0 |

- **Direct holes.** 144 constants mention `sorryAx` in their own value. All 144 are public
  theorems.
- **Transitive-only dependents.** There are 148: 97 thm, 39 def, and 4 induct, 4 ctor and 4 rec.
  - The 39 definitions are raw bundles and simulators with stored admitted fields:
    `wee20PHFE_raw`, `wee20PHFE`, `wee20Sim_raw`, `wee20SASim_raw`, `layeredPG_raw`, …,
    `PHFE.replay`, `toQuadratic`, and the `PHFE.*Equiv` codecs.
  - The four inductives are the target structures `Wee20.Targets`, `SchemeTargets`,
    `SimTargets` and `PGTargets`. Their field types mention those bundles.
  - This is the M0-expected propagation (intake F14 analogue). No admission sits in a
    definition body: all 144 direct holes are theorems.
- **Against the worker.** REPORT's "2225 stored constants … 1933 standard-axiom-only; 292
  transitively depend on sorryAx, with no other nonstandard axiom … 144 direct admissions" is
  **reproduced exactly**.

## 4. Headline `#check`s (`Heads.lean`, rc 0, 0 errors)

All of the following elaborate as stated; the full statements are in `logs/probes/Heads.log`.
- **Def 4.1:** `FEScheme.Raw`, `FEScheme`, `Simulator.Raw`, `Simulator`, `SASimulator.Raw`,
  `SASimulator`.
- **Def 4.2:** `#print Correct`, `CorrectExcept`, and `Correct.correctExcept_zero`.
- **Def 4.3:**
  - `simGame`, `simAdv`;
  - `#print SimSecureWith`: ∀ A : TwoStage, ∀ q, `Negligible (S.simAdv Sim A q)`;
  - `SimSecure`: ∃ Sim : Simulator S, `SimSecureWith Sim.toRaw`;
  - `SubexpSimSecureWith`: ∃ c > 0, ∀ A q, `SubexpSmall c …`;
  - `SubexpSimSecure`, `SASimSecureWith`, `SASimSecure`, `saGame`.
- **The derivation:** `TwoStage.toSA : TwoStage → PolyExpr → S.SAAdv`,
  `SASimulator.Raw.toSim`, and
  - `expect_simGame_eq_saGame`:
    `(S.simGame Sim.toSim A q real κ).expect test = (S.saGame Sim (A.toSA q) real κ).expect test`;
  - `simAdv_eq_saSimAdv`: `S.simAdv Sim.toSim A q κ = S.saSimAdv Sim (A.toSA q) κ`.
- **Def 4.6:** `#print Wee20.LinearEfficient`: ∃ M q, ∀ ℓ n d κ pp pk x y draw, …. **§9:**
  `phfeClass`, `pad_one`.
- **Correctness:**
  - `wee20PHFE_raw_correct G ℓ n d PG : PHFE.PGSound PG → (wee20PHFE_raw G ℓ n d PG).Correct`;
  - `wee20PHFE_raw_correctExcept_zero`.
- **Security:**
  - raw: `wee20PHFE_saSimAdv_le`, `wee20PHFE_simAdv_le`, the `_dlin_le` forms and the four
    `wee20PHFE_raw_*SecureWith`;
  - efficient: `wee20PHFE_correct`, `_correctExcept_zero`, `_simSecure`, `_saSimSecure`,
    `_subexpSimSecure`, `_subexpSASimSecure`;
  - `wee20PHFE_gjls21`. Under `hT : Targets G ℓ n d`, `p` with `hp`, `∀ κ, 2^κ ≤ p κ`,
    `Wee20Realizable43 … (layeredPG_raw ℓ (n.mul n) d) p hp` and `G.DLINAssumption`, it gives
    `CorrectExcept 0 ∧ SimSecure ∧ LinearEfficient G`.

## 5. Duplication probes

**`Dup.lean`** (rc 1: its one error is the `exact?` in the S3 row "named lemma?", which failed, as
recorded; every other line passed).

| Item | Probe | Result |
|---|---|---|
| S3 / F08 | `(fun l => l.foldr pairEncode []) = PrivateKeyScheme.encodeList` by `funext; induction` (`simp only [List.foldr_cons, encodeList, ih]`) | **passes**: the 21 inline folds are `encodeList` (statically recounted: `Simulation/Games` 4, `Defs/Simulator` 2, `Wee20/WireDraws` 14, `Wee20/PHFE/Simulator` 1) |
| S3 / F08 | `[a, b].foldr pairEncode [] = encodeList [a, b] := rfl`, and the same for four entries | **pass by `rfl`**: on the literal lists the delivery spells out, the replacement is definitional |
| S3 / F08 | `exact?` for `l.foldr pairEncode [] = encodeList l` | **could not close**: no bridge lemma exists, so reuse would want one reader `foldr_pairEncode_eq_encodeList` (or the statements switched to `encodeList`) |
| S2 / F07 | `gT ^ (a + b).val = gT ^ a.val * gT ^ b.val` for `B.GT`, by `rw [ZMod.val_add, ← pow_add, ← pow_mod_card gT _, B.card_GT]` | **passes**: the base `pow_val_add` proof with `card_GT` for `card_G` |
| S2 / F07 | `gT ^ (-a).val = (gT ^ a.val)⁻¹` for `B.GT`, by the base `pow_val_neg` pattern | **passes** |
| S2 / F07 | `#check` of base `pow_val_add`, `pow_val_neg` (`x : B.G`) and `pow_val_mul_GT` | they confirm that the base has the GT version only for `mul`. The two `_GT` lemmas are near-copies, with no base lemma to apply |

**Prefix probes** (dup-sweep §3): each is the delivered module cut just before the lemma, with
its signature closed by `exact?`.

| Lemma | `exact?` |
|---|---|
| `pow_val_add_GT`, `pow_val_neg_GT` | could not close (no restatement of an existing lemma) |
| `expVec_add`, `expVec_neg` | could not close |
| `Linear.dlinMatrix_mulVec` | could not close |
| `Classes.phfeEval_sum` | could not close |
| `Layered.auxCount_add_one`, `Layered.nodeBound_eval` | could not close |
| `Layered.forward_root` | **`exact rfl`**: the obligation holds definitionally. It is not a duplicate, but a `sorry` that `rfl` closes now |

No dup-sweep §3 statement is a restatement of an existing lemma.

## 6. State after the run

- **Kept:**
  - `$SP/olean-replay-ioc0-phfe`: the accepted tree, 1577 files (95 own plus the 2 Mathlib
    extras, 25.4 MB) and 3346 symlinks; `stateplan check` 1532/1532 OK at the end;
  - `$SP/olean-replay-ioc0-sprg`: Gate 52's tree, 8.1 MB of its own; check 1480/1480 OK at the
    end.
  - Both are hard-link copies, so deleting either frees only its own files.
- **Disk.** Free space was 3,023 MB at the start and 2,819 MB at the end (−204 MB in all: the
  two trees, about 34 MB, plus exports, logs and filesystem metadata). It never fell below
  2,800 MB.
- **Work directory.** `$SP/io-c0/` holds the exports, plans, logs, probes and the scratch
  repository `git.git`.
- **Not touched:**
  - `$SP/olean-snapshot` (rehash 0/0/0 at the start and the end);
  - `$SP/olean-replay-efd1` (0/0/0, and state check OK, at the end);
  - `$SP/olean-snapshot-10`;
  - other agents' trees and processes.
