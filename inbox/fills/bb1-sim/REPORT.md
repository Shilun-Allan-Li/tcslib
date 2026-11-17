# Fill `bb1-sim` — final (Claude lead)

**Result.** T2 `bb1_sim_real`, T3 `bb1_sim_random`, `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel` are proved, and the ten approved readers are inserted verbatim. With T4 (#346) in, **`bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1) uses only `propext`, `Classical.choice` and `Quot.sound`**: its `sorry` trace is empty.

Every new or changed file is free of `sorry`. Admissions at the check head are exactly the base's 22 minus the four targets, so 18 in 8 modules.

No statement changed, no frozen file was touched beyond the readers, and there are no scope requests.

## Bases

| | commit | tree |
|---|---|---|
| issue base (#346 head) | `89a18a8225be1b76166af12a15179da291747783` | |
| records tip at issue | `ca129d64cd54a92aabe517e5262058664b49f651` | |
| **patch base** | `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c` | `b5a5842dd0a5af86975864b29065bec44758f561` |
| **check base** (+ #340 head `916afc25…`) | `7cfe2b1b9a7e001d9ae972811cf85a332518111d` | `02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d` |

`tools/mkbase.sh` printed exactly the two pinned lines (`evidence/logs/mkbase.log`):
```
PATCH_BASE 72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c tree b5a5842dd0a5af86975864b29065bec44758f561
CHECK_BASE 7cfe2b1b9a7e001d9ae972811cf85a332518111d tree 02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d
```

**Rebase (Q9): none.**
- At the final, the records branch is at `54b18e4a6b9605862d5d8353e3351415a0c85b57`.
- #346 (`89a18a82…`) and #340 (`916afc25…`) are both **not merged**.
- The Lean diff `ca129d64…54b18e4a` (`*.lean`, toolchain, manifest, lakefile) is empty (`evidence/logs/records-tip-final.txt`).
- So, as the brief says, the fill stays on its bases.

**Branches** (local, unsigned; `COMMITS.tsv` signing column `none`):
- `fill/bb1-sim` head **`c35595aef7636c2ba9a25e1ffdac141b08d2fea5`**;
- check branch `check/bb1-sim-merged` head `408c8195c36007195b0f96a991814b98b5a53aab` = the four fill commits cherry-picked onto the check base.
- **Tree equality:** `git merge-tree --write-tree 916afc25… c35595ae…` = `bdae2f85606a1b930a2eaab1bec13a3b4b2cf56e`, the check head's tree. Every build and check ran at the check head.

**Commits** (`patches/`; `git am` at the patch base reproduces every hash, checked in a scratch clone, `evidence/delivery/am-check.out`):

| # | commit | content |
|---|---|---|
| 1 | `23614c0a` | the ten approved readers in `Defs` and `BonehBoyen` (Q7 follow-up) |
| 2 | `3f430cae` | `expect_simulate_rel` and `expect_sample_rel` |
| 3 | `622f5b03` | the five helper modules |
| 4 | `c35595ae` | T2 and T3: bodies, refreshed sketches, the helper imports, a `## Contents` section |

The checkpoint-1 commits 3 and 4 (`bcb9bcca`, `35c780c4`) were work in progress and are replaced. Commits 1 and 2 are unchanged since checkpoint 1.

## Environment and pool

- **Preflight** (`evidence/logs/preflight.log`):
  - 4 CPUs.
  - Memory: no effective cgroup limit; `MemAvailable` 15.19 GiB.
  - Disk: 14.09 GiB free on the clone's ext4 filesystem. Before the preflight I deleted this host's own finished statement-job worktrees and olean trees. Nothing was copied, moved or deduplicated.
- **Cache:**
  - The store already held 2,420 archives (121 MB) from this host's earlier jobs (`cache-store.log`).
  - The narrowed `lake exe cache get` used the 94 roots (equal to the pack's `roots.txt`). It downloaded nothing, decompressed 2,339 files and exited 0 (`cache-get.log`).
  - `PACKAGES-CHECK PASS`; 0 empty oleans.
- **Bootstrap** (`evidence/build/bootstrap/`): 193/193 rc 0, 0 errors in both forms, sources bound 193/193; exactly the 22 base `sorry` warnings in 10 modules; peak 2.9 GiB.
- **Lean parallelism.**
  - Until the user's message relaying Seyoon's ruling (`workflow.md` §4.1 on `main`, PR #353; quoted in `evidence/logs/parallelism-ruling.txt`), every Lean process ran through the host's one-Lean lock. That covers the bootstrap, every development check, both sweeps and the sub-agent's checks.
  - The final sweep was already running when the ruling arrived and was not interrupted.
  - From the next phase on (seals, controls, scans, axioms, StmtDump, shadow probe), Lean ran through `evidence/tools/seal/poolrun.py`:
    - pool **3** = min(nproc 4, `MemAvailable` ≈ 15 GiB / 4 GiB);
    - a host-wide counting semaphore (slot locks) shared by three concurrent jobs: the head series, the base series and the probes;
    - a 4 GiB `MemAvailable` floor before each start.
  - 197 probes ran through the pool (`evidence/logs/pool-memory.txt`). The lowest `MemAvailable` seen was **13.89 GiB** of 15.71 GiB, and the peak RSS of one probe was **2.93 GiB**.
- **Interruptions, recorded:**
  - A worker restart killed a first final run after 3 of 100 head seal probes (`evidence/rule10/driver-before-restart.out`).
  - I stopped a second run myself to add four missing proof sketches (docstrings only, found by `sk15`). That changed the head, so every Lean check of the final was rerun at the final head.

## Who did what

- **Lead:**
  - the readers, `Relational`, `Lazy`, `Real`, `Random`, `Chain`, T2/T3 and `BonehBoyenSecurity.lean`;
  - every commit, the integration and every check.
- **Sub-agent A (`stepM`)** wrote `Coupling.lean` (step M):
  - the group-algebra lemmas, the nine call-by-call rows `stepM_*`, `stepM_call`;
  - in its own worktree and olean tree (seeded from the lead's tree for 198 modules with byte-identical sources: `evidence/subagents/stepM/seed-treeA.txt`), sharing the lock.
  - It ran no `lake` and committed nothing.
  - Its log, searches and final native and dev-seal A/B logs are in `evidence/subagents/stepM/`.
  - The lead integrated the file unchanged, except for three proof sketches added to its docstrings, and checked it against the lead's tree: native and dev seals A and B rc 0.
- No second sub-agent was used.

## Changed files (lines at the patch base → head)

| file | base | head |
|---|---|---|
| `Games/Relational.lean` | 134 | 146 |
| `IdentityBased/Defs.lean` | 476 | 563 (`97ecb6e0…`) |
| `IdentityBased/BonehBoyen.lean` | 714 | 760 (`88454d6f…`) |
| `IdentityBased/BonehBoyenSecurity.lean` | 170 | 225 |
| `BonehBoyenSecurity/Lazy.lean` (new) | — | 438 |
| `BonehBoyenSecurity/Real.lean` (new) | — | 406 |
| `BonehBoyenSecurity/Coupling.lean` (new) | — | 565 |
| `BonehBoyenSecurity/Random.lean` (new) | — | 139 |
| `BonehBoyenSecurity/Chain.lean` (new) | — | 130 |

`git diff --stat <patch base>` lists exactly these nine files (`evidence/frozen/diff-stat.txt`). Of the frozen files, only `Defs` and `BonehBoyen` change, by the reader insertions.

## The proof

T2 and T3 follow design r1 §3 and the checkpoint outline. Notation:
- `S := bb1Scheme G ℓ`, `c(ρ) := A.toComp (S.sidCodec κ) κ q ρ`;
- for generator coins `r`: `d := desc(κ, r)`, `p := |G|`.

**T2** (body in `BonehBoyenSecurity.lean`):
1. `BB1Sim.setup_out` reads `Setup` as `r, g, α, h, g_2 ↦ o r g α h g_2`, with `RealReads`.
2. Both acceptances are averages over `r` (`prob_bind`).
3. `ProbComp.abs_expect_sub_le_expect` with the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]`:
   - bad coins: two probabilities;
   - good coins: equal, by `BB1Sim.prob_sidGame_coins`.
4. `prob_eq_expect` and `Bridge.prob_sample_eq_uprob` turn the bound into `uprob`.

**`BB1Sim.prob_sidGame_coins`** (`Chain`), the chain for good coins:
1. Move `h` past `g_2` and `ρ` (`expect_sample_comm`).
2. **R1 + E-h** (`expect_sample_sidImpl`):
   - **R1** is `expect_simulate_rel` from `S.sidImpl b κ (o h).1 (o h).2` to `bb1RealAt o h`, with `R s u :↔ s = (u.1.map fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`;
   - **E-h** is `Games.expect_simulate_eager` with `O := bb1RealLazy o`, `OE h := bb1RealAt o h`, `used u := u.1.isSome`.
3. `g_2 = g^{b'}` (`expect_sample_equiv` along `Equiv.ofBijective _ (pow_val_bijective_of_ne_one _ g.2)`).
4. **Step M** (`expect_simulate_bb1RealLazy`): `expect_simulate_rel` with `RelM`, from `bb1RealLazy` to `bb1SimLazy … (fun c => (g^c, e(g,g)^{α b' c}))`. The per-call hypothesis is `stepM_call`, by the rows and `expect_sample_rel`:
   - `Init` along `e ID : G ≃ Z_p` (`exists_equiv_mul_pow`);
   - `KeyGen` along `r ↦ r + b'/(ID − ID*)` (`key_eq`; `ID ≠ ID*` in `Z_p` from `natCast_bitsToNat_injective`, i.e. `CharP.natCast_injOn_Iio`, BS-F01);
   - `Challenge` along the identity (`F_target_eq`, `pair_pow_val_eq`).
5. **E-c** (`expect_simulate_bb1SimLazy`): `Games.expect_simulate_eager` with `O := bb1SimLazy`, `OE c := bb1SimImpl … (g^c) (e(g,g)^{αb'c})`, `used v := v.2.isSome`.
6. On the simulation side:
   - `(a, b', c)` splits into three draws (`Bridge.expect_sample_pair`);
   - `if true then …` reduces, and the unused `T` drops out (`expect_const`);
   - `c` moves past `ρ`.

**T3** (body in `BonehBoyenSecurity.lean`):
1. Unfold both games (`bb1SimGame_eq`, `prob_bind`; `if false …` reduces to `T`), fix `r`, `g`, `abc`, and swap `T` with `ρ`.
2. Apply **`BB1Sim.expect_bb1SimImpl_random`** (`Random`):
   - **E-T** on both sides: `expect_simulate_bb1SimLazy` with `zt T := (Z, T)`;
   - then `ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`.
   At the first valid `Challenge`, `expect_sample_rel` uses `R := Eq` along `T ↦ decodeT(M₁)⁻¹ decodeT(M₀) T` (the probe's P-3). Every other call does not read the bit (`bb1SimImpl_two_of_not`).

**`Relational`.** `expect_simulate_rel`:
- induction on `c`, generalizing the states (`simulate_pure/_query`, `expect_pure/_bind`; design §2.3, L1).

`expect_sample_rel`:
- `expect_bind`, `expect_pure`, `expect_sample_equiv`, then a pointwise comparison (L3).

Both proofs follow their frozen sketches, so the sketches are unchanged.

**Sketch refresh.**
- T2's `**Proof sketch.**` now names `setup_out`, `expect_simulate_rel` (twice), both eager steps, `expect_sample_rel`, `CharP.natCast_injOn_Iio` and `abs_expect_sub_le_expect`. It drops `Games.expect_simulate_congr` (design §5, risk 3).
- T3's names `expect_simulate_eager`, `expect_simulate_congr` and `expect_sample_rel`.
- The statement prose before each sketch is byte-identical (frozen check H2).

## The new declarations

68 public declarations: the ten readers and 58 helper declarations. All are in `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`; `BB1Sim.` below is its sub-namespace. There are no private ones.

| full name | home | kind | readers |
|---|---|---|---|
| `IBEScheme.sidImpl_zero_onSpec`, `_two_onSpec`, `_one_onQuery`, `_two_onQuery`, `_keyGen_ne_onSpec`, `_challenge_fresh_onSpec` | `Defs` | theorem (approved reader) | — |
| `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT` | `BonehBoyen` | theorem (approved reader) | — |
| `BB1Sim.sidSpec_dom_zero/_one/_two`, `sidSpec_rng_zero/_one/_two`, `zeroBits_eq_cast` | `Lazy` | theorem (glue for the game's types) | — |
| `BB1Sim.bb1SimLazyChal` | `Lazy` | def | `bb1SimLazyChal_fresh`, `bb1SimLazyChal_of_not` |
| `BB1Sim.bb1SimLazy` | `Lazy` | def | `bb1SimLazy_eq`, `_zero`, `_one`, `_two_fresh`, `_two_of_not` |
| `BB1Sim.bb1SimImpl_zero_coins`, `_one_coins`, `_two_of_not`, `_two_fresh_allOutputs`, `_allOutputs_of_ne_two`, `expect_simulate_bb1SimLazy` | `Lazy` | theorem | — |
| `BB1Sim.RealReads` | `Real` | structure (`Prop`) | its fields `encPP`, `msgSpace`, `keyGen`, `enc` (projections) |
| `BB1Sim.BB1RealState` | `Real` | abbrev (notation) | — |
| `BB1Sim.bb1RealAt` | `Real` | def | `bb1RealAt_none`, `bb1RealAt_some` |
| `BB1Sim.bb1RealLazy` | `Real` | def | `bb1RealLazy_zero_none`, `_none_of_ne`, `_some` |
| `BB1Sim.setup_out`, `sidImpl_allOutputs_some`, `sidImpl_none_of_ne`, `expect_simulate_sidImpl_bb1RealAt`, `expect_sample_bb1RealAt`, `expect_sample_sidImpl` | `Real` | theorem | — |
| `BB1Sim.exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq`, `pair_pow_val_eq` | `Coupling` | theorem | — |
| `BB1Sim.RelM` | `Coupling` | def | `relM_iff` |
| `BB1Sim.stepM_init_none`, `_init_some`, `_keyGen_none`, `_keyGen_target`, `_keyGen_ne`, `_challenge_none`, `_challenge_repeat`, `_challenge_invalid`, `_challenge_fresh`, `stepM_call`, `expect_simulate_bb1RealLazy` | `Coupling` | theorem | — |
| `BB1Sim.bb1SimLazy_random_call`, `expect_bb1SimImpl_random` | `Random` | theorem | — |
| `BB1Sim.prob_sidGame_coins` | `Chain` | theorem | — |

**Changes since checkpoint 1** (declared there as expected):
- **Nine additions:** the step-M rows `stepM_*`.
- **One statement change,** `BB1Sim.bb1SimImpl_two_of_not`. Its right-hand side was `bb1SimImpl b … 1 1 2 x s` and is now `bb1SimImpl false … 1 1 2 x s`: away from the first valid `Challenge`, the call reads neither the coins nor the challenge bit. The new form is more general; T3's comparison uses it.

`RealReads` and `setup_out` are the probe's statements, in namespace `BB1Sim`. Lint check 8 lists no new definition (*Lint*), so no `_iff` reader was added.

## Statement changes

**None.** The four targets' headers and statement prose, `bb1_sidSecure` and `prob_simulate_rel` are byte-identical to the patch base (frozen-header check, below).

## Checks

1. **Builds** (at the check head `408c8195`).
   - **Bootstrap:** see *Environment*.
   - **Final sweep** (`evidence/build/final-sweep/`): the 13 `DOWN` modules and the 5 helpers in the head order (`evidence/build/order-head.txt`, the helpers before `BonehBoyenSecurity`).
     - **18/18 rc 0**, 0 errors in both forms, 0 `sorry` warnings.
     - Sources bound to `git show HEAD` 18/18.
     - Every module that changed since the bootstrap was rebuilt from its final source, with its downstream, in order.
   - The root `TCSlib` was not built. Neither `audits/*/Checks` is downstream.
2. **Admissions** (`evidence/admissions/`):
   - `admissions.py` on the bootstrap logs, overridden module by module by the final sweep's: **18 declarations in 8 modules = base-sorries minus the four targets, PASS**.
   - The syntactic scan of the nine files against the patch base finds no new `sorry`/`admit`/`native_decide`/`axiom`/`@[simp`/`attribute`, and the four `sorry`s are gone: PASS.
3. **Statements.**
   - **decls2** against the patch base (`evidence/decls2/decls2-final.tsv`): **ADDED 68 (the ten readers + 58 helper declarations), 0 CHANGED, 0 REMOVED.**
   - **StmtDump** (`evidence/stmtdump/`): 74 constants with full names and types: the 68 new ones, the four targets, `prob_simulate_rel` and `bb1_sidSecure`. 0 missing, 0 errors (`final/`). The checkpoint-1 dump (65) is kept.
   - **Frozen-header check** (`evidence/headers/frozen/`, `frozen_check.py`): **12/12 PASS**.
     - Headers of the four targets identical (H1).
     - Their statement prose identical (H2).
     - `prob_simulate_rel` and `bb1_sidSecure` identical whole (H3).
     - Both files identical outside the bodies, sketches, helper imports and `## Contents` (H4).
   - Its six controls give `ALL_CONTROLS_OK True`. Each of these fails as it must:
     - a sketch edit spilling into the prose;
     - a one-character header change;
     - an unpermitted import;
     - an edit to `bb1_sidSecure`;
     - a docstring edit outside `## Contents`;
     - an edit to `prob_simulate_rel`.

     The unchanged file passes.
4. **Reader insertion check** (`evidence/headers/insertion/final/`; tool adapted from T4's):
   - **25/25 PASS**;
   - removal restores `4e220ead…` and `da875140…`;
   - the blocks are verbatim after their anchors (`Defs.lean:430`, `BonehBoyen.lean:412`);
   - final `97ecb6e0…` (563) and `88454d6f…` (760).

   Its 12 controls give `ALL_CONTROLS_OK True`:
   - a character changed: exactly one differing line;
   - a reader deleted: MISSING;
   - an extra line in either file;
   - a reader moved or reordered: MOVED;
   - a docstring edited;
   - a duplicate.
5. **Axioms** (`evidence/axioms/`): `Axioms.lean.txt`, run at the check head; `runs/`.
   - **Axiom list:** the 68 new constants (including the ten readers), the four targets, `prob_simulate_rel`, `bb1_sidSecure` and `exists_bb1_distinguisher`. **75 constants, all standard** (`propext`, `Classical.choice`, `Quot.sound` or a subset).
   - **Census:** every stored constant of the nine changed or new owners, **0 non-standard**:
     - `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3;
     - `Lazy` 24, `Real` 28, `Coupling` 20, `Random` 2, `Chain` 1.
   - **`sorry` dependency trace** (the staging probe's `#sorry_trace`): no constant whose own value uses `sorryAx` in the closure of `bb1_sidSecure` (20,373 constants, T4 in), `bb1_sim_real`, `bb1_sim_random`, `expect_simulate_rel`, `expect_sample_rel` or `prob_simulate_rel`.
   - A first run of the probe had an elaboration error in its own listing code (a counter typed as `MessageData`); it is kept as `runs-attempt1/`, and its census and traces already gave these results.
6. **Rule 10** (`evidence/rule10/`, `evidence/scan/`). 
   - **Canonical seals** A and B, strict and coe (the coe-A seal canonical), `-DmaxErrors=0`, over the full TCSlib import closure. They cover all nine changed or new owners at the check head (`rule10/head/`) and the four existing owners at the check base (`rule10/base/`, base tree `evidence/build/base-tree/`). **Every seal: rc 0, 0 errors, no failing declaration.**

     Requests per owner (A / B / coe-A / coe-B), head and base:

     | owner | head | base |
     |---|---|---|
     | `Relational` | 53 / 53 / 52 / 52 | 53 / 53 / 52 / 52 |
     | `Defs` | 805 / 806 / 804 / 805 | 805 / 806 / 804 / 805 |
     | `BonehBoyen` | 840 / 841 / 839 / 840 | 840 / 841 / 839 / 840 |
     | `BonehBoyenSecurity` | 2320 / 2321 / 2319 / 2320 | 2312 / 2313 / 2311 / 2312 |
     | `Lazy` | 868 / 869 / 867 / 868 | — |
     | `Real` | 871 / 872 / 870 / 871 | — |
     | `Coupling` | 874 / 875 / 873 / 874 | — |
     | `Random` | 871 / 872 / 870 / 871 | — |
     | `Chain` | 877 / 878 / 876 / 877 | — |

     - `Relational` matches the #351 precedent (53/53/52/52, 0 errors in all four variants).
     - **Differences from the base** (`rule10/request-diff-head-vs-base.txt`): none for `Relational`, `Defs` or `BonehBoyen`; the readers add no request.
     - `BonehBoyenSecurity` gains 8 requests in each variant: the helpers' definitions that it now imports (`bb1SimLazy`, `bb1SimLazyChal`, `bb1RealAt`, `bb1RealLazy`, `RelM`), their generated matchers (`bb1SimImpl_allOutputs_of_ne_two.match_1_1`, `stepM_call.match_1_1`) and `RealReads.mk._flat_ctor`.
     - No strict-only `FinDist` failure occurs (DW-10 Q3), because no failure occurs at all.
   - **Paired controls** (`mkctl_bb1sim.py`: T4's and the statement job's rows, plus new rows):
     - ten reader rows (negative: the unfolding the reader replaces; positive: the reader);
     - five helper-definition rows: `bb1SimLazy`, `bb1SimLazyChal`, `bb1RealAt`, `bb1RealLazy`, `RelM`.

     `Relational` and `BonehBoyenSecurity` define nothing, so they get no pair. Each probe takes a covering subset of the seal records. Results:
     - Unsealed pretest: all pass.
     - **Strict `ALL_OK True` and coe `ALL_OK True`**: 32 probes and 485 sealed negatives, each failing exactly once; every positive passes; there are no stray errors (`rule10/head/ctlcheck-{strict,coe}.*`).
     - Two earlier attempts are kept:
       - Attempt 1 of the whole run (`rule10/head-attempt1/`): its unsealed pretest failed because T4's inherited `BB1.idToZ` row opens `TCSlib.Cryptography.Candidates`, outside the helpers' imports. The row was restated with this job's opens.
       - Attempt 1 of the controls (`rule10/head/controls-attempt1/`): the `sidImpl_one_onQuery`/`_two_onQuery` negatives (`rfl`) held under the seal, since those readers need no sealed unfolding. They were restated as what the readers replace: a typed reader applied to the game-typed query, which needs `inLens`. The `bb1RealLazy` negative failed twice, not once, and is now wrapped in `by exact`.

       Both were control-statement defects, not module findings. The seals were not rerun for them.
   - **Explicit-unfold scan** over the nine changed files (`evidence/scan/head/`): 527 `rw`/`simp`/`unfold` items classified; **0 foreign**.
   - **Development seals** (`devseal.py`, not evidence): every helper and `BonehBoyenSecurity` passed A and B during the work.
7. **Frozen-file check.** `git diff --stat 72c0498a…` lists only the nine files of *Scope* (`evidence/frozen/diff-stat.txt`).
8. **Lint** (`evidence/lint/`):
   - `style_lint.py` on the nine files: **0 findings**.
   - `campaign_style_lint.py TCSlib/Cryptography --check8b`: **92 FAIL / 104 WARN over 524 files** at the check base (the baseline) and **92 / 104 over 529** at the check head. The line-set diff has **0 new, 0 gone**.
   - `sk15.py`: no new proof of 15 or more lines without a `**Proof sketch.**`. The one finding is the base's `bb1SimChal_fresh`.
9. **Sizes and widths** (`evidence/sizes/`): every new or changed file is at most 760 lines and 100 characters per line: PASS.
10. **Docstrings.**
    - Every new declaration has a docstring that states it in words and gives its formula, with a [BB04, …] tag from the DW-7 transcription or a glue note.
    - The tags used are `[BB04, proof of Theorem 4.1, *Setup*/*Phase 1*/*Challenge*/*Phase 2, Guess and the advantage*]`, `[BB04, §4.1, *Setup*]`, `[BB04, §2.1]` and `[BB04, §4.4]` (the latter already in `bb1_sidSecure`).
    - The quotations are from the transcription's passages.
    - The helper module docstrings have title, Main definitions, Main results and References.
    - `BonehBoyenSecurity.lean`'s `## Contents` lists the five helpers.
11. **Name-clash and shadow scans** (`evidence/clash/`):
    - (a) `clash_scan.py` (check base → check head): **68 new names, 0 CLASH, 0 DUP-NEW**.
    - (b) A Lean probe over the whole import environment (TCSlib, Mathlib, core; `clash/shadow/`): **none of the 68 new short names (last component) is the last component of any other constant.** Its control (`ShadowCtl.lean.txt`) finds `Option.bind_assoc` and others for `bind_assoc`, so the scan does find matches. Attempt 1 printed the same result and then kept running for an hour; it was stopped and replaced (`runs-attempt1/`).
    - (c) None of the 68 new short names occurs, as a whole identifier, in a `DOWN` module at the check base, so no unqualified use can change its resolution (`uses-in-DOWN.txt`). A first version of this scan matched T4's private primed `BB1Machine.sidSpec_rng_one'`/`_two'`; the file records it.

## Overlap and reuse

Searches are in `evidence/overlap/searches.txt` (`git grep` over TCSlib at the check head) and in sub-agent A's notes (`evidence/subagents/stepM/NOTES.md`, TCSlib and Mathlib).

**Design §2.4's table, confirmed at the check head:**
- `ProbComp.expect_simulate_congr` (`Games/Hopping.lean:384`): one state type; the `R = Eq` case. Used by T3.
- `Games.expect_simulate_eager` (`Hopping.lean:494`): used by E-h, E-c and E-T. **No new eager lemma.** `expect_simulate_bb1SimLazy` and `expect_sample_bb1RealAt` are instances, each a single application with the handler-specific hypotheses (DL-33 respected).
- `ChallengeSim.expect_simulate_eager` (`OracleSecurity/ChallengeSim.lean:148`) is a different, CPA-shaped lemma and is not used.
- `simulate_eq_of_abs(_bounded)` (`Games/Simulate.lean:334`, `:357`), `ETTGame.expect_simulate_abs(_inv)` (`EncryptThenTag/Tools.lean:65`, `:88`), `PRFGame.expect_lazyImpl` (`OracleFromPRF/Lazy.lean:351`), `ETTGame.expect_ettImpl_lazy` (`EncryptThenTag/Lazy.lean:499`), `HashSignFill.expect_simulate_sample_once` (`HashAndSign/OneQuerySampling.lean:47`) and `LamportFill.planted_coupling` (`Lamport/Planted.lean:403`): each is as design §2.4 describes. None states R1, step M, E-h or E-c, and none was copied.
- Averaging bound: `ProbComp.abs_expect_sub_le_expect` (`Probability.lean:409`) is used in T2's body. The private ETT copy (`EncryptThenTag/Forgery.lean:515`) is untouched (Q6, DL-40), and **no third copy** was added.

**Helpers and their nearest relatives:**
- **`BB1Sim.sidSpec_dom_*`/`sidSpec_rng_*`/`zeroBits_eq_cast` (`Lazy`)** are the probe's `dom_*`/`rng_*`/`zeroBits_eq_cast` (statement job's `probe/PlProbe/BB1SimStepM.lean.txt`).
  - **Disclosed overlap:** T4's `BonehBoyenMachine/Oracles.lean:77`, `:84` has **private** `BB1Machine.sidSpec_rng_one'`/`_two'` with the same statements as my public `sidSpec_rng_one`/`_two`.
  - T4's files are frozen here, so its copies stay. A later cleanup could re-point them to the public ones.
- **`bb1SimLazy`/`bb1SimLazyChal`, `bb1RealAt`/`bb1RealLazy`:** specific lazy handlers. Their relatives `PRFGame.lazyImpl` (`OracleFromPRF/Lazy.lean:149`) and `ETTGame.ettLazy` (`EncryptThenTag/Lazy.lean:441`) are other games' handlers; no shared generic form exists.
- **`RelM`, step M's rows, `stepM_call`:** specific to BB1. They are ported from the probe's P-2 (statement job, `a3cb45f6`), with the probe's algebraic hypotheses proved as `exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq` and `pair_pow_val_eq`.
- **The group algebra:**
  - `natCast_bitsToNat_injective` is Mathlib's `CharP.natCast_injOn_Iio` (`Mathlib/Algebra/CharP/Basic.lean:55`, with `ZMod.charP`) plus `bitsToNat_lt`/`bitsToNat_injective` (`Asymptotic/Sampling.lean:412`, `:417`). It is a two-line composition with no Mathlib or TCSlib equivalent (BS-F01).
  - `exists_equiv_mul_pow` composes `Equiv.mulLeft` with `Equiv.ofBijective _ (pow_val_bijective_of_ne_one …)` (`Pairing/Group.lean:252`).
  - `key_eq`, `F_target_eq` and `pair_pow_val_eq` are BB04's computations from `pow_val_add`/`_neg`/`_mul`/`_mul_GT` and `bilinear_pow` (`Pairing/Group.lean`).
  - None restates a Mathlib `ZMod`/`orderOf` fact.
- **`setup_out`, `RealReads`:** the probe's, ported.
- **`sidImpl_allOutputs_some`, `sidImpl_none_of_ne`:** case facts about `IBEScheme.sidImpl` from its readers. They have no published equivalent (the readers state single cases).
- **`prob_sidGame_coins`, `expect_bb1SimImpl_random`:** T2's and T3's chains. They have no relative.

## Exchange commits (BS-F08, disclosed)

The exchange commits `1ef26470` ("fill bb1-sim: checkpoint 1") and `e8b3388d` ("fill bb1-sim: final") carry an SSH signature (`gpgsig`).
- **Cause:** I created them with `git -c commit.gpgsign=false`. The `git pull --rebase` before each push then re-created them, and this host's global `~/.gitconfig` sets `commit.gpgsign = true` (`gpg.format = ssh`), so the platform key signed them.
- **Not fixed:** fixing them would need a force-push, which the brief forbids.
- **Deliverable unaffected:** the four `fill/bb1-sim` commits in `patches/` are unsigned (`COMMITS.tsv`, signing `none`), and `git am` reproduces them.
- **This note's commit** was made, and rebased, with `-c commit.gpgsign=false` throughout.

## Scope requests

None. The route needed no other reader, import or frozen-file change.

## Questions for Seyoon

None.

## Evidence

`evidence/SHA256SUMS` lists every evidence file, and the top-level `SHA256SUMS` lists every delivered file; their paths equal the delivered files. The main entries:
- `logs/` (preflight, cache, mkbase, records tip, the parallelism ruling);
- `build/` (bootstrap, checkpoint-1 and final sweeps, the base tree for the base seals);
- `admissions/`, `decls2/`, `stmtdump/`, `headers/{insertion,frozen}/`, `axioms/`, `rule10/{head,base,head-attempt1}/`, `scan/`, `statements/`, `lint/`, `sizes/`, `clash/`, `overlap/`, `frozen/`;
- `subagents/stepM/`;
- `tools/`, every tool used, with its provenance in its header.
