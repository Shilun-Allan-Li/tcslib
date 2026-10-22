# C1 seam-layout fill — REPORT (`Turing.exists_seamLayoutTM`, `Build/SeamLayout.lean`)

**Outcome: the target is proved in full.** `Turing.exists_seamLayoutTM` elaborates with no
`sorry`, no error and no warning, with axioms exactly
`[propext, Classical.choice, Quot.sound]` and the constant **`C = 18`**. All four checkpoints
were reached, each at its own commit (checkpoint zips `fill-c1-seamlayout-cp1.zip` and
`-cp2.zip` were written; checkpoints 3 and 4 completed in one working stretch and the final
zip, written at the delivery commit, supersedes per-checkpoint zips for them).

## 1. Preflight (addendum v2.3, Part 1)

Quoted from `evidence/logs/preflight.log` (2026-10-22, 02:06 UTC):

- `nproc` = 4.
- cgroup v1; `memory.limit_in_bytes` = 9223372036854771712 (no cgroup limit, "max").
  Per v2.3 item 1, headroom = `MemAvailable` = 15,871,524 kB = **15.14 GiB ≥ 4 GiB: PASS**.
  `memory.stat`: rss 516096, cache 16371712, shmem 15327232 (memory in use far below 1 GB; the
  rest of `usage_in_bytes` = 6.34 GB is page cache, not a shortage). No `oom`/`oom_kill` event
  and no Lean exit 135/137/139 occurred at any point.
- Disk (clone `/home/user/tcslib`, ext4 on `/dev/vda`): **24.56 GiB free ≥ 12 GiB: PASS** at
  the initial preflight; re-check before the cache step (after the toolchain install):
  **22.15 GiB free ≥ 8 GiB: PASS**.
- Nothing (clone, `.lake`, oleans, TMPDIR) is on a memory-backed filesystem.
- `/usr/bin/time -v` is **not available** on this host; the bootstrap and sweep logs record
  per-module start/end wall-clock times instead (item 6). No module stalled; no self-imposed
  timeouts were used.

Lean 4.25.0 started normally (`lean --version` exit 0, commit `cdd38ac5…`); **Part 2's shim was
not needed and was not used.**

## 2. The cache (addendum v2.3, items 2–4), as run

Roots: `evidence/logs/mathlib-roots.txt`, computed from the order list
`campaign/fills/c1/orders/c1-fill-seamlayout.txt` (94 modules) exactly as item 2 prescribes,
after the region (a0) import edit: **40 Mathlib roots** (matches the brief). Command as run,
from the clone root:

```sh
TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt) \
  2>&1 | tee evidence/logs/cache-get.log
```

Result: **1002/1002 files downloaded, 0 failed**, unpacked in 3967 ms, exit 0. The unfiltered
`lake exe cache get` was never run; no cleaned retry (item 4) was needed.

Item 2's manifest check (`evidence/logs/manifest-check.log`): all **11 packages present** in
`.lake/packages` match `lake-manifest.json`'s URL and revision exactly. Four manifest packages
(`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` — the documentation toolchain) were not
fetched by the narrowed cache and are **absent, not mismatched**; no later Lake command
re-cloned or updated any package.

Item 3: narrowed get exit 0 with no failed download; `find .lake/packages -name '*.olean'
-size 0` prints nothing; the probe importing the first root elaborates
(`evidence/logs/cache-probe.log`, exit 0).

## 3. Base, branch, bootstrap

- Brief SHA-256 `85ea4a61116abd75d7dd54597b258933bf6d5fbd67ee4e25aa753c782f4bffec` and addendum
  v2.3 SHA-256 `1ea7a37656f1fb76645673ae2dca68a00d12562b214f6dc36dac61a95dc13662` verified; the
  repository copy of the brief at the campaign tip matches the attachment except for the three
  `@ANCESTOR@` placeholders.
- `git merge-base --is-ancestor 1c06ea94d0eb9226c355ffa8941aa6ed4ab9c1d6 HEAD` at the fetched
  `complexity/arora-barak-ch3-4` tip: **PASS**.
- Branch `fill/c1-seamlayout` created at exactly **`1c06ea94d0eb9226c355ffa8941aa6ed4ab9c1d6`**
  (`git rev-parse HEAD` confirmed); no rebase, merge or cherry-pick at any point.
- Overlay check: after the region (a0) edit the file equals
  `campaign/fills/c1/inputs/c1-fill-seamlayout/SeamLayoutOverlay.lean.txt` byte for byte.
- **Bootstrap** (`evidence/logs/bootstrap.log`): all 94 modules of the order list checked in
  order with `scripts/lean_check_tree.sh`, one Lean process at a time, **94/94 exit 0**
  (addendum item 5: the full list once up front, the downstream facade last).
- **Base sorry set recorded first**: 35 warnings over 15 modules, matching
  `campaign/fills/c1/logs/c1-fill-seamlayout-base-sorries.txt` per module and in total
  (observed by line in `evidence/logs/base-sorries-observed.txt`; the recorded list is by
  declaration name — per-module counts agree exactly; SeamLayout's one is the target, 97:8 on
  the overlay). **No difference.**
- Import probe at base: 0 errors, 0 warnings (`evidence/logs/import-probe-base.log`).

## 4. What was proved, and how (the checkpoints)

### CP1 — the two leaves, framed

- `sl_PairPhase`, `sl_pairSkipTM`; `sl_SplitPhase`, `sl_unarySplitTM` (both machines read
  their actions through the published `Action.apply_*` field equations only; `step` and
  `Action.apply` are never unfolded, even for the leaves).
- Framed contracts, each with an exact time, a first-visit cut at `done`, an explicit endpoint
  over an arbitrary configuration, and silence at every time up to the exit:
  - `sl_pairSkipTM_run`: exactly `2|a| + 2` steps on `pairEncode a tail`, head `2|a| + 2`
    cells right, everything else unchanged. By induction on `a`; the pair reads from
    `FinTM.bufferTape_append_shift` and `pairEncode_eq`.
  - `sl_unarySplit_copy`, `sl_unarySplitTM_run`: exactly `q + 3` steps; `1^q 0` written on
    `sm` from two cells past its head (that head ends on the written terminator), the
    terminator's source cell blanked and **not restored**, the source head one cell past it.
    By induction on `q`.
- **Why no row serves each leaf** (also in their docstrings): the pair scan exits at a
  non-blank aligned pair (`false, true`), which no seek row reads — the seek family stops only
  at blanks; the split writes at an offset destination while its source head advances, stops
  at a `false` terminator rather than a blank, and blanks a single source cell — no copy or
  transfer row does any of this.
- Supporting privates: `sl_apply_eq` (the applied-action normal form of a silent,
  input-stationary action through `Action.apply_state/_inputPos/_workTapes/_workTapePos/
  _output`, `Cfg.workTapeSymbols_eq` and `moveInputPos_zero` only), `sl_step_move`,
  `sl_split_step_true`, `sl_split_step_exit`, `sl_pairSkip_two_steps`.

### CP2 — the word identities (the ruling's route)

All through `Turing.pairEncode_eq` and the published `TuringMachine/BufferWords` API — never
`serializeK_eq`, never `StepBlock`'s private copies:

- `sl_bufferTape_unary_int` — the unary word's cells at an integer index
  (`FinTM.bufferTape_unary`);
- `sl_sm_word` — the written interval `[2, 2 + q]` over a blank tape reads
  `bufferTape (1^q 0) (z − 2)` (`sl_bufferTape_unary_int`, `bufferTape_eq_none_of_not_mem`);
- `sl_reverse_read` — **phase 5's backward read**: cell `q − p` of `1^q 0` is cell `p` of its
  reversal, `p ≤ q + 1`; derived from `bufferTape_nat`, core `List.getElem?_reverse`,
  `bufferTape_left`, `bufferTape_of_neg` and `bufferTape_eq_none_of_not_mem`, as the brief
  prescribes (no published reverse lemma exists);
- `sl_read_unary` — the source word's unary field at `2|a| + 2 + p`
  (`bufferTape_append_shift`, `bufferTape_nat`, core `List.getElem?_append_left`,
  `bufferTape_unary`);
- `sl_read_table` — the table field past `2|a| + 2 + q + 1` (`bufferTape_append_shift`; right
  blank and beyond included);
- `pairSkip`'s pair reads: inside `sl_pairSkipTM_run` (CP1), from `_append_shift` and
  `pairEncode_eq`, by induction on `a`;
- `s.drop r` read directly through `FinTM.bufferTape_drop`; `s.take (h + q)` through
  `FinTM.bufferTape_take` and `bufferTape_eq_none_of_not_mem` at the tape normalizations.

### CP3 — phases 1–7 on the host, with the time ledger

- The phase key `sl_Key` (8 constructors, route order), the carrier family `sl_Ph` (an
  `abbrev`), the machines `sl_part` (four seek/sweep rows, the transfer, the two leaves), the
  dispatch table `sl_red`, and the `Fintype`/`DecidableEq` instances by
  `cases i <;> dsimp only [sl_Ph] <;> infer_instance` — the StepBlock precedent followed, not
  transcribed (that module is outside the closure and was not cited).
- `sl_cfg` — the canonical mid-run configuration: a control state and the three owned tapes'
  contents and heads as the **same nested `Function.update` triple as the target's endpoint**
  (src innermost, then tbl, then sm), over an arbitrary frame `d`.
- `sl_rewrap` (the dispatch rewrap `c'.mapState (fun _ => ⟨i', ent⟩) =
  c₂.mapState (Sigma.mk i')` from fieldwise agreement, via `Cfg.ext` and the published
  `Cfg.mapState_*` equations), `sl_guard` (a phase guard from a row's first-visit cut),
  `sl_tagged_ne_done` (a tag other than the last phase's is never the exit).
- `sl_phase1` … `sl_phase7`: each phase hosted by **`Turing.phaseHostTM_run`** — the row or
  leaf contract supplies the endpoint and the cut, the cut supplies the guard, and the lemma's
  two components give the dispatch into the next phase's entry and the whole lockstep window
  (used for the global first-visit cut). Each phase lemma is stated over generic values for
  the tapes and heads it does not touch, so the chain instantiates them exactly.

### CP4 — phase 8, silence, the frame, the target

- `sl_phase8`: the clear, covered by `phaseHostTM_run`'s **first component** up to and
  including its exact time `2(h + q) + 2` (see §5 on the deviation), ending at the exit
  `⟨.clearHead, .done⟩` with the source blank; its second component is the strict cut.
- The main proof: the start configuration rewrapped onto phase 1 (`hstart`, consuming the
  seven start hypotheses once), the eight phases chained by `MultiTapeTM.runFrom_add`
  (`hc1`–`hc7`, `hfin`), and:
  - **state** at `T`: `some ⟨.clearHead, .done⟩` — `done` is clear's exit, as the docstring
    requires; **seven dispatches**, no extra rewind after transfer or clear;
  - **frame**: the full triple `Function.update` endpoint for both `workTapes` and
    `workTapePos` is **definitional** at the end — `sl_cfg`'s fields are literally the
    target's triples (src ↦ blank / `bufferTape v` on tbl / `bufferTape (1^q 0) (· − 2)` on
    sm; heads 0, 0, 0) — and `inputPos` and the output ride through every phase untouched;
  - **silence** at every `u ≤ T`: the output-prefix sandwich — `d.output <+:` output at `u`
    `<+:` output at `T` `= d.output` (`MultiTapeTM.output_prefix`, `List.IsPrefix.eq_of_length`);
  - **the cut** (`∀ u < T`, not at `done`): the eight lockstep windows partition `[0, T)`;
    phases 1–7 by `sl_tagged_ne_done`, phase 8 by the clear row's own cut.

### The time ledger and `C`

`T = 2n − r + 4h + 5q + 2|v| + 23` (chosen before the configuration: a function of `a`, `v`,
`q`, `r` alone), split by `hTsplit` over the per-phase ledger, with the seven dispatch steps:

| phase | row/leaf | steps |
|---|---|---|
| 1 | `skipTM` over `s.drop r` | `n − r + 1` |
| 2 | `skipBackTM` over `s` | `n + 3` |
| 3 | `sl_pairSkipTM` | `h` |
| 4 | `sl_unarySplitTM` | `q + 3` |
| 5 | `walkTM` over `(1^q 0).reverse` | `q + 2` |
| 6 | `transferTM` over `v` | `2|v| + 2` |
| 7 | `skipBackTM` over `s.take (h + q)` | `h + q + 3` |
| 8 | `clearTM` over `s.take (h + q)` | `2(h + q) + 2` |
| dispatches | one per join | `7` |

with `h = 2|a| + 2`, `n = |s| = h + q + 1 + |v|`; `T ≤ 7n + 18` (slack `h + 3|v| + r`) and
`7n + 18 ≤ 18(n + 1)`, so **`C = 18`** (`by omega` from `length_pairEncode` and `r ≤ n`).

## 5. Deviation from gate 46 (c), recorded: phase 8's transport

The carry-forward suggests running phase 8 through
`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` "as `phaseHostTM_run`'s own proof does", with
the trivial guard. That transport's `hagree` hypothesis is a **table-level** fact about
`Turing.phaseHostTM` (`host.tr (emb q) … = …`), which has no published lemma;
`phaseHostTM_run`'s own proof discharges it with `simp only [phaseHostTM]` — an unfold of
another file's definition that rule 10 bans for this fill (the seal test with
`attribute [local irreducible] Turing.phaseHostTM` would fail on it). Instead the dispatch
table gives phase 8's `done` a **self-redirect**
(`sl_red .clearHead .done = some ⟨.clearHead, .done⟩`). `phaseHostTM_run` then applies to
phase 8 as to every other phase, and its **first component** — the `∀ u ≤ T` lockstep window —
delivers the clear's exact endpoint at `T₈` and every earlier state. The dispatch the
self-redirect would take happens at `T₈ + 1`, **strictly outside the contract's horizon**, so
the eight phases, the seven dispatch steps, the exact ledger, `C = 18`, and "clear's `done` is
the exit `done`" are all exactly as the binding sketch requires. The statement is unchanged;
nothing is proved modulo anything.

Escalations: **none**. Promotion candidates: **none** (every helper is seam-layout-specific;
`sl_rewrap`/`sl_guard` are thin wrappers over `Cfg.ext` and `phaseHostTM_run`'s shapes).

## 6. Rule 10 (the pinned base, no unfolding)

- **Declarations cited outside the file.** All 45 names of the issued probe resolve and were
  available; of them the fill cites: the five rows' `_run_ofCfg` contracts, `phaseHostTM`,
  `phaseHostTM_run`, `MultiTapeTM.output_prefix`, `pairEncode`, `pairEncode_eq`,
  `length_pairEncode`, `FinTM.bufferTape` with `_nat`, `_left`, `_of_neg`, `_drop`, `_take`,
  `_eq_none_of_not_mem`, `_unary`, `_append_shift`, `Cfg.ext`, `MultiTapeTM.step_of_some`,
  `runFrom_zero`, `runFrom_succ_eq_step'`, `runFrom_add`, the five `Action.apply_*` equations,
  the five `Cfg.mapState_*` equations, and `Cfg.workTapeSymbols_eq`.
  **Beyond the issued probe** (each added to
  `evidence/probe/SeamLayoutFillProbeExtended.lean` and re-run, 0 errors): the row machine
  definitions `skipTM`, `skipBackTM`, `walkTM`, `transferTM`, `clearTM` (named by `sl_part`;
  read only through their `_run_ofCfg` contracts), the phase alphabets `SeekPhase`,
  `SweepPhase`, `MultiTapeTM.runFrom_succ_eq_step` (the unprimed sibling of the probe's
  primed form), `moveInputPos_zero`, `Cfg.mapState` as a term, and the model types; plus the
  core/Mathlib lemmas listed in that probe (`Function.update_*`, `Option.*`, `List.length_*`,
  `List.getElem?_*` — core `List.getElem?_reverse` as the brief prescribes —
  `List.IsPrefix.eq_of_length`/`length_le`, `decide_eq_*`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `Int.toNat_of_nonneg`, `Int.natCast_nonneg`, cast and order basics,
  `if_pos`/`if_neg`).
- **No unfolding.** No `unfold` appears in the diff. Every `rw`/`simp only` argument is a
  published lemma, an `if_pos`/`if_neg`/`show`-bridge, a local hypothesis, or one of the
  fill's own `sl_` definitions (`sl_cfg`, `sl_red`, `sl_Ph`, `sl_pairSkipTM`,
  `sl_unarySplitTM` — own-file definitions). `MultiTapeTM.step` and `Action.apply` are not
  unfolded even for the leaves: the leaf steps go through `step_of_some` and the published
  `Action.apply_*` field equations.
- **Seal test** (`evidence/probe/SeamLayoutSeal.lean`, log `evidence/logs/seal-test.log`): a
  scratch copy of the module with `attribute [local irreducible]` on `FinTM.bufferTape`,
  `pairEncode`, `Cfg.mapState`, `Action.apply`, `MultiTapeTM.step`, `MultiTapeTM.runFrom`,
  `MultiTapeTM.outputSymbol`, `phaseHostTM`, the five row machines, `Cfg.workTapeSymbols`,
  `Cfg.inputSymbol`, `moveInputPos`, `Function.update`, `List.take/drop/reverse/replicate`
  still elaborates (0 errors).
- **Probe re-run after delivery**: `SeamLayoutFillImportProbe` 0 errors, 0 warnings
  (`evidence/logs/import-probe-after.log`); the extended probe likewise
  (`evidence/logs/import-probe-extended.log`).

## 7. Rule 11 (MIG-1)

- `git diff 1c06ea94..HEAD` greps **0** occurrences of the six R3 canonical rows
  (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
  `incrementTM_run_overflow` as bare `_run` forms) — only the framed `_run_ofCfg` forms are
  cited.
- No private declaration of another file is cited (every cited name is public at the base;
  the import probe plus the extended probe witness resolution from the import context).
- Every new private carries the `sl_` prefix. **No new public declaration** (ground rule 3);
  the statement, its docstring, the module header and all other files are untouched; the one
  import added is region (a0)'s `TCSlib.Complexity.TuringMachine.BufferWords`.

## 8. Duplication governance

- `screen-before` (one run, `nice -n 10`, before any edit): matches the recorded base —
  **867 declarations, 1,112 pairs, 406,659 characters** (`logs/screen-before.txt`, first
  line: `declarations screened: 867; copy pairs (target reproduces >= half of source): 1112;
  reproduced text: 406,659 chars`).
- `screen-after` (one run, `nice -n 10`, after the fill; `logs/screen-after.txt`, first line):
  `declarations screened: 897; copy pairs (target reproduces >= half of source): 1143;
  reproduced text: 431,082 chars`.
- **New copies: none.** No pair reaches 90%. **No new cross-file pair has an owned-file
  declaration on a side** (grep over the after-output: zero `SeamLayout` pairs with another
  file). The known hazards were checked by name: no pair of an `sl_` declaration with
  `StepBlock`'s word identities or phase key, with `UniversalStartup`, or of the pair-skip
  leaf with `Build/Primitives`' `pairExtractTM` family. (An intermediate draft of
  `sl_apply_eq` did pair at 63% with `Primitives.lean::pairExtractTM_fst_run` through the
  shared `apply Cfg.ext`-with-bullets shape; its proof was restated fieldwise — commit
  `09773a66` — and the official after-run has no such pair.)
- The **31 new pairs are all in-file**, among the fill's own privates (897 − 867 = 30 new
  screened declarations; 1,143 − 1,112 = 31 new pairs), each below the 90% copy line:
  - **26 pairs among `sl_phase1`–`sl_phase8`** (52%–89%; the maximum, 89%, is
    `sl_phase7` vs `sl_phase2`, the two instantiations of the same `skipBackTM` row over
    different words). Justification: each phase lemma is the instantiation of the one public
    `Turing.phaseHostTM_run` over the shared `sl_cfg` carrier — exactly the "one proof per
    shared argument" discipline of ground rule 7; the shared text is the hosted-run
    statement, guard and rewrap scaffold, while the mathematical content (the row or leaf
    applied, its reads, the endpoint values and the join arithmetic) differs per phase.
  - **4 pairs among the step lemmas** `sl_step_move`, `sl_split_step_true`,
    `sl_split_step_exit` (82%–87%). Justification: all three are instances of the
    applied-action normal form `sl_apply_eq`, differing in the written cells and head moves;
    the shared text is that normal form's quotation.
  - **1 pair** `sl_read_unary` vs `sl_read_table` (54%). Justification: both decompose the
    same source word through `pairEncode_eq` and `FinTM.bufferTape_append_shift`; the shared
    text is the decomposition bridge, the fields read differ.

## 9. Edge cases (gate guidance; sanity checks)

Checked **by evaluation of the closed form** `T = 2n − r + 4h + 5q + 2|v| + 23` and by the
per-phase times fixed in the proof:

- the auditor's four instances: `a=v=[], q=0, r=0` → `T = 37`; same at `r = 3 = n` → `34`;
  `a=[false,true], v=[], q=2, r=9` → `66`; `a=[], v=[false,true,false], q=0, r=0` → `49` — all
  four match the gate's recorded times;
- `r = n`: phase 1 is the skip over `s.drop n = []`, 1 step (`|[]| + 1`);
- `q = 0`: phase 5 walks `[false].reverse`, 2 steps; `unarySplit` in 3 (`q + 3`);
- `v = []`: transfer in 2 (`2·0 + 2`; the hypothesis's cell `|v|` at `n` is the right blank);
- `a = []`: `h = 2` (`length_pairEncode`);
- an extra populated tape with a negative head position, and all-`false` table bits: instances
  of the proved statement itself — the theorem quantifies over every frame `d` (the endpoint
  changes exactly the three owned tapes and heads) and every `v`.

## 10. Final checks

1. `Build/SeamLayout`: **zero errors, zero warnings, no sorry**
   (`evidence/logs/final-module-check.log` via the sweep; also checked standalone).
2. Final sweep over all 94 modules of the order list, one Lean process at a time
   (`evidence/logs/final-sweep.log`): **94/94 exit 0**; sorry warnings exactly the base's 35
   minus SeamLayout's one = **34**, in the base's 14 other modules (quoted tail in §11).
3. Import probe re-run: 0 errors, 0 warnings; extended probe: 0 errors.
4. **Axioms** (`evidence/logs/axioms.log`, a scratch copy with `#print axioms` for the target
   and all 35 new privates): `Turing.exists_seamLayoutTM` depends on exactly
   `[propext, Classical.choice, Quot.sound]`; every private is within that set; **no
   `sorryAx` anywhere**.
5. **Lint** (`evidence/logs/lint-after.log`):
   `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build` →
   **0 FAIL**, 31 WARN over 38 files. The base was 30 WARN; the one new WARN is the size
   warning on `SeamLayout.lean` (1755 lines > 1000). Justification on record: ground rule 8 of
   the brief ("Size. No cap; file size alone is not a driver"); the file carries one public
   theorem whose eight-phase composition the brief mandates in this one module.
   **No line exceeds 100 characters.**

## 11. Logs quoted

- Final sweep: `evidence/logs/final-sweep.log` — 94 × `exit=0`, `FINAL SWEEP DONE`, then the
  facade re-check after the last commit (`exit=0`). Per-module sorry warnings: 34, exactly the
  base's 15-module distribution minus `SeamLayout`'s one (TimeConstructible 2, InputDevice 3,
  InputWindow 1, Loop 5, Primitives 3, RecordTable 4, Wrappers 2, ZoneRebalance 2,
  CodeSimulator 2, Composition 3, Encoding 1, NDCodeSimulator 2, Simulation 1, UniversalK 3;
  **SeamLayout 0**).
- Screen outputs: `logs/screen-before.txt` and `logs/screen-after.txt` in the zip; the two
  totals lines are quoted verbatim in §8.

## 12. Size and inventory

- `Build/SeamLayout.lean`: **1755 lines** (base 120; overlay 121). Declarations: **1 public**
  (the frozen target, now proved), **35 private** (base: 1 public, 0 private):
  - leaves: `sl_PairPhase`, `sl_pairSkipTM`, `sl_SplitPhase`, `sl_unarySplitTM`;
  - steps: `sl_apply_eq`, `sl_step_move`, `sl_pairSkip_two_steps`, `sl_split_step_true`,
    `sl_split_step_exit`;
  - leaf contracts: `sl_pairSkipTM_run`, `sl_unarySplit_copy`, `sl_unarySplitTM_run`;
  - word identities: `sl_bufferTape_unary_int`, `sl_sm_word`, `sl_reverse_read`,
    `sl_read_unary`, `sl_read_table`;
  - host: `sl_Key`, `sl_Ph`, `sl_part`, `sl_red`, `sl_instFintypePh`, `sl_instDecEqPh`,
    `sl_cfg`, `sl_rewrap`, `sl_guard`, `sl_tagged_ne_done`;
  - phases: `sl_phase1` … `sl_phase8`.
- Regions touched: (a0) the one authorized import; (a) the privates above; (b) the proof.
  Region (c) is not used (nothing is partial). The statement, its docstring, the module
  header and every other file are byte-identical to the base.

## 13. Delivery

`fill-c1-seamlayout.zip`: this `REPORT.md`; the full modified source
(`src/TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean`); the `git format-patch` series
against the base (`patches/`); a git bundle whose only prerequisite is the base
(`fill-c1-seamlayout.bundle`, verified); the bootstrap, final-sweep, axiom, seal, lint, cache,
preflight and probe logs; both copy-text screens; `SHA256SUMS`.
