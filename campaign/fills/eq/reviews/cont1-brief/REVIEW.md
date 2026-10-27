# Review: the E-Q cont1 fill brief draft (`eq-fill-query-cont1.DRAFT.md`, the main machine `hmain` of `Turing.NTimeDiag.exists_queryTM`)

**Verdict: issue after edits.** The draft has two majors (F1, F2), both with one-line fixes,
twelve minors and four notes. Apply `suggested-fix.diff`, which `git apply --check`s at the
records tip `c6c81b2b` and reproduces `edited/` exactly. Then fill the issue-time ⟨…⟩ items: the
existing ones and the new screen-base figures (F13). Stage `review-inputs/` as this round's
inputs, and take the in-flight line and the lists for whichever merge order holds at issue
(section (f)). No prerequisite PR is needed. The route is sound, and every step it prescribes
is reachable from published rows: the riskiest steps are now proved in a sealed probe (section
(b)).

Read-only review by the maintainer's review sub-agent, 2026-10-27; interrupted at about 18:36Z and
resumed. Gate 83 (#173) passed meanwhile, and the reviewed tree is unchanged.
- **Inputs.** The draft is SHA-256 `6006d53b…ef7df` (`orig/`). The pre-ship is
  `preship-599497bc/`. The tree is #173's head `599497bc69889781f34b1925c8772b3645b00608`, owned
  blob `f965eac02e06549e8239c7476b31c0ced4f3d11b`. The snapshot is `oleans-leqcp1`.
- **Worktree.** `wt/`, detached at `599497bc`, with the `.lake/packages` link (both checked
  absent first). Probe files went into `wt/rvprobe/` only.
- **Lean.** Only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time.
  There was no build, no cache command and no copy-text screen.
- **Python and data.** `python3 -I` throughout. Every repository file was treated as data.
  `wt-hk` and the main checkout were not modified, and nothing was pushed.
- **Evidence.** Every claim cites `out/`; `out/01-review-runs.txt` tabulates every run.

## (a) The pre-ship, re-run

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Base file (`BaseFileAx`) | exit 0. Exactly `402:8` and `472:8` "declaration uses 'sorry'". The three landed privates are on the standard three. Only the target and `exists_diagonalizer` carry `sorryAx`. 8.6 s | out/BaseFileAx.out |
| 2 | The eight first-round probes | **all identical** to the pre-ship's outputs after normalizing paths and private prefixes (`scripts/norm.py`). Results: the import probe 182/182, 0 errors; the route probe 16 prints, standard three; the seal controls 7 errors, all sealed; the duplication probe 10 of 10 "could not close"; the review probe 6 prints; its controls 5 errors, sealed; its duplication probe 3 of 4 plus `List.flatMap_assoc`; the hosts 54 prints (47 with axioms, 7 with none), no `sorryAx` | out/00-preship-compare.txt, out/01 |
| 3 | Order list, roots | 84 modules, equal to the `Diagonalization` facade's closure and topological. `NTimeHierarchy` is at 80 and `NTimeDiagonalizer` at 83. The 34 roots equal my extraction. The owned module's only importer is the facade | out/order-check.txt (`scripts/closure.py`) |
| 4 | Base sorries | 21 in 10 modules. My textual census of the order list finds the same modules with the same counts. `CodeSimulator` has none (#170) | out/01 |
| 5 | Lint | 0 FAIL, 2 WARN over 5 files, byte-identical to the pre-ship's | out/lint-diagonalization.txt |
| 6 | Statement, `hmain`, regions | `hmain` is quoted exactly (file 405–407). The target is at 402, the home at the blank line 375, the `sorry` at 410 and the status paragraph at 399–401: all right. **Stale:** the docstring 248–269/273, the header 14–69, E-D's region "275 to the end" and the base size 361/0 private (F1) | file, below |

## (b) The route's mathematics and feasibility

**Verdict on the plan: sound and sufficient.** I re-read the hosts:
- the clock's two clauses;
- the install and input calls (each with only a positive cut);
- the release adapter, the input seek and the conditional;
- `Round`/`Segment`/`iterate_seq` and the phase host (its redirects allow the loop's back-edge);
- R1's transports, the expansion, `copyMapTM`, `writeAdvTM`, the scan fold and the emitter;
- `timeConstructible_iff`.

Each route step has a published row:
- **The capped locator from `ℓ₀ = 2`.** Every round is at a rung `ℓ < n`, so `a ≤ n` holds and
  the timeout certificate applies. The first round needs `n ≥ 3`, which is the setup's fold.
  A `next` keeps `ladder f (h + 1) < n`.
- **The decision.**
  - `X > L` gives `L < X⁴`.
  - Otherwise the twice-cut square `min (min (X²) K²) K` with `K = L + 2` compares with `L`
    exactly as `X⁴` does, and at the top the inner cut square is `X² = budget f ℓ`.
  - The power-of-two fold on `bits n` decides `n = 2^L`.
- **The ledger.**
  - Passed rounds cost `O(ℓ_{h+1} + (L + 1)²)`: the call's bound with `f a < X ≤ ℓ_{h+1}`
    (`qy_round_le`), the clock's `5τ + 2m + 2`, the counter rewrite and the expansions.
  - The stopping round costs `O(n + (L + 1)²)`: the clock's `5(2^m − 1) + 2m + 2` with
    `2^m ≤ (2n + 1)(2D₀ + 1)`.
  - The post-loop phases are `O(g n + 1)`: L5's `(h + 1)³ ≤ 8n`.
- **The writer's word.** It is `query_eq`'s word, through `pairEncode_eq` twice.

**What I proved, sealed** (`probe/EQC1ReviewProbe.lean`; 0 diagnostics; 33 axiom prints on the
standard three; out/EQC1ReviewProbe.out). It re-proves the pre-ship's 15 route lemmas (without
`qy_guard`) and the first review's 6 in one section. Its seal covers 20 definitions:
- the pre-ship's 12;
- `clockCfg`, `wordPatch`, `FinTM.bufferTape`;
- the owned file's `query`, `budget`, `stageCode`, `stage`, `ladder`.

The 8 new controls close unsealed and fail sealed (out/EQC1ReviewSealControl.out: 8 errors, all
in the sealed section). The new lemmas:
- **`qy_clocked_call`** (the first-arrival cut, the riskiest step). The clock is
  `exists_stepClockTMVia (Function.Embedding.refl Bool) (seamReleaseTM C.tm entry)` with
  `stopAt s := decide (s = Sum.inr exit)` and an all-ones counter of width `m`. From the call's
  published clauses alone:
  - if the exit time `t ≤ 2^m − 1`, the host reaches `finish (some (Sum.inr exit))` at
    `T ≤ 5t + 2m + 2`, with the call's endpoint right-tagged and the counter
    `wordPatch ct cp w'` (`|w'| = m`);
  - otherwise the host reaches some `timeout r` at `T ≤ 5(2^m − 1) + 2m + 2` with empty output;
  - in both cases there is no exit earlier, and no `entry ≠ exit` is used.
- **`qy_timeout_cert`**: a timeout forces `n < f a`, from `qy_call_bound` and `qy_ones_ge`.
- **`qy_rounds_spec`, `qy_stage_of_run`** (the stop rule in the machine's form). For
  `s = stage f n`:
  - every rung `≤ s` is below `n`, the decision is `next` below `s` and not `next` at `s`, and
    it is `top` exactly at the top;
  - conversely, a run that passes `0..s−1` and stops at `s` has `s = stage f n`.
- **`qyCut`, `qy_cut_spec`, `qyMachineDecide`, `qy_machineDecide_eq`, `qy_top_budget`.** The
  machine's decision equals `qyDecide`. It is built from the binary compare `n < f a`, the unary
  compare `L < X`, the cutoff product against `L` with `L = |bits n| − 1`, and the fold's verdict
  on `bits n`. At the top the cut square is `budget f ℓ`.
- **`qy_poly_log_le`, `qy_loop_ledger`, `qy_main_bound`.** With passed rounds
  `≤ A₁ (ℓ_{r+1} + (L + 1)²)` and the last `≤ A₂ (n + (L + 1)²)`, the loop is within
  `(10 A₁ + 9 A₂)(n + 1)`. The phases then absorb into `(B₁ + B₂)(g n + 1)` by `n ≤ g n`.
- **`qy_writer_word`**: the emission order for both branches, in `L6`'s terms. The budget is
  quadrupled. Then come `[F,F,T,T]`, `(bits ((unpair i).1 + 1)).dropLast` doubled and `[F,T]`.
  The tail is `1^{ℓ+1}`, or `1ⁿ ++ [true]`, the expansion's block plus one cell.

**The licensed leaves are provable from published rows**, and nothing escalates:
- **L2.** A lockstep along `bits n` (`walkTM` carries the other head), a one-cell read, then a
  top-down compare. This is a small own-file finite-state leaf within `O(|bits n| + 1)`, with
  its run proved through `step_of_some` and the `Action.apply_*` equations (now in the probe).
- **L3.** The unary compare is the walk plus a read. The cutoff product is rounds of a copy,
  stopping at `K`. It needs an iteration host: F11.
- **L5.** `Nat.unpair` in unary from `h`: search `s` with `(s + 1)² > h` by L3, then a subtract
  and a compare. `O((h + 1)³)`, iterated like L3.
- **L6.** A tape-word emitter writing each bit `r` times, optionally dropping the last symbol,
  plus fixed words over `emitAction`.
- No published machine-level form exists for any of the four (section (d)).

**The checkpoint plan (2–7) is sensible** for a Claude agent:
- the leaves are independent and can be built first;
- checkpoint 3 is the largest;
- 5 and 6 depend only on 4's escape;
- the plan becomes stateable at checkpoint 3 if the locator is its own phase-host machine (F16).

The size estimate (2.4–3.9k lines) stands. **The measured budget is a 9-CPU host's.** On a host
like the last Claude fill host it is 2–3× slower (F8).

## (c) Rule 10 (the 2026-10-23 scope)

**`hmain` can be proved reading other files' TCSlib definitions only through published lemmas.**
Every definition the route reads has a reading, and all are in the extended probe (216 names,
0 errors; out/EQImportProbeExt.out):

| Definition | Its published reading |
|---|---|
| `TimeConstructible` | `timeConstructible_iff` |
| `ComputesFunInTime`/`ComputesInTime` | their `_iff`s |
| `Cfg.ofWords`, `stateWord` | their field equations |
| `Cfg.mapState` | `_state`/`_inputPos`/`_workTapes`/`_workTapePos`/`_output` |
| `clockCfg` | its simps fields |
| `wordPatch` | `_of_mem`/`_of_not_mem`/`_append` |
| `counterLoopCfg` | `counter_cfg_eq` |
| R1's `embedEmitCfg`/`embedSilentCfg` | simps `state`/`inputPos`/`output`, `_selected_tape`/`_pos`, `_unselected`, `_cap`, `embedEmitCfg_eq` |
| `seamReleaseTM` | `_runFrom_pos` |
| the phase host | `phaseHostTM_q₀`/`_run`/`_run_le` |
| `pairEncode` | `pairEncode_eq` |
| `FinTM.bufferTape` | `bufferTape_eq`/`_append*` |
| `Cfg.Stopped` | `stopped_iff` |
| a machine's start | `initCfg_ofWords`, `initCfg_with_q₀` |
| own leaves | `MultiTapeTM.step_of_some`, `Action.apply_*` |

- **No needed fact lacks a published lemma**, so the brief needs no further license.
- **Gaps in the brief's text** (F10):
  - the brief names neither `wordPatch` nor the R1 transports' equations;
  - its seal list omits `wordPatch` and `embedSilentCfg`;
  - it should say how an own leaf's `step` unfolding is classified;
  - a `private inductive … deriving DecidableEq` gets a public instance name.
- **The probe's own proofs.** Every `rw`/`simp only` argument in the new lemmas is a theorem or a
  local. The `rfl`s reduce only core terms (`Option.map Sum.inr (some e)`). The owned file's
  definitions are sealed too and read through their laws.

## (d) Duplication

- **Population against the citations** (`scripts/citedfiles.py`, out/cited-files-vs-population.txt).
  The 30 files cover every cited row's file but two: `TuringMachine/Configuration` (`Action.apply_*`)
  and `TuringMachine/Deterministic` (`step_of_some`, `runFrom_*`). The leaves' run lemmas cite
  both (F13). Other "OUT" lines in that file are name collisions of the approximate mapping.
- **Semantic search, by text** (out/dup-search.txt; the tree, #172's head, `origin/main`):
  - no machine-level `unpair`, unary product or minimum, binary or unary compare, or
    doubled/quadrupled emitter;
  - `ClassP/BinaryArith` (`origin/main` only) has the polynomial-time `le`/`lt` (`AddSub`) and
    `mulU` (`Loops`), as `PolyTimeComputable`: not citable here, and different in form;
  - `PolyTimePairing.polyTimeComputable_lenLe` is likewise polynomial-time and function-level;
  - `Programs/Light/Lib/Logs.cbrtLeast_pow_le` is a different statement.
- **Semantic search, by `exact?`** (out/EQC1ReviewDupProbe.out). The new statements: 4 of 5
  "could not close". The fifth, the expansion's block, is **`List.flatten_replicate_singleton`**
  (cite it).
- **Hazards.**
  - The `qy_guard` copy hazard is handled by the draft.
  - The idiom example now *is* a published lemma (F6).
  - The first round's guard pairs are gone (the pre-ship's pair diff).
- **#172's `NTimeHierarchy`** (a population member) gains 10 `nh_` and `un_` privates. None
  restates a cont1 step; `nh_stage` is a two-line corollary of `stageCode_frequently`.

## (e) Consistency and the agent

Hosts, rules, checkpoints, the checklist and the environment agree with the route and with
addendum v2.6 except for the following:
- **Stale since checkpoint 1's landing.**
  - The line ranges and sizes (F1).
  - "Nine imports"; the file has twelve (F3).
  - L1 is still a licensed leaf, and the "L1–L6"/"L1–L4"/"L1–L3" lists remain (F9).
  - Checkpoint 7 and "`C`, term by term" still describe the landed conditional (F15).
  - Rule 11's "unused in the tree".
- **Stale since #170/#171.**
  - `exists_uniformSimulator` is still listed out of scope (F5).
  - The idiom example (F6).
  - The import probe lacks the word tests the brief tells the agent to use (F7).
- **Codex and megafill remnants.**
  - The megafill banner is gone, but no single-fill line replaces it (F12).
  - The budget is the Codex host's (F8).
  - "Quote both outputs" ignores the cp1 review's F8 (F14).
  - No cover-brief or queue rule is left.

## (f) In flight: the in-flight line and the lists at issue

Gate 83 has passed, so #173 can merge. Gate 84 passed for #172. cont1 issues only after #173
merges, so two cases remain at issue.
- **#172 merged before issue** (in either order with #173). The issue tree is both PRs' merge.
  #172 changes only `NTimeHierarchy`, adding imports of `NTimeDiagonalizer` and `ChoiceWords`
  and no Mathlib root.
  - Re-take, at the issue commit, against the merged-tree replay's snapshot (never composed):
    - the order list: still 84 modules, re-sorted so that `NTimeHierarchy` follows
      `NTimeDiagonalizer`;
    - the base sorry set: **20 in 9 modules**, without `ntime_hierarchy`;
    - the screen base: `NTimeHierarchy` changed, and with F13 the population changes anyway;
    - the base file's elaboration.
  - The roots (34), the blob, the line numbers, every probe (none imports `NTimeHierarchy`) and
    the lint counts are unchanged. I linted with #172's file: 0 FAIL, 2 WARN over 5 files;
    only its WARN line's count changes, 1,793 → 1,940 (out/lint-diagonalization-with-172.txt).
  - Text:
    - in-flight: "none: no open PR touches your order list";
    - drop `ntime_hierarchy` from the out-of-scope list;
    - "Parallel batches": `ntime_hierarchy` is proved (#172, merged), and its file imports yours,
      citing only statements;
    - the tail from your module on is now `NTimeDiagonalizer`, `NTimeHierarchy` and the facade.
      `NTimeHierarchy` takes 6.2 s and 1.8 GB here (out/NTimeHierarchyAt172.out), so the tail
      takes seconds, not "about 5 s" alone.
- **#172 still open at issue.** The lists stay as measured. The in-flight text:
  > #172 (H's landing): `Diagonalization/NTimeHierarchy.lean` only. It will import your file
  > and `TuringMachine/ChoiceWords`, and it cites only your file's public statements
  > (`exists_diagonalizer`, `acceptLang_mem_NTIME`, the ladder and stage laws). It is in your
  > order list and screen population; after it merges, your landing replays it downstream. Cite
  > nothing it adds.

  #172's `NTimeHierarchy` elaborates on cont1's base tree with no diagnostic (6.2 s), so the
  two PRs do not conflict.

## Findings

| # | Severity | Location | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **major** | "What this is" (97–98); "Owned regions" (221–223); rule 8 (432) | The binding freeze text still carries the first round's lines. Taken literally, **"E-D's region, 275 to the end"** freezes the agent's home (375), its body (410) and region (d) (399). The header is 23–78, not 14–69. The target's docstring is 376–401 and its statement 402–404, not 248–273. Rule 8's base is 498 lines with 22 public and 3 private declarations, not 361 with 0 private. The quoted statement also shows `:= by sorry`, while the body is the landed `suffices` | file (`grep -n`, above); line 81 of the draft itself says 498 | The diff: the right ranges and the quoted body |
| F2 | **major** | Hosts, "The clock" (228–229) | `exists_stepClockTM`, offered as an equivalent, leaves the counter tape after either exit **arbitrary** (`∃ ct'`) and has no frame clause. The next round's clock needs the counter delimited, blank at `cp − 1` and `cp + m`. That can no longer be shown, so the loop is unprovable along that route. The joint form's `wordPatch ct cp (w'.map e)` with `|w'| = m` keeps every other cell, and its frame clause gives the counter head's interval | `StepClock.lean` 1096–1180; `qy_clocked_call` (sealed) | The diff: require `exists_stepClockTMVia` at `e := refl`, and say why not the `Bool` instance |
| F3 | minor | 82, 207–208, rule 6 | "The nine imports … exactly the nine": the file has **twelve** import lines (6–17), the original three plus E-Q's nine. An agent counting them meets a contradiction in a binding rule | file 6–17 | The diff |
| F4 | note | 84 (⟨IN-FLIGHT⟩), lists | An issue-time item that depends on #172's merge order | section (f) | The texts in (f) |
| F5 | minor | "Out-of-scope sorries" (614) | Lists `exists_uniformSimulator` (`CodeSimulator`), which #170 proved. It is not in the base set the agent must compare by name | `base-sorries.txt`; out/01 census | The diff: drop it (and `ntime_hierarchy` too if #172 has merged) |
| F6 | minor | Duplication, the idiom example (549–552) | The example idiom, `computesFunInTime_ifEq w [true] [false]` with the `[decide (x = w)]` conversion, **is** `computesFunInTime_decideEq` since #171. Writing it would be a re-derivation of a published lemma, which the brief's own rule sends to "cite the lemma", not an idiom | out/EQImportProbeExt.out (its type) | The diff: a still-valid example (`Cfg.mapState_mapState`), and the #171 note |
| F7 | minor | Pre-ship (149–153), "Cited infrastructure" (408–414) | The brief says every cited name is in `EQImportProbe` and tells the agent to use `computesFunInTime_decideEq`/`_allTrue`. The probe has neither, nor the R1 transports' field equations, `wordPatch_append`, `step_of_some`, `Action.apply_*`, `exists_emitCallTM` or `Round.of_cut`. Its header still describes the first round's overlay and drafting base | out/EQImportProbeExt.out: **216/216, 0 errors** | Stage `review-inputs/EQImportProbe.lean.txt`; the diff's counts |
| F8 | minor | Budget (588–591) | The figures are the 9-CPU Codex host's. The last Claude fill host (G4 cont4, `nproc` 4) took 22 min for a 96-module bootstrap. It took 11 min 47 s for an 847-declaration screen that the maintainer's host ran in about 5. At that ratio this brief's 1,735-declaration screen is about 45 min, and the "25 minutes" finishing reserve is too short | `s13d/reviews/g4-cont4/REVIEW.md` §(f); `g4-cont4-REPORT.md` 418; `s13d-fill-g4-cont4.md` 507 | The diff: both hosts' figures and a one-hour reserve |
| F9 | minor | Leaves (262–266), rules 7 and 10, the checklist, hazards, gate guidance, hosts ("guard split") | L1 is still licensed as a leaf to write, with the first round's rows, although `qy_guard_decider` is landed through the word tests. The "L1–L6", "L1–L4" and "L1–L3" lists invite a second guard decider and count L4, which is a scan fold, not a leaf | file 268–339 | The diff: L1 landed, "L2, L3, L5, L6" |
| F10 | minor | Rule 10 (436–480), rule 11 (485) | The rule-10 readings omit `wordPatch` (`_of_mem`/`_of_not_mem`/`_append`) and the R1 transports' equations. The seal list omits `wordPatch` and `embedSilentCfg`. The rule allows own leaves to unfold `step`/`Action.apply` but does not say how the inspection table classifies that. A copied `private inductive QyStep … deriving DecidableEq` gets the public name `instDecidableEqQyStep` (`workflow.md` §4). Rule 11's "unused in the tree at the drafting base" is stale: the three landed privates use `qy_` | `Embed.lean` 983–1051; `StepClock.lean` 88–130; `workflow.md` §4 | The diff |
| F11 | minor | Leaves L3, L5 (271–279) | Both are loops (L3's product, L5's search), but the brief names no iteration host. "A finite-state scan or a fixed composition of the rows" does not cover a loop, and `policy.md`'s review checklist item 8 forbids a private loop driver | `policy.md` 236–253 | The diff: rounds of `Round.iterate_seq`, or the counter loop |
| F12 | minor | Head of the brief | The megafill banner was removed with no single-fill line in its place. Part 1, item 2 defines "a Lean process" by Part 3, item 5, a megafill part. The model standalone brief (G4 cont4) opens with "A single fill (… Part 3 does not apply)" | `s13d-fill-g4-cont4.md` 3–4; addendum Part 1 item 2, Part 3 | The diff: a single-fill line that names Part 3's items 5 and 7 as restated |
| F13 | minor | Population (519–532) | The memory rule says a population covers every cited file. The brief's rule 10 sends the leaves to the machine model's step and action equations, which live in `TuringMachine/Configuration` and `TuringMachine/Deterministic` (278 and 535 lines); both are outside the 30 | out/cited-files-vs-population.txt | Add both (32 files, `review-inputs/screen-population.txt`); re-measure the screen base at issue, which #172's merge forces anyway; ⟨N/P/C/T/M⟩ in the diff |
| F14 | minor | Duplication (573–574); checkpoint zips (73–75) | "Quote both outputs in `REPORT.md`" repeats what the cp1 review's F8 asked to change: the screen outputs made the first REPORT 564 KB. The other F8 point is missing too: a cp zip's logs must be finished runs, or marked partial | `reviews/fill-cp1/REVIEW.md` F8, "The continuation" | The diff |
| F15 | minor | "Where it stands" (128–129); checkpoint 7 (385–388); the checklist's "`C`, term by term" | These still describe the conditional and `qy_guard` assembly that `qy_query_of_main` landed. "`n ≤ g n` is already absorbed" can be misread: `M₁`'s own `O(n)` phases still need `n ≤ g n` inside `hmain` | file 341–374, 405–410 | The diff: checkpoint 7 proves `hmain` with `A = B₁ + B₂` (`qy_main_bound`) |
| F16 | note | Checkpoint 3 | A `Turing.Round` is stated on one machine with an anchor, and `M₁` exists only at checkpoint 7. Building the locator as its own phase host lets checkpoint 3 land alone | `Contract/Basic` 685–700 | The diff (one sentence) |
| F17 | note | Pre-ship (154) | "16 lemmas, 14 of them axiom-printed": all 16 are printed since the first review | out/EQRouteProbe.out | The diff |
| F18 | note | Pre-ship; inputs | `qy_clocked_call`, the stop rule's machine form, the cutoff decision, the ledger and the writer order are proved and sealed here. Handing them over removes the brief's riskiest unprobed steps | out/EQC1ReviewProbe.out, out/EQC1ReviewSealControl.out | Stage `review-inputs/EQC1Review*.lean.txt` and cite them (decision 3) |

## Decisions for the user

1. **When to issue, against #172.**
   - **(a) Merge #172 and #173, both gated, then take the pre-ship once at the merged tree:** the
     order list re-sorted, 20 sorries in 9 modules, a new screen base and the base file on the
     merged-tree replay. The in-flight line is then "none". **Recommended:** one re-take at the
     final tree, no in-flight caveat, and F13's population change needs a new screen base
     anyway.
   - (b) Issue with #172 in flight: the lists as measured, plus (f)'s in-flight text. cont1's
     landing then replays `NTimeHierarchy` downstream.
2. **The population (F13).**
   - **(a) 32 files, with `Configuration` and `Deterministic`.** **Recommended**: the memory rule,
     and the leaves cite them.
   - (b) Keep 30 and record the two as not screened.
3. **The cont1 review's probes as inputs (F18).**
   - **(a) Stage `review-inputs/` (the 216-name import probe, `EQC1ReviewProbe` with its controls
     and its duplication probe) and keep the diff's pre-ship bullet.** **Recommended**: the
     clocked call is the step most likely to cost an agent a stop, and the probe proves it from
     published clauses.
   - (b) Leave them as review evidence only; drop the bullet and the "216" counts from the diff.

The agent is Claude (the user's ruling); no decision there.

## Files

- `REVIEW.md` (this file); `suggested-fix.diff`, which applies with `git apply` from the
  repository root at `c6c81b2b`. It holds:
  - 37 asserted replacements in the draft (`scripts/apply_fixes.py`);
  - five new files under `campaign/fills/eq/drafts/eq-fill-query-cont1/review-inputs/`: the
    216-name import probe, `EQC1ReviewProbe`, `EQC1ReviewSealControl`, `EQC1ReviewDupProbe` and
    the 32-file population.
  - The applied result is byte-equal to `edited/` and to the elaborated probe files.
- `orig/`, `edited/`: the draft before and after.
- `probe/`: every Lean file I ran, which are copies of `wt/rvprobe/`:
  - the pre-ship's nine;
  - `EQC1ReviewProbe`, `EQC1ReviewSealControl`, `EQC1ReviewDupProbe`, `EQImportProbeExt`;
  - `NTimeHierarchyAt172` (#172's file, elaborated on cont1's base);
  - the population file.
- `out/`: each run's `.raw`, `.out` and `.time`, plus:
  - `00-preship-compare.txt`, `01-review-runs.txt`, `order-check.txt`;
  - both lint outputs, `cited-files-vs-population.txt` and `dup-search.txt`;
  - `NTimeHierarchy-at-172.lean`.
- `scripts/`:
  - `elab.sh` (the `leanelab.sh` wrapper) and `norm.py` (output comparison);
  - `closure.py`, `names.py`, `citedfiles.py` and `extract.py` (probe assembly);
  - `new-lemmas.lean.txt` and `apply_fixes.py`.
- `wt/`: the review worktree, left in place; only `rvprobe/` is untracked there.
