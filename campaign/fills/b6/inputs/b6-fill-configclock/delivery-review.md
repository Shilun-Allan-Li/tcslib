# Review — B6 F3 (`Turing.exists_configWindowRunnerTM`), delivery `fill-b6-configclock.zip`

**Verdict: NEEDS MAINTAINER DECISION.** This is a clean partial, 0/1 targets filled. It adds five
private arithmetic lemmas and a flagged appendix, and every integrity, freeze, hygiene,
elaboration, probe, lint and screen check passes at the current tip. The target stays open
because of escalation E1, and I confirm E1 is real: the brief contradicts itself. Ground rule 10
forbids unfolding any definition in `Build/CfgRecord` or `Build/RecordTable`. But the prescribed
route and the maintainer's recommended clock-writer stub need tape-cell access from a
`RecordAt d 0 fs` hypothesis, and no public eliminator for `RecordAt` exists at the pin
(checked). The maintainer must rule before a continuation can proceed. Integrating the partial
is mechanically safe, but its appendix text and the hypothesis shapes of the `cw_` lemmas depend
on that ruling (see "Integration notes").

Review conditions:
- Campaign tip at review: `67c2c56cdfcd6ed550f2fd9cca1338953ff9583e`. It is one backlog-only
  commit after the commissioned `0f643174`; `git diff --name-only 0f643174 67c2c56c` lists only
  `backlog.md`. Its Lean content equals `e5fcd8ee` (0 `.lean` files differ).
- During the review the tip moved again, to `8b383e0b` (H2-F inputs, backlog). That move also
  changed no `.lean` file, so every result below holds at it.
- Olean snapshot: `oleans-lwalk`.
- Worktrees (detached): `review/f3/wt-tip` (tip as is), `review/f3/wt-tipd` (tip plus the
  delivered file), `review/f3/wt-base` (`8420da14`, used for patch application and then reset).

## Checks

| # | Check | Result | Key output |
|---|---|---|---|
| 1 | Zip SHA-256 | PASS | `737087199358da82bb22513423f2aff29bf7e551ce3207705e75eb7cdab0d8bd`, as commissioned |
| 2 | Extraction | PASS | new empty dir `review/f3/x`; 48 files, no symlinks, no path escapes |
| 3 | Delivery `SHA256SUMS` | PASS | 47/47 OK; covers every file except itself |
| 4 | Authorized shim | PASS | `evidence/runtime/executable-path.c` = `985924ad…4fba7`; not compiled or run. `lean-env.sh` and `scripts/compare-sorries.py` were also not run. No other C files |
| 5 | Brief and dispatch | PASS | tip `briefs/b6-fill-configclock.md` with `@ANCESTOR@`→`8420da14…` is byte-equal to the dispatch (`6bf925d1…2980`) and to the zip copy; the addendum is byte-equal |
| 6 | Base and ancestor | PASS | REPORT base `8420da149ad2df8b62cfde91069a249649fda6c6`; the worker's observed tip `9ff6b094` (the F3 brief commit) is an ancestor of the campaign tip |
| 7 | Bundle | PASS | `git bundle verify` okay; sole prerequisite `8420da14`; ref `fill/b6-configclock` = `2240b69e14bedfdb7ac6cabaee3aceddd5830fb7`, parent `8420da14`, tree `4f3c3327…` (equals REPORT); fetched only into a scratch repo with alternates |
| 8 | Format-patch series | PASS | the one patch applies at the base (`git apply --check`); the result is byte-equal to the delivered file and to the bundle commit's file; only `WindowClock.lean` changes |
| 9 | Ownership (diff vs base) | PASS | two hunks: `143a144,224` (home, 81 lines) and `186c267,279` (docstring's last line → original text minus ` -/`, then an appended "**Fill appendix (B6-F3, partial).**" paragraph, then ` -/`). Removing both inserts recovers the base byte for byte. Target statement and body (base 187–219 = delivered 280–312) are byte-identical |
| 10 | Freeze (`declfreeze.py`) | PASS | `public before/after: 4 4`, no public added or removed; `exists_configWindowRunnerTM` body/docstring change only (the appendix; statement unchanged); private added: `cw_budget, cw_head_bound, cw_round_cost, cw_time_bound, cw_true_value` |
| 11 | Hygiene of 94 added lines | PASS | no `#eval`, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `syntax`/`macro`/`elab`, `axiom`, `admit`, `sorry`, `set_option`, `open`/`section`/`variable`/`import`, attributes. Only `by decide` on numeral facts |
| 12 | Widths | PASS | new lines at most 90 characters; no line of the file exceeds 100 characters (max 96, pre-existing) |
| 13 | Rule 11 | PASS | no match for `copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`. No TCSlib declaration outside the file is cited (only core/Mathlib lemmas), so no private Catalog name |
| 14 | `cw_` prefix | PASS | all 5 new privates |
| 15 | WindowClock unchanged base→tip | PASS | 0 diff lines. Lean changes base→tip are `Build/Catalog` and `Build/Contract/Catalog` (#109). `declfreeze` on Catalog: no public statement changed, publics `walkTM`, `walkTM_run_ofCfg`, `skipTM_eq_walkTM` added, 4 proof bodies changed |
| 16 | Elaboration at tip, delivered file | PASS | `leanelab.sh wt-tipd oleans-lwalk …/WindowClock.lean`: exit 0, 0 errors, one warning `WindowClock.lean:280:8: declaration uses 'sorry'` (the target) |
| 17 | Elaboration at tip, tip's own file | baseline | exit 0, one warning `WindowClock.lean:187:8: declaration uses 'sorry'` |
| 18 | New warnings (`warndiff.py`) | PASS | `warnings base/new: 1 1`, `new warnings: 0`, `removed warnings: 0` |
| 19 | Axiom prints (`mkaxprobe` + 5 privates) | PASS (partial) | `FinTM.inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts`, `FinTM.configBound_le_two_pow`: `[propext, Classical.choice, Quot.sound]`; `exists_configWindowRunnerTM`: `[propext, sorryAx, Classical.choice, Quot.sound]` (its own `sorry`); `cw_true_value`, `cw_round_cost`: `[propext, Quot.sound]`; `cw_budget`, `cw_time_bound`, `cw_head_bound`: `[propext, Classical.choice, Quot.sound]`. Identical to REPORT |
| 20 | `F3ImportProbe` at tip (as is, tip olean) | PASS | exit 0, 0 errors, 0 warnings, 54/54 `#check` outputs |
| 21 | `F3ConsumerProbe` at tip (as is) | PASS | exit 0, 0 errors, 0 warnings |
| 22 | Probes on the delivered module | PASS | each probe body appended to a copy of the delivered module (import line dropped; module imports cover it): `F3ConsumerProbeAppended` exit 0, 0 errors, only the module's own sorry warning (line 280). The worker's `F3ImportProbeExpanded` (the 54 plus 20 core/Mathlib names) appended: exit 0, 0 errors, 74/74 outputs, the same single warning |
| 23 | Copy-text screen, before (tip) | done | script SHA `f4feac91…f878f181` verified; 21-file population byte-equal to the worker's; `declarations screened: 1022; copy pairs …: 500; reproduced text: 147,000 chars` (exit 0, 614 s) |
| 24 | Copy-text screen, after (tip + delivery) | PASS | `declarations screened: 1027; copy pairs …: 500; reproduced text: 147,000 chars` (exit 0, 599 s); `pairdiff after before`: `new at head 0; earlier-only 0` |
| 25 | Comparison with the worker's screens | consistent | worker (base): 1020/503/149,653 → 1025/503/149,653, 0 new. Mine (tip): 1022/500/147,000 → 1027/500/147,000. The 3-pair gap is #109's re-proof of `skipTM_run_ofCfg` through `walkTM`. Gone at tip: `skipBackTM_run_ofCfg`←`skipTM_run_ofCfg` 68%, `seekEndTM_run_ofCfg`←`skipTM_run_ofCfg` 60%, `seekStartTM_run_ofCfg`←`skipTM_run_ofCfg` 58%. No pair in either after-screen involves a delivered declaration |
| 26 | Downstream (graph2 at tip) | PASS | `downstream closure: 2 modules`; replay order `TCSlib/Complexity/SpaceComplexity/WindowClock`, `TCSlib/Complexity/SpaceComplexity`; import check PASS |
| 27 | Lint | PASS | `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity` in `wt-tipd`: `style_lint: 0 FAIL, 4 WARN over 107 files` (the 4 inherited size WARNs). Identical to the worker's `lint-final.log`; differs from the tip only in WindowClock's INFO line (312 lines; 4 public / 5 private) |
| 28 | Size | report | 219 → 312 lines; 4 public / 0 private → 4 public / 5 private |

## Delivered declarations (REPORT cross-checked against the diff)

All five are `private lemma`s in the home (delivered lines 144–223), use only core/Mathlib
lemmas, and none is used yet by the target.

| Declaration | Role (REPORT) | Diff check |
|---|---|---|
| `cw_true_value` | `ofDigits₂` of `W` trues is `2^W − 1` (the brief's pitfall lemma) | as reported |
| `cw_round_cost` | `L + n + 1 ≤ 2^(L+1)` from `p ≤ L`, `n + 2 ≤ 2^p` | as reported |
| `cw_budget` | `C·(B+1)·(L+n+1) ≤ 2^((C+q+8)·(k(2s+1)+p+2)) − 1`, given `L = k(2s+1)+p+k+4` and `n+2 ≤ 2^p` **as hypotheses** | as reported; the hypotheses stand in for `recordLength`'s formula and the `posWidth` bound |
| `cw_time_bound` | writer, runner, clear and dispatch costs ≤ `C_t · 2^(C_t(L+1))` | as reported |
| `cw_head_bound` | `C(L+W+1) ≤ C(c+1)(L+1)` for `W ≤ cL` | as reported |

There is no machine, no one-cell leaf and no clock writer. The target body is the original
`sorry`. Phase reached: none (phase 1, the clock writer, is not reached).

## E1 assessment (the decision the maintainer must make)

What I verified at the base `8420da14`:
- `RecordAt` is a `def … : Prop := ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (pos + p) =
  fieldsTape fs p` (`Build/CfgRecord.lean:357`).
- No public declaration eliminates `RecordAt`. I scanned every public statement mentioning
  `RecordAt` (my own scan, `review/scripts/pubmentions.py`). It finds exactly the worker's
  12-entry inventory, at the base and still at the tip:
  - the def itself;
  - `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM`;
  - `TableAt.recordAt_take` (a producer from table hypotheses);
  - `exists_fieldsCopyTM`, `exists_tableAppendTM`, `exists_recordValidTM`,
    `exists_recordNextTM`;
  - `exists_windowLoopTM`, `exists_windowRunnerTM`;
  - the target.

  None of them gives cells from a `RecordAt` hypothesis.
- `recordLength` (`RecordTable.lean:153`) and `posWidth` (`CfgRecord.lean:142`) are plain defs.
  No public lemma states their formula or the bound `n + 2 ≤ 2^posWidth n`.
  - `binDigits_posWidth_succ` is public, but turning it into the bound needs `binDigits`'s
    length, which has no public lemma.
  - The bound exists only privately (`CfgRecord`'s `record_pos_lt`) and inside
    `configBound_le_two_pow`'s proof.
- The recommended stub (`audits/evidence/b6-fill-configclock/tools/home.lean.txt`) takes
  `RecordAt d 0 fs`, and its sketch drives `copyMapTM_run_ofCfg` and `skipTM_run_ofCfg`, which
  are stated on cells. Proving it therefore needs `RecordAt` unfolded or a public eliminator.
  Rule 10's only named exception is `phaseHostTM`'s table.

So E1 is a genuine contradiction inside the brief, not a worker error. The worker's strict
reading has two counterweights:
- F2's own `Build/WindowRun.lean` proofs unfold `RecordAt` (e.g. `intro p hlo hhi` on a
  `RecordAt` goal).
- The frozen, landed `FinTM.configBound_le_two_pow` in this same file closes
  `n + 2 ≤ 2 ^ posWidth n` by definitional unfolding of `posWidth`
  (`rw [← Nat.size_eq_bits_len] at h; exact h`).
- The brief itself lists `recordLength k n s = k(2s+1) + posWidth n + k + 4` as a fact to use.

**Options for the ruling:**
- (a) Authorize, for WindowClock, unfolding the specification-level defs `RecordAt`,
  `recordLength` and `posWidth`. These are Prop and arithmetic definitions, not machine
  implementations.
- (b) Land a small public API before the continuation, as the worker requests:
  - a `RecordAt` iff/eliminator;
  - `recordLength_eq` (true by `rfl`);
  - a public `n + 2 ≤ 2 ^ posWidth n` (promote `record_pos_lt`).

  This needs edits to `Build/CfgRecord` and `Build/RecordTable`, so a PR and a replay of their
  downstream.

The worker also flags state transport of `RecordAt` across control types as the same gap. Under
(a), that is immediate.

## Discrepancies between REPORT.md and my measurements

- None of substance. Every hash, tree, line count, declaration count, axiom print, lint line
  and screen delta I could reproduce matches.
- Screen numbers differ only because I ran at the tip (after #109) and the worker at the base.
  The difference is explained in row 25, and the delta is zero in both.
- I could not reproduce the worker's 176-module bootstrap or final sweep (no `lake build`; only
  the owned file was elaborated). Its downstream closure at the tip is just the facade.
- REPORT says "Final file: 312 lines, 4 public / 5 private": confirmed.
- One observation, not a discrepancy: the five `cw_` lemmas are unused (dead) until the
  continuation, which Lean does not warn about.

## Duplication

- New pairs: **none** (`pairdiff`: new at head 0, both in my tip screens and in the worker's
  base screens). No new cross-file or in-file pair involves a `cw_` lemma.
- The one WindowClock pair at the tip is pre-existing and landed:
  `ConfigCount.lean::ComputesInTime.of_spaceUsed_le` reproduces
  `WindowClock.lean::FinTM.inWindow_of_spaceUsed_le` at 67%. Nothing to factor.
- "new copies: none" is confirmed.

## Integration notes

- Commit to cherry-pick: `2240b69e14bedfdb7ac6cabaee3aceddd5830fb7` (single commit on
  `8420da14`). It is in the bundle `fill-b6-configclock.bundle`; the format-patch
  `patches/0001-Add-B6-F3-clock-arithmetic-and-partial-fill-appendix.patch` is equivalent. It
  touches only `TCSlib/Complexity/SpaceComplexity/WindowClock.lean`, which is unchanged
  base→tip, so it applies to the tip without conflict.
- Replay list (graph2 at tip): `TCSlib/Complexity/SpaceComplexity/WindowClock`, then
  `TCSlib/Complexity/SpaceComplexity`.
- Status text:
  - The module header's status is unchanged and still accurate: the target is open.
  - If you rule (a) or (b), the appendix sentences "Rule 10 prevents extracting the field-cell
    hypothesis from `RecordAt` …; the pinned public contracts supply no eliminator" and "The
    numerical helpers keep … as explicit hypotheses for the same reason" become stale. Correct
    them at integration or in the continuation.
- Whether to integrate now: the partial adds no admission and no copy, but it is all
  arithmetic, and `cw_budget`'s hypothesis form may change after the ruling. Either option is
  defensible: integrate now and let the continuation discharge `hL`/`hn`, or hold until the
  continuation.
- The continuation brief should fix ground rule 10's text, or pre-land the API, and restate
  that the recommended writer stub may be used.
