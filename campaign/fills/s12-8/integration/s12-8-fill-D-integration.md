# §12.8 fill, stream D (R8.0b and R8.6): integration record

Brief: `briefs/s128-fill-D.md` (ancestor `182e6f44`). Delivery: `infra_local/fill-s128-D.zip`,
agent commit `b2b7ac5d` on base `37ab6091`. The agent's report is
`audits/s12-8-fill-agent-reports/D-REPORT.md`.

**This PR is held for the separate R8.0b audit gate.** The batch changes audited public
signatures, so under the brief's integration note (the §13d process rule) the user merges it
only after that gate closes. The gate's evidence set is in `audits/evidence/s12-8/r80b-fill/`.

## Result

**Complete.** The four tasks of the brief are done, with no admitted helper.

| Task | Declarations | Status |
|---|---|---|
| 1. Generalize in place (types only) | `counterLoopCfg`, `counterLoopOrbit`, `counterLoop_time_le` | bodies byte-identical; every call site unchanged |
| 2. The rich-body host | `lastEmb`, `counterLoopTMVia`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` | new, the brief's exact text; proved by the one round induction `counter_rounds` |
| 3. Re-derive the `Bool` contracts | `counterLoopTM_run_done`, `counterLoopTM_run_escape` | statements byte-identical; short re-derivations at `Function.Embedding.refl Bool` through Z5 `MultiTapeTM.runFrom_eq_of_agreeOn`, no induction |
| 4. R8.6 | `expandTM_run_ofCfg` | proved **modulo `writeAdvTM_run_ofCfg`** (stream B), as the brief allows |

`counter_cfg_eq`'s body now instantiates the generic private `counter_layout`, and the private
`counter_buffer_complement` takes disposition (i), a direct instance of
`FinTM.bufferTape_map`.

## Verification (maintainer)

- **Integrity.** All 44 `SHA256SUMS` entries are OK. The zip's C file
  (`evidence/lean-readlink.c`, an `LD_PRELOAD` shim for the agent's environment) is excluded:
  it was never compiled or run, and neither the patch nor any source references it. The
  agent's Python helpers (`declaration-freeze.py`, `screen-delta.py`, the copied
  `copy-text-screen.py`) were not run either, and are not committed.
- **Integration.** `git am -3` applied the one-patch series cleanly at the campaign tip
  `aed5b4ff` as `be1b7691`, keeping the agent's authorship. `CounterLoop.lean` is unchanged
  between the agent's base and the tip, and matches the delivered snapshot byte for byte.
- **Freeze** (`audits/logs/s12-8-fill-D-freeze.log`, the maintainer's own check).
  - Publics 27 → 31: the four additions of task 2, each checked against the brief's text.
  - The three `STATEMENT CHANGED` lines are task 1's type-only generalizations. Their bodies
    are byte-identical (comment-aware body comparison), as are `counterLoopTM`'s and
    `expandTM`'s.
  - Body changes exactly at the brief's four swaps: `counter_cfg_eq`,
    `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `expandTM_run_ofCfg`.
  - Privates 24 → 23: `counter_layout` and `counter_refl_agree` added; `counter_last_unselected`,
    `counter_patch_initial` and `counter_orbit_succ` removed (one-use, inlined); nine rewritten
    over a generic alphabet, matching the report's ledger.
  - One import added, `TCSlib.Complexity.TuringMachine.SymbolLift`, which the brief prescribes.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added lines.
- **Duplication** (`audits/logs/s12-8-fill-D-screen-after.txt`, base
  `audits/logs/s12-8-fill-D-screen-base.txt`). 539 → 543 declarations and 414 → 418 pairs.
  The four new pairs are all in-file, with no cross-file pair and none removed:
  - `counterLoopTMVia` ↔ `counterLoopTM`, 91% / 84%: **E1**, below.
  - `counterLoopTM_run_escape` ↔ `counterLoopTM_run_done`, 83% / 72%: the two required
    `Bool` re-derivations. Each applies Z5 to its own generic contract; they share transport
    setup, and neither reproduces a proof of the loop.
  - **New proof copies: none.**
- **Lint** (`audits/logs/s12-8-fill-D-stylelint.log`): 0 FAIL over `TuringMachine` (14 WARN)
  and over `TuringMachine/Build` (6 WARN), all size warnings.
- **Size.** `CounterLoop.lean` grows from 1,279 to 1,697 lines. Justification: the brief makes
  the generalization in place and forbids new files, and file size alone is not a driver (user,
  2026-10-11). The file stays whole until 12.2c's per-theme reorganization of `Build/`.
- **Replay** (`audits/logs/s12-8-fill-D-replay.log`). 6 modules, the downstream closure of
  `CounterLoop`, at `be1b7691` into a snapshot of a tip-consistent olean tree; the user ran it
  from the maintainer's command. **0 errors.** 11 sorry warnings: `CounterLoop` 0,
  `InputCall` 2, `CfgRecord` 5, `TQBF` 4, both facades 0.
- **Axioms** (`audits/logs/s12-8-fill-D-axioms.log`; probe
  `audits/evidence/s12-8/S128FillDAxioms.lean.txt`, every public declaration). Read-only
  against the replay's tree.
  - All 31 prints are within `[propext, Classical.choice, Quot.sound]`, except
    `expandTM_run_ofCfg`'s `sorryAx`.
  - They match the agent's after-log line for line, and the agent's base/after comparison
    shows the 28 existing lines unchanged.
- **Admission walk** (`audits/logs/s12-8-fill-D-admissions.log`). The only constant in
  `expandTM_run_ofCfg`'s dependency closure that mentions `sorryAx` is
  `writeAdvTM_run_ofCfg`. So R8.6 is proved modulo exactly the cited row, as reported.
  Stream B proves that row (PR for B+C), so R8.6 becomes admission-free once both are merged.
- **Instances** (`audits/logs/s12-8-fill-D-instances.log`). The agent's
  `R80bInstances.lean.txt` was re-run read-only by the maintainer: 0 errors, 0 warnings. It
  covers the five base statements verbatim, the brief's executed rich-alphabet instances, and
  R8.6 at a zero counter, an empty counter and an empty pattern. A control copy confirms the
  file is genuinely checked.

## Escalation E1 (for the R8.0b gate)

The brief requires both definitions verbatim:
- `counterLoopTMVia` is mandated new text;
- `counterLoopTM` is frozen.

Their screen pair is 91%, over the 90% copy line. Factoring the pair would break one of the
two text mandates, so the agent kept both and escalated, correctly. This is a definition pair
the brief itself prescribed, not copied proof: there is one round induction, and the `Bool`
contracts are derived from the generic ones.

**Proposed disposition:**
1. Authorize this one pair at the R8.0b gate.
2. Open a 12.2c follow-up: redefine `counterLoopTM` as the identity-embedding instance of
   `counterLoopTMVia`. That would remove the pair; the brief's freeze ruled it out here.

## Disposition

- The R8.0b gate pack follows. The user merges this PR after that gate closes.
- With stream B merged, R8.6 is admission-free; the post-merge sweep confirms it.
