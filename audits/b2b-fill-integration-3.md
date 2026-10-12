# B2b fill, delivery 3 (complete; both targets admission-free): integration record

Brief: `briefs/ch34-b2b-cont2.md` (ancestor `d71c389a`). Delivery:
`infra_local/fill-ch34-b2b-cont2.zip`, agent commit `a5486974` on base `d0b7761f`. The agent's
report is `audits/b2b-fill-agent-reports/fill-3-REPORT.md`. The earlier records are
`audits/b2b-fill-integration.md` and `audits/b2b-fill-integration-2.md`. The patch was applied
at the campaign tip `d0b7761f` as `2041510e`.

## Result

**Complete: 2/2.** `Complexity.NP_subset_PSPACE` and `Complexity.SAT3_mem_PSPACE` are proved
and admission-free ([AB09, Example 4.6]). There is no escalation and no modulo dependency.

- **Discharged:** the one admitted private helper, `b2b_search_contract`. Its statement is
  unchanged.
- **One shared trial contract**, `b2b_trial_run`, serves every counted round and the final
  certificate. It composes:
  - the identity capture;
  - the native rewind;
  - the framed append copy (`copyTM_run_ofCfg`, `b2b_buffer_concat`);
  - the captured virtual verifier call;
  - the verdict reader.

  The phases are joined through `phaseHostTM_run`.
- **The loop.** One round contract (`b2b_round_run`) adds the rejecting suffix: clear the
  buffer, then increment. The search instantiates `counterLoopTM_run_escape` at the least
  accepting counted index, or `counterLoopTM_run_done` followed by the final trial. The round
  durations are chosen classically and made a function of the configuration by injectivity of
  the certificate configurations (`ctrVal_enumWord`).
- **Space.** The public counter-loop trajectory clauses reduce every body-head position to one
  round's. This gives a fixed radius `n + Q + cV·((n + Q)^e + 1) + cI + 1`, with no factor
  counting trials. The host contract's interval-to-cardinality packaging and the ledger are
  unchanged.

There are 11 new private declarations: one pure configuration definition (`b2b_trialCfg`) and
ten theorems. There is no new machine, public declaration or import. The module's `Main
results` tag now reads "proved" (authorized status update).

## Verification (maintainer)

- **Integrity.** All 25 `SHA256SUMS` entries are OK. The zip has no C file and no script; the
  agent's sandbox `readlink` shim is described in its report and is not in the delivery.
- **Integration.** `git am -3` applied cleanly, keeping the agent's authorship. The file
  matches the delivered snapshot byte for byte.
- **Freeze** (`audits/logs/b2b-fill-3-freeze.log`).
  - No public was added or removed, and no public statement or body changed.
  - The only changed existing declaration is the private `b2b_search_contract`. The diff
    inside it removes only its `sorry`, so its statement is unchanged.
  - 11 privates added; imports unchanged (7). No `sorry`, `axiom` or unsafe token among the
    added lines.
  - The only other removed line is the module's status tag.
- **Status refresh** (`6da48293`, maintainer, comment-only). The freeze kept two private
  docstrings describing a continuation frontier: `b2b_search_contract`'s and
  `b2b_host_contract`'s ("… remain open"). Both now say "Status: proved" and name the proving
  lemmas. The comment-stripped code is identical to the delivered file.
- **Duplication** (`…-screen-after.txt`; base: the brief's population at the tip).
  - Byte-identical to the agent's before and after runs: 854 → 865 screened declarations,
    **634 → 635 pairs**, 177,277 → 177,396 characters.
  - One new pair, in-file: `b2b_trialCfg` ← `b2b_setupCfg` (65%). These are two different pure
    configuration records that share `Cfg.init`/`bufferTape` notation, and the report justifies
    the pair.
  - No cross-file pair. **New copies: none.**
- **Lint** (`…-stylelint.log`): 0 FAIL, 2 WARN over `SpaceComplexity`, both size warnings.
- **Size:** `Inclusions.lean` 1,538 → 2,880 lines (4 public / 64 private). Ground rule 8 sets
  no cap, and file size alone is not a driver (user, 2026-10-11).
- **Replay** (`…-replay.log`, user-run): 4 modules at `6da48293` into a tip-consistent
  snapshot. **0 errors.** 4 sorry warnings, all `TQBF`'s; **`Inclusions` 0**.
- **Combined tree** (`audits/logs/fills-3-combined-replay.log`, user-run). This delivery was
  built without PR #38's generalized `CounterLoop`, which its search cites. The replay checked
  `integrate/fills-3`: the tip with PRs #38 and #43 and both fill integrations. It covered
  13 modules, the downstream closure of `CounterLoop`, `CfgRecord` and `Inclusions`. **0 errors**;
  `Inclusions` 0 sorry warnings.
- **Axioms and admission walk** (`…-axioms.log`; probe
  `audits/evidence/b2b/B2bFill3Axioms.lean.txt`), on both the per-fill and the combined tree,
  with identical output.
  - All four `Inclusions` publics print within `[propext, Classical.choice, Quot.sound]`.
  - The walk from both targets finds no `sorryAx` source.
  - A census of all 474 private constants of `Inclusions` finds none that uses `sorryAx`.
  - The agent's 15 prints agree.

## Disposition

The fill is complete and goes in by PR. **The B2b fill gate is now due:**
- its pack `audits/b2b-fill-pack.md` and bundle are in the same PR;
- it covers all three deliveries.
