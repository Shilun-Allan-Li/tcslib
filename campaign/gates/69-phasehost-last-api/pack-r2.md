# External audit pack — the phase host's last phase (PR #156, an API gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 1 minor, 8
notes. The major: six older proofs in four files re-derived the newly published prefix argument
(the agreement transfer, with the host's table read by unfolding `phaseHostTM` in another file).
**The user ruled (2026-10-23) to fix it in this PR.** The minor (the PR body's file count, the
lint record's revision) is a records fix, done.

**The head:** `lean/phasehost-last` at `0e5f210b`, one commit after round 1's head `a4d9b024`; its
Lean diff from `a4d9b024` is the five files below (`evidence/round1-fix/repoint.patch`). This
bundle's Lean files are from `0e5f210b`, and its records from the records commit that the dispatch
prompt names.

| File | Change since round 1 |
|---|---|
| `TuringMachine/Build/WindowRun` | `wr_prefix`: `phaseHostTM_run_le` at the clock phase (`Ph := wr_Ctrl Q`), the guard from `hcut` (the runner redirects only the timeouts); its sketch says so |
| `TuringMachine/Build/StepBlock` | `recordSkipTM_tail`: `phaseHostTM_run_le` at the walker phase, whose redirect is `none` (`rfl` on this file's `skipRed`); its docstring says so |
| `SpaceComplexity/Inclusions` | three `have`s: `b2b_trial_run`'s `hpz` (the test host's verdict phase), `b2b_round_run`'s `hprefix` (the body's test phase, with the existing `hguard`), `b2b_finish_answer`'s `hp` (the host's answer phase); each `phaseHostTM_run_le`, the guards `rfl` on this file's redirect tables or `hguard` |
| `TuringMachine/CodeSimulator` | `canonEmitVerdict`'s `leaf`: `phaseHostTM_run_le` at the emitting phase, its type stated, the guard `rfl` on the proof's own `red` |
| `TuringMachine/Build/OracleSim` | **found by the maintainer, not in round 1's list:** `oracleHost_offQuery`'s table agreement off the query state re-derived `phaseHostTM_tr_of_red_none` by unfolding the host; it is now that lemma, the redirect's absence by `simp [oracleRedirect, hq]` (this file's definition); its sketch says so |

Statements unchanged everywhere; no public declaration changed.

## Brief for the auditor

1. **The fix.** Is each of round 1's six sites now an application of `Turing.phaseHostTM_run_le`
   with only a local guard conversion, and does the lemma apply exactly (the phase family, the
   start `c.mapState (Sigma.mk i)`, the guard's form, the conclusion at the uses: `rw` and term
   uses downstream are unchanged)? Is OracleSim's site exactly `phaseHostTM_tr_of_red_none`?
2. **Rule 10 in the re-points.** The seal (`evidence/round1-fix/seal/`): five sealed copies, built
   by `mkseal.py` from the head files (`*Seal.diff` shows each insertion), with `phaseHostTM`,
   `MultiTapeTM.runFrom`, `MultiTapeTM.step`, `Cfg.mapState`, `Action.mapState`, `Action.apply`
   and `embedEmitTM` locally irreducible and `Action.apply` erased from simp, over primed copies of
   `wr_prefix` and `recordSkipTM_tail` and over `example`s restating the five other sites. Each
   copy's only errors are its seven controls; the controls close unsealed
   (`PHLSealControl.out`). Inspect every `simp`, `rw`, `exact` and `rfl` in the patch: the `rfl`s
   reduce only same-file redirect tables or the proof's own `let`s.
   **Disclosed, unchanged:** `b2b_round_run`'s `hprefix` keeps its statement over the trial
   configuration `d`, which is the tagged `c` by this file's `b2b_trialCfg` and the definitions of
   `Cfg.mapState` and `Cfg.init`, as before the change; the sealed `example` states the re-point
   with the tagged start explicitly.
3. **Completeness, semantically (round 1's note 9).** Is any other proof a re-derivation of either
   lemma? The maintainer's two searches (`evidence/round1-fix/residue.txt`;
   `phasehost-reads-inventory.md` with `sweep/`: every file that uses the host elaborated with
   `phaseHostTM` sealed) find 12 older reads in seven files. Each reads one field of the host (its
   start state, its redirect branch's dispatch) or takes one step; none is a run's prefix or table
   agreement. **By the user's ruling (2026-10-24) they go to a follow-up API PR** (a start-state and
   a redirect-branch equation, with the re-points). Is that classification right? Does any listed
   read in fact re-derive a published lemma and belong here?
4. **No collateral change.** Per file: the freeze (`freeze/`: public and private counts unchanged,
   only the named privates' bodies changed, statements byte-identical); diagnostics equal to the
   base's (`elab/`); axioms (`axioms/`).
5. **Round 1's other points.** Is the minor's records fix adequate (the PR body; the lint records
   at the head)? Is anything in round 1's resolutions unaddressed?
6. **Duplication.** The eight-file screen at the head: no pair new or gone.

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lphl`, round 1's replay snapshot): each of the five files at the
  base and at the head has the same diagnostics: none in `StepBlock`, `WindowRun` and `Inclusions`;
  `OracleSim`'s one linter warning (line 851, older code); `CodeSimulator`'s one sorry warning
  (`exists_uniformSimulator`, 8656 → 8654) (`evidence/round1-fix/elab/`).
- **Axioms** (each head file with `#print axioms` for its public theorems, lemmas and definitions
  appended, `mkax.py`): no `sorryAx` outside `CodeSimulator`'s `exists_uniformSimulator`;
  `CodeSimulator`'s prints are identical at the base and the head (`evidence/round1-fix/axioms/`).
- **Seal:** as in item 2; the sealed copies' SHA-256 are in `seal/sealed-copies.sha256`.
- **Freeze:** `StepBlock` 64/71, `WindowRun` 10/25, `OracleSim` 13/87, `Inclusions` 4/64,
  `CodeSimulator` 12/185 public/private before and after; changed: `recordSkipTM_tail`,
  `wr_prefix`, `oracleHost_offQuery`, `b2b_trial_run`, `b2b_round_run`, `b2b_finish_answer`,
  `canonEmitVerdict`; no statement changed (`evidence/round1-fix/freeze/`).
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 83 files; `SpaceComplexity` 0 FAIL, 81 WARN over
  107 files, both as at the base; `Seam` listed at 919 lines; no new line over 100 characters
  (`evidence/round1-fix/lint-*.txt`).
- **Screen (v3), round 1's eight-file population at `0e5f210b`:** 549 declarations, 125 pairs,
  74,069 characters; against round 1's final head, no pair new or gone
  (`evidence/round1-fix/screen-phl-head3.*`, `pairdiff-r2-head.txt`).
- **Replay:** `replay-lphl2.sh`: the five changed files' downstream closure (23 modules,
  `down-lphl2.txt`; a subset of round 1's 88) at `0e5f210b`, chained from `oleans-lphl` (the tree
  of `a4d9b024`, whose replay passed 88 of 88). **Pending:** as in round 1, this round is
  dispatched before the replay; the PR is clear to merge only when both have passed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/69-phasehost-last-api/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `phasehost-last-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
