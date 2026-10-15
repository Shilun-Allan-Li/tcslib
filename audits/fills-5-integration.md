# fills-5: three continuation partials, the record-table find universe fix, the B4 pre-issue promotion, and 12.2c T2a: integration record

Side branch `integrate/fills-5`, based on the wave-5 briefs (#58, merged). The branch carries:
- the 12.2c T2a maintainer commit (cherry-picked as `7c2b240d`; its Lean is identical to the
  replayed `13199bda`);
- three continuation deliveries, each applied by `git am -3` with Codex authorship. Their owned
  files were unchanged between the agent's base (`ae9e0af5`) and the integration base, and each
  matches the delivered snapshot byte for byte;
- the maintainer's universe fix for `exists_tableFindTM` (user option (b));
- the B4 pre-issue promotion (`40b38caf`; user: "Promote first"), drafted by a maintainer sub-agent
  in its own worktree and verified by the maintainer.

| Delivery | Brief | Agent commit (base) | Integrated | Report |
|---|---|---|---|---|
| §12.10 W2-S, continuation 1 (partial) | `briefs/w2-fill-oraclesim-cont.md` | `4737c0c1` (`ae9e0af5`) | `52f75eb0` | `audits/wave1-fill-agent-reports/oraclesim-2-REPORT.md` |
| §12.8b record tables, continuation 1 (partial) | `briefs/w1-fill-recordtable-cont.md` | `945183c3` (`ae9e0af5`) | `e4afa616` | `audits/wave1-fill-agent-reports/recordtable-2-REPORT.md` |
| B5a, continuation 1 (partial) | `briefs/b5a-fill-cont.md` | `81943cf0` (`ae9e0af5`) | `3c26a331` | `audits/b5a-fill-agent-reports/cont-1-REPORT.md` |

## Results

- **W2-S: still open (0/1), with 50 admission-free privates.** These are:
  - the R1-relocated frozen call;
  - the source/shadow transport, in which a true-origin shadow tape mirrors the query head and a
    control bit records its side;
  - the off-query transfer, via R1, Z5 and `runFrom_eq_plainEmptyOracle`;
  - the complete local query preparation and restoration, for both signs of the head's
    displacement and zero, and for an arbitrary original cell `-1`. These cost `natAbs p + 3`
    steps each and have no early exits;
  - the specialized copy, and a candidate phase-host machine.

  The service seam, the global invariant and the time ledger remain. There is no obstruction.
- **Record tables: 14/20.** Row 14, `exists_fieldsCopyTM`, is proved for every field count and
  alphabet universe. It is a strong induction citing `rt_copy_run_base`, and it corrects the
  inherited additive constant from 17 to 15 with no statement change. Append has its complete
  seek-and-copy prefix (`rt_append_copy`); its suffix and return remain. There are four new
  privates. **Escalation (row 15):** `exists_tableFindTM` was stated for `Γ : Type*`, but its
  mandated loop `counterLoopTMVia`, like `phaseHostTM`, takes its alphabet in `Type`. The agent
  reproduced the mismatch in a minimal probe and stopped, per rule 4. Resolved below.
- **B5a: still 6/8, with 18 admission-free privates.** These are:
  - the physical binary-header loader `exists_canonHeaderCall`, which extracts the pair's first
    component with `exists_inputCallTM`;
  - the fail-fast length guard: `binaryGuardTM`, an instance of `counterLoopTM` over the input
    block controller `guardBlockTM`, with `_done` and `_escape` contracts whose time bounds are
    independent of the counter's value.

  Both sanctioned imports (`Build/Primitives`, `Build/InputCall`) were added.
  `Codes2Tape.lean` and `EXPCOM.lean` are byte-identical. Neither §12.11 row is assembled yet.
- **The universe fix (maintainer, `49fccb6b`; user option (b)).** `exists_tableFindTM` is restated
  at `{Γ : Type}`, with a flagged "Universe" paragraph in its docstring. Every consumer's
  alphabet (`RecSym Q T`) lies in `Type`, and no declaration cites the row yet.
  - Rows 17–20 were already stated over `Q T : Type`. Rows 14 and 16 stay at `Type*`, since
    their routes need only universe-polymorphic rows.
  - Option (a), generalizing the two hosts, is the optional backlog item **UNIV-1**.
  - The statement change goes to the gate below.
- **12.2c T2a** (`7c2b240d`):
  - FAC-1's facade wiring: seven campaign files, which puts `Codes2Tape` and `Build/Zone` under CI;
  - H-1's audit-program refresh: all 12 targets are now admission-free;
  - item 6's export `Turing.embedEmitTM_tr`.

  Its replay passed: 92 modules, 0 errors (`audits/logs/12.2c-t2a-replay.log`).
- **The B4 pre-issue promotion** (`40b38caf`). Twelve of `ClassNP/SAT.lean`'s private
  declarations become public in `Formulas/CNFEncoding.lean` (namespace `Std.Sat.CNF`):
  - the parse-inverse family `parse_repr`, `takeTrues_repr`, `parseLit_repr`, `parseClause_repr`
    and `parseClauses_repr`;
  - the six-state grammar automaton `syntaxStep`, `SyntaxSuffix`,
    `syntaxSuffix_cons`/`_nil`/`_run`, `syntaxOK` and `syntaxOK_spec`.

  One Mathlib import is added (`Mathlib.Tactic.FinCases`). `SAT.lean` (4,635 → 4,407 lines) and
  `ClassNP/Tautology.lean` (1,728 → 1,629, whose five duplicate `taut_*_shape` lemmas are deleted)
  now cite them; their other declarations changed only in the names they cite.
  `MultiTapeTM.spaceUsedByTape_le_card_Icc` moves from `Build/Zone.lean` to `Build/Catalog.lean`,
  with the same name and statement; Zone, its only user, imports Catalog. The home is `Catalog`,
  not `Deterministic`: 23 modules downstream instead of 222. Catalog's private
  `catalog_space_bound` is a special case, recorded for later retirement. The design doc's line
  about the lemma's home is corrected. Blueprint pages for `SAT`/`Tautology` still name the old
  privates and need regenerating. Freeze: `audits/logs/b4-promotion-freeze.log`.
- No new admission, no proved-modulo citation, and no machine correction in any delivery.

## Verification (maintainer)

- **Integrity.** Every `SHA256SUMS` entry is OK: 42, 43 and 77. Each git bundle verifies, and
  its tip equals the delivered snapshot. The deliveries' environment shims are excluded:
  `app-path.c`, `lean-self-exe.c` and `lean-readlink.c`. So are the agent scripts:
  `run-final-probes.py`, `run-final-sweep.py`, `screen-owned.py`, `screen.sh`, `verify-freeze.py`,
  `freeze_check.py`, `new_pairs.py`, `screen_delta.py`, `verification_audit.py`, `analyze.py`,
  `census.py`, `check.sh`, `copy-coverage.py` and `package.py`. None was compiled or run, and no
  patch references any of them.
- **Freeze** (`audits/logs/{w2-oraclesim-fill-cont-1,w1-recordtable-fill-cont-1,b5a-fill-cont-1}-freeze.log`).
  - No statement changed, and no public was added or removed.
  - Only authorized bodies changed: row 14, plus the flagged appendices.
  - The open targets' comment-stripped code is identical.
  - Privates added: `OracleSim` 50, `RecordTable` 4, `CodeSimulator` 18. No existing private changed.
  - The only import change is B5a's two sanctioned additions.
  - The universe fix's own freeze (`audits/logs/rt-find-universe-fix.log`) shows exactly one
    statement changed, as intended.
- **Duplication.** Every screen matches its agent's byte for byte. Each was run on a tree holding
  only that agent's file over its base (`ae9e0af5`).
  - **W2-S** (24-file population, base 1,416 declarations and 1,735 pairs): 1,746 pairs. These are
    11 new in-file pairs at 52–80%: the local-dispatch configuration and step lemmas (prepare,
    restore and walk phases), each justified in the report.
  - **Record tables** (same base): 1,735 pairs, with no new pair.
  - **B5a** (27-file population, base 1,511 / 1,789): 1,790 pairs, one new in-file pair at 64%
    (`binaryGuard_escape` → `binaryGuard_done`: the two exits of one counter loop).

  **New copies: none.** The head screens together (`audits/logs/fills-5-wave1-screen-combined.txt`,
  1,476 / 1,747; `audits/logs/fills-5-b5a-screen-combined.txt`, 1,571 / 1,801) contain no pair
  beyond the per-batch ones: **no cross-batch pair**.
- **Screen bases at the issue tree** (after the promotion, for this round's briefs):
  `w1-fill-cont2` 1,477 / 1,747, `b5a-fill-cont2` 1,572 / 1,801 and `ch34-b4-mem` 1,472 / 871.
  The first two each gain one declaration, the relocated lemma in `Catalog`, and no pair.
- **Lint** (`audits/logs/fills-5-stylelint.log`): 0 FAIL over `TuringMachine`. The warnings are
  all file-size ones; `OracleSim` now passes 1,000 lines (1,747).
- **Sizes:** `OracleSim` 842 → 1,747; `RecordTable` 1,237 → 1,823; `CodeSimulator` 488 → 869. The
  briefs waive size.
- **Replay** (user-run, fresh `.oleans` into the T2a snapshot, at `40b38caf`;
  `audits/logs/fills-5-replay.log`). It covered the downstream closure of `OracleSim`,
  `RecordTable`, `CodeSimulator`, `SAT`, `Tautology`, `CNFEncoding`, `Catalog` and `Zone`.
  - 54 modules, **all with 0 errors**. Sorry warnings are exactly the expected base, including
    `RecordTable` 6 (one fewer), `OracleSim` 1, `CodeSimulator` 2, `TQBF` 3 and `Zone` 2.
    `SAT`, `Tautology`, `CNFEncoding`, `Catalog` and `Hardness` have 0.
  - The first pass compiled 53. The 54th, `TCSlib/ComputationalModels`, an out-of-campaign catalog
    facade that is pure imports, could not load `TCSlib.BooleanAnalysis.DecisionTree`, whose
    `.olean` was not in the campaign snapshot. That was an environment gap, not a code error. A
    gap-closure run at the same commit compiled `DecisionTree` (Mathlib imports only) into the
    snapshot and then the facade: **2 modules, 0 errors** (the log's last block). The facade was
    this PR's only exposure to a public-name clash, and none occurs.
  - The T2a replay (`audits/logs/12.2c-t2a-replay.log`, 92 modules, 0 errors) covers the Embed
    export and the facade.
- **Axioms and admission walks** (`audits/logs/fills-5-axioms.log`; probe
  `audits/evidence/fills-5/AxF5.lean.txt`, against the replay tree):
  - 59 prints, with no non-standard axiom;
  - every proved public of the three files has an empty walk, including row 14;
  - each of the nine open rows rests on itself alone (W2-S, find, append, rows 17–20, and the
    two §12.11 rows);
  - W2-S's three corollaries and `POracle_eq_P_of_mem_P` rest on W2-S only;
  - the two scheme instances and `EXP ⊆ P^EXPCOM` rest on the two §12.11 rows, and
    `baker_gill_solovay` also on the summit;
  - the private censuses find no `sorryAx` (OracleSim 273, RecordTable 122, CodeSimulator 122).
- **Pre-ship probes,** re-run at the issue tree, all with 0 errors:
  - S128b, with the restated row;
  - S1210, whose census still names the probe-local summit;
  - the B5a probe and the B5a import probe;
  - B4 membership's probe (124 checks, including the nine promoted rows).

  The logs are `audits/logs/{w1-fill-cont2,b5a-fill-cont2,ch34-b4-mem}-preship.log`.

## Disposition

All go in by PR, with:
- **four continuation briefs:**
  - `briefs/w2-fill-oraclesim-cont2.md`;
  - `briefs/w1-fill-recordtable-cont2.md`, which resumes row 15 under the restated statement;
  - and, **B5a split by declaration** (user, 2026-10-12), `briefs/b5a-fill-canon.md` and
    `briefs/b5a-fill-h1.md`. H1 is proved modulo the canonizer;
- **B4 membership's brief**, `briefs/ch34-b4-mem.md` (held last round for this promotion);
- **one small gate pack**, `audits/12.2c-t2a-pack.md`, for the five maintainer Lean changes: the
  facade wiring, the H-1 program, the Embed export, the `find` restatement and the promotion.
