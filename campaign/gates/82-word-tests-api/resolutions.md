# The linear word tests (PR #171, an API gate): resolutions

**Gate:** the API gate of PR #171 (`lean/word-tests` at `d17f63c8`). Pack `pack.md`; bundle
SHA-256 `6670e22b2c6aa1ce51bd54206d886048b4d0a6504d70dda4d69f7f9e6bcbc4c9` (46 sections), the records
at `5ffd739e`. **Findings** (`findings.md`, verbatim, SHA-256 `2daa1b36…`; received 2026-10-27):
**PASS, 0 blockers, 0 majors, 3 minors, 12 notes.** The gate is closed.

**The round-1 fix:** commit `9256939f` on #171 (`evidence/round1-fix/round1-fix.patch`), for
findings 1–3. Against `oleans-laplusm`:
- the module with its four axiom prints, and its sealed copy (the same seal over `incFixed`,
  `FinTM.ComputesFunInTime` and `FinTM.ComputesInTime`): 0 diagnostics; the same axioms as
  before (`WordTestsAx.*`, `WordTestsSealed.*`). The seal controls test the definitions, not the
  module, and are unchanged;
- `EXPCOM` with the module inlined (`EXPCOMCat.*`, generator `inline_wordtests.py`): 0
  diagnostics, the base's count; `expcom_front_poly` on `[propext, Classical.choice, Quot.sound]`
  (`EXPCOMCatAx.lean.txt`);
- the freeze: `EXPCOM` 9 → 9 public, 15 → 15 private, the one changed body `expcom_front_poly`;
  `WordTests` 4 → 4, the one changed body `computesFunInTime_allTrue` (`freeze-*-r1.txt`);
- lint: `TuringMachine` 0 FAIL, 68 WARN over 85 files; `Diagonalization` 0 FAIL, 2 WARN over 5
  files, both as in the pack. The policy linter `scripts/style_lint.py` reports 0 findings on
  `WordTests` (`style-lint-WordTests.txt`), the check that would have caught finding 3;
- one line of `WordTests` over 100 characters (101, in the bound's ring identity), new in this PR,
  is wrapped. `EXPCOM`'s one long line (105) predates the PR.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `expcom_front_poly`'s local `hu` still converts `computesFunInTime_ifEq [] [true] [false]` to the singleton `decide` reading. | **True; fixed** in `9256939f`. `hu` is now `polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq [])` composed with `hi.comp ht`, under `simpa only [Function.comp_def]` (a core lemma, no TCSlib definition). The `by_cases` re-proof is gone. **A library-wide search for `computesFunInTime_ifEq`** finds two more members of the family outside the ruling's three files: `SAT`'s `sat_pt_eq` (line 2886) and `CookLevin/Hardness`'s `clA5_pt_eq` (line 6818). Each is `ifEq w [true] [false]` with the same singleton-`decide` conversion, composed with a polynomial field map, and they are twins of each other. They are ledgered with PL-1 for the dedup window (12.2c), beside `Savitch`'s `hD'`, so that #171 and its written replay stay as they are. The other `ifEq` uses are different tests (bit flips, `00`), not this conversion. |
| 2 | minor | `computesFunInTime_allTrue`'s sketch names `computesFunInTime_decideEq []`, but the proof uses `ifEq`; its time argument is not the proof's. | **True; fixed** both ways in `9256939f`. The proof now cites `computesFunInTime_decideEq []`, which also shortens `hout` to one `simp only [incFixed_getD_eq_nil_iff x]`. The sketch now says the composition is by `computesFunInTime_comp`: its bound, the increment's time plus the test's at that time, is linear again, and the constants are absorbed. |
| 3 | minor | The module header lacks `## Main definitions` (policy §1). | **True; fixed** in `9256939f`: "None: the module states contracts for machines that the library already builds." |
| 4 | note | Integrity and snapshot provenance verified. | Agreed. |
| 5 | note | The public forms are total and non-vacuous; the fixed-word constant may depend on the word. | Agreed. |
| 6 | note | Both increment facts are correct and cite existing laws. | Agreed. |
| 7 | note | Output equations and boundary cases check. | Agreed. |
| 8 | note | The composition bound is linear, including on empty input; the stronger length observation is true. | Agreed; the sketch now states the argument the proof uses (finding 2). |
| 9 | note | The leaf placement and catalog entries are appropriate; the Linarith failure was not reproduced. | Agreed. The failing variant is recorded only by its output (`evidence/consumers/TMSATCat-with-Linarith.out`). |
| 10 | note | Rule 10 is respected by the audited changes; `EXPCOM`'s legacy `simp [incFixed]` uses are not sealed here. | Agreed. The one legacy use (`simpa [incFixed] using …`, line 348) dates from 2026-10-12, is unchanged here, and is outside this PR's new code. |
| 11 | note | Freeze, removals and re-points reproduce. | Agreed. |
| 12 | note | Elaboration evidence is consistent; not rerun by the auditor. | Agreed. The replay (below) is the independent elaboration. |
| 13 | note | Lint totals reproduce; the recorded lint does not detect finding 3. | Agreed; see the policy linter's run above. |
| 14 | note | The disclosed deferred duplication is real; verify E-Q's citations when checkpoint 1 lands. | Agreed. The deferred items are ledgered as PL-1 (`campaign/duplication-ledger.md`). E-Q checkpoint 1's guard cites both rows, and its gate (83) checks that. |
| 15 | note | The downstream replay remains pending. | Agreed; it is #171's merge condition (below). |

**The replay.** #170 merged first (`ba2441f7`, 2026-10-27), so `mk-next.sh` merged the campaign
into #171 (clean; head `91a1ad87a8777399251d063eeb474cc38cf5677a`) and wrote `replay-lwords.sh`
(`evidence/merged-tree/`):
- **The closure:** 18 modules, the pack's list, chained from `oleans-lb5am`. It pins the five
  changed files: `WordTests`, the `TuringMachine` facade, `Nondeterminism`, `TMSAT` and `EXPCOM`.
- **The snapshot-tree commit is `79efb462`, #170's merged head.** `oleans-lb5am` is the snapshot
  of `101434fd`. The only Lean difference between the two is `Relativization`'s docstring-only
  commit (gate 81's finding 2). `Relativization` and the `Diagonalization` facade are in this
  closure, so the replay rebuilds them.

Its precheck passed.

**Merge state. #171: not yet clear to merge** (2026-10-27): the gate is passed; it waits for
`replay-lwords`.
