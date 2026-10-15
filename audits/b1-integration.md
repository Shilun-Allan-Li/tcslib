# Epoch B1 (oracle machines, light half) — integration record (2026-10-11)

**One maintainer PR** on branch `integrate/b1-oracle` (base `22b6c84a`), as decided by the user. It carries:

- the pre-issue promotion **P0**: the oracle-machine library rows and C1-P1;
- the **eight light B1 targets** of plan §4e, filled from the maintainer's executed route check.

`POracle_eq_P_of_mem_P` is **deferred**, with its statement and docstring byte-identical. It goes
to a shared oracle-call-hosting extension, planned together with B5's `NPOracle_EXPCOM_subset_EXP`
dispatcher. A normal fill gate follows.

## Maintainer decisions applied (user-approved plan)

| # | Decision | Applied as |
|---|---|---|
| 1 | P0 in its natural homes | `Oracle.lean`, `OracleFinite.lean`, new `Build/OracleCall.lean` |
| 2 | One batch, not the split | One PR, three owned chapter files |
| 3 | Defer `POracle_eq_P_of_mem_P` | Untouched; draft headline below |
| 5 | Public first-halt lemma in **`Finite.lean`** | `Turing.MultiTapeTM.exists_first_halt`. The seven private copies are named below; their files are not edited |
| 6 | The two forced mirrors approved | Disclosed with their fractions under **Duplication** |
| 7 | C1-P1 folded in | The blank-cell bound is promoted to `Oracle.lean`. `queryString_length_le` cites it, statement byte-identical. E5 cites it; the private copy is deleted |

## Per-file summary

| File | Lines | Change |
|---|---|---|
| `TuringMachine/Finite.lean` | 331 → 354 | +1 public: `MultiTapeTM.exists_first_halt`, plus one *Main results* bullet |
| `TuringMachine/Oracle.lean` | 517 → 682 | +11 publics (below). `queryString_length_le` is re-derived through the promoted bound, with a flagged C1-P1 appendix; statement unchanged |
| `TuringMachine/OracleFinite.lean` | 131 → 149 | +2 publics: `FinOracleTM.ComputesInTime.mono`, `.output_unique` |
| `TuringMachine/OracleNondeterministic.lean` | 423 → 412 | The private `queryString_length_le_of_blank` is deleted (moved to `Oracle.lean`). E5 cites the public one, with a flagged appendix |
| `TuringMachine/Build/OracleCall.lean` | new, 182 | 6 publics: `queryString_bufferTape`, `answerAction`, `step_of_qQuery`, `step_of_answerAction`, `runFrom_two_of_qQuery`, `capture_reaches_qQuery` |
| `TuringMachine.lean` (facade) | +3 | Imports `Build/OracleCall`; one *Contents* line |
| `ClassOracle/Classes.lean` | 223 → 395 | Imports `Build/OracleCall`. Targets 1–3 filled. +9 privates: `queryTM` with its `_yes`/`_no`/`_agree`/`_init` facts; `negOut`, `negCfg`, `negOut_step`, `negOut_runFrom`. Status line and two flagged appendices |
| `ClassOracle/SATOracle.lean` | 68 → 69 | Targets 4–6 filled; status line |
| `Diagonalization/Relativization.lean` | 412 → 961 | Targets 7–8 filled. +40 privates: the `uw*` family (13) and the stage family (27). Status line and two flagged appendices |
| `machine-library-design.md` | +45 | New §12.9: the oracle-machine rows, and what is not yet there |
| `backlog.md` | +25 | C1-P1 marked discharged; new FH-1 (first-halt dedup) |
| `AroraBarakChapters3-4Plan.md` | +1 row | Decision-log entry |

**New publics (20).**

- In `Oracle.lean`:
  - `OracleTM.step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`;
  - `ComputesInTime.mono`, `ComputesInTime.output_unique`;
  - `runFrom_comm_of_step`, `runFrom_eq_of_forall_ne_qQuery`;
  - `queryString_length_le_of_blank`, `queryString_eq_of_cells`;
  - `runFrom_eq_plainEmptyOracle` (the transfer bridge).
- In `OracleFinite.lean`: the 2 bundled rows.
- In `Build/OracleCall.lean`: the 6 rows above.
- In `Finite.lean`: `exists_first_halt`.

**No public was removed.**

**Targets (8/8):**

- `Classes`: `mem_POracle_of_polyTimeReducible`, `oracle_mem_POracle`, `compl_mem_POracle`.
- `SATOracle`: `compl_SAT_mem_POracle_SAT`, `NP_subset_POracle_SAT`, `coNP_subset_POracle_SAT`.
- `Relativization`: `unaryWitnessLang_mem_NPOracle`, `exists_oracle_ne`.

**Routes**, with the audits' constructions binding:

- **T1.** The P3.1 gift: W1's `captureAction` with its return state taken to be `qQuery`. W1 writes
  on the last tape, which is the query tape. Then the two-step answer tail. Budget
  `(C+2)·2^c·(n^c+1)`.
- **T3.** The P3.1 gift, the direct emission negation, at the same budget.
- **T7.** P3.2 answer 7, the four-state machine, at exponent 1 and constant 3. It is hand-built,
  and its docstring names the missing ND guess-writer row.
- **T8.** P3.2 answer 2, the stage construction:
  - fresh lengths by `Classical.choose`, with witness `2 ^ 2 ^ (i + b + 1)`;
  - import-free counting through `Nat.testBit`;
  - the `max` cutoff of test A9;
  - consistency, then query-set locality with the partial oracle first;
  - domination at `i ≥ k + 1 + 2c`.

## Verification (logs `audits/logs/b1-integration-*`)

- **Changed modules.**
  - Each checks at **0 errors**: `TCSLIB_OLEANS=<OL> bash scripts/lean_check_tree.sh`, never `lake build`.
  - Remaining sorry warnings are exactly the out-of-scope `POracle_eq_P_of_mem_P` (`Classes`) and `baker_gill_solovay` (`Relativization`). `SATOracle`, `Oracle`, `OracleFinite`, `OracleNondeterministic` and `OracleCall` have none.
  - Non-sorry warnings: only the two pre-existing unused-simp-argument linter notes in `Finite.lean`'s `step_output_prepend` (12.2c 11A, line 164).
- **Replay** (`b1-integration-replay.log`; order `b1-integration-replay-order.txt`; raw output `b1-integration-replay-full.log`).
  - Scope: the downstream closure of every changed module, in dependency order. `ComputationalModels` and the root are excluded.
  - Result: **207/207 modules, 0 errors, 0 failures**, 47 sorry warnings.
  - `b1-integration-sorry-sets.log`: the 47 are exactly the source-level sorry-bearing declarations remaining after the change. That set is the base's 55 minus the eight targets; nothing was added.
- **Freeze** (`b1-integration-freeze.log`).
  - No existing statement changed, and no public was removed.
  - Changed bodies are exactly the eight targets, plus `queryString_length_le` and E5, which now cite the promoted bound.
  - The only private removed is the moved `queryString_length_le_of_blank`.
  - Out-of-scope declarations and docstrings are byte-identical.
- **Axioms** (`b1-integration-axioms*.log`, `…-compare.log`).
  - Base prints of the **94 existing publics** of the changed files: 86 are byte-identical after.
  - The other 8 are exactly the targets, which go from `[propext, sorryAx, Classical.choice, Quot.sound]` to `[propext, Classical.choice, Quot.sound]`.
  - `POracle_eq_P_of_mem_P` and `baker_gill_solovay` still show `sorryAx`, identically to base.
  - All **20 new publics** are within the standard triple; `answerAction` uses no axioms.
- **Lint** (`b1-integration-stylelint.log`): `campaign_style_lint.py` over `TuringMachine`, `ClassOracle` and `Diagonalization` gives **0 FAIL** in each. The 14 `TuringMachine` WARNs are the base's 14, an identical set.
- **Size.** `Relativization.lean` is 961 lines, with INFO "> target 600" and under the 1000 threshold. It is a split candidate: the stage construction could move to its own file later. `Oracle.lean` is 682 lines (INFO).

## Duplication (`b1-integration-screens/`; command in `command.txt`)

**Population:** the changed Lean files, `Simulation`, `Embed`, `Catalog`, `Deterministic`,
`Nondeterministic` and `OracleNondeterministic`. `OracleCall` is screened after only.

- **Before:** 390 pairs, 118,065 characters.
- **After:** 397 pairs, 118,605 characters.
- **No pair disappeared.**

The seven new pairs:

| Pair | Fraction | Disposition |
|---|---|---|
| `OracleTM.runFrom_comm_of_step` ↔ `MultiTapeTM.runFrom_comm_of_step` (both directions) | 63/63 = 100% | **Approved forced mirror** (decision 6): the one-term `Semiconj.iterate_right` proof over a different `step` constant |
| `FinTM.ComputesInTime.output_unique` → `OracleTM.ComputesInTime.output_unique` | 72/87 = 83% | **Approved forced mirror** (decision 6): absorb both computations to the later time |
| `uw_tail` → E3 `OracleNDTM.stepWith_eq_of_ne_qQuery` | 78/137 = 57% | Pre-named glue: repeated citations of the fixed-choice step E2 |
| `uw_scan_step` → `uw_false_step` (in-file) | 71/100 = 71% | Pre-named glue: the shared `uw_step_scan` / `inputSymbolInner` call line. The one-unfolding helper keeps the three scan steps from pairing at up to 89% |
| `Catalog.f2_loopBody_step` → `queryTM_init` | 78/145 = 54% | Glue: the `Cfg.ext rfl rfl ?_ ?_ rfl` / `funext` / `by_cases` / `simp` initial-configuration idiom; no machine argument is shared |
| `runFrom_ofMultiTapeTM` → `runFrom_plainEmptyOracle` (in-file, both pre-existing) | 115/217 = 53% | **Screen artifact; no new text.** The base body of `runFrom_plainEmptyOracle`, then the file's last declaration, ran on through the trailing `end OracleTM` / `end Turing` (115/237 < 50%). The new `runFrom_eq_plainEmptyOracle` now follows it, so its body ends earlier |

**"New copies: none"**, apart from the two approved mirrors.

### FH-1: the seven private first-halt copies (recorded, not edited)

`Turing.MultiTapeTM.exists_first_halt` is the public form; `capture_reaches_qQuery` cites it. These
copies predate it, with lines at `22b6c84a`:

| File | Line | Copy |
|---|---|---|
| `ClassNP/EXP.lean` | 812 | `enumCont_first_halt` |
| `ClassNP/SAT.lean` | 914 | `sat_first_halt` |
| `ClassNP/SAT.lean` | 4013 | `sat_call_first_halt` |
| `CookLevin/Hardness.lean` | 6164 | `clA5_call_first_halt` |
| `Build/Catalog.lean` | 5981 | `f2_loop_first_halt` |
| `Build/Catalog.lean` | 8926 | `f2_splitCount_firstHalt` |
| `Build/Loop.lean` | 187 | `loop_first_halt` |

They are recorded as backlog **FH-1**, for the owning files' next windows.

## Route note: the fresh-length margin (fill-gate finding 1)

The P3.2 route asks for a fresh length `nᵢ` with `2 ^ (nᵢ / 10) > nᵢ ^ i + i`.
The fill (`exists_fresh_len`, `freshLen_spec`) uses the weaker condition
`nᵢ ^ i + i < 2 ^ nᵢ`, together with `b < nᵢ` and `i + 2 ≤ nᵢ`. The
counting and the diagonalization need only that condition, so it
**supersedes** the `/10` margin and the theorem is unaffected. The P3.2
margin was a sufficient bound, not part of the argument.
`exists_oracle_ne`'s sketch now states the condition the proof uses
(swept comment-only at the gate close).

## Deferred: oracle-call hosting (the B1b extension)

`POracle_eq_P_of_mem_P` needs a plain host simulating an oracle machine that runs a decider on
the extracted query word. No public row provides this:

- the clean call in `ClassNP/EXP.lean` (`enumCont_cleanTM`) is private, and rewinds the native input;
- no work-tape origin-finding facility exists;
- the framed copy needs a blank at relative cell `-1`.

The draft headline row was elaborated in the pre-ship probe, with the target's call shape checked
from it:

```lean
theorem Turing.FinOracleTM.exists_plain_simulation (M : FinOracleTM Bool) (D : FinTM Bool)
    (O : Language Bool) (τ : ℕ → ℕ) (hτ : Monotone τ) (hD : D.DecidesInTime O τ) :
    ∃ (P : FinTM Bool) (a : ℕ), ∀ (x out : List Bool) (t : ℕ),
      M.ComputesInTime O x out t → P.ComputesInTime x out (a * (t + 1) * (t + 1 + τ t))
```

The supporting rows still to be designed:

- the clean call, promoted and given a variant without input rewind;
- query-head origin tracking;
- query extraction, with cell `-1` saved;
- the dispatch host;
- the budget arithmetic.

These need a design note and a statement gate, shared with B5 (`machine-library-design.md` §12.9).

## Provenance

The fills transcribe the maintainer's pre-ship route check, executed against `22b6c84a` with
0 errors and every assembly within the standard triple. Docstrings, proof sketches and the
long-line wraps were added in place. The pre-ship probe, with the contracts and the B1b
headline, gave 0 errors and 18 `[S]` sorries. Both remain maintainer evidence in the drafting
session.
