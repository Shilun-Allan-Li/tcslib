# External audit pack — §12.8 statement gate: the rich-alphabet record layer (R8.0–R8.8)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). §12.8
of `machine-library-design.md` designs the machine rows that S1b needs:
S1b is the configuration-graph simulation behind `NSPACE(S) ⊆ DTIME(2^{O(S)})`.
The same rows also serve Savitch, the space hierarchy, TQBF and the §13d zone
revision. The design doc is attached in full. Its relevant sections are:

- **§12.8**, the design and decisions 12.8.1–12.8.6. Configuration records
  use a **rich alphabet**, and the `Bool` counter rows run on rich tapes
  through one embedding transport.
- **§12.8a**, the statement draft. Its §8 records the landed layer, the
  changes from the draft, and decisions O1–O7.

**Why a gate, and why a PR.** Two rules apply:

- **The §13d rule.** Catalog and Seam are G1-owned files, and `scanTM` is the
  G2 core of the §13d revision. Every Lean change of that revision lands by a
  PR the user merges, plus its own audit gate.
- **Decision O7.** The transport R8.0 (PR #16) lands by PR plus this gate.

The change is **one PR** (`integrate/s12-8-statements`). It contains:

- `91af3305`, the R8.0 transport. This is PR #16's only commit, so merging
  this PR merges #16.
- `508dae33`, the statement layer.
- `06e93198`, its records.
- `a40f486c`, a merge of the campaign tip (12.2c T1). It was clean; the only
  shared file is TQBF, where one docstring line changed.
- The commit carrying this pack.

**The audit object.** Almost everything is a statement:

- **25 sorried contracts**, each with a proof sketch;
- the **definitions**: machines, carriers and phase types;
- the **proved** transport R8.0;
- two proved results that keep their proofs: `seamCompTM_runFrom_left`, a
  verbatim promotion, and `cfgRecord_length`.

Audit them for truth, adequacy for the named consumers, freedom from vacuity,
and placement. The gate closes on zero blockers and zero majors. The
duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

## What is proposed (verify)

| File (new unless noted) | Declarations | Status |
|---|---|---|
| `TuringMachine/SymbolLift.lean` (PR #16) | **R8.0**: `decodeBool`, `decodeBool_apply`, `Action.liftSymbols`, `Cfg.liftSymbols` with `_state`, `_workTapePos`, `_inputSymbol`, `MultiTapeTM.liftSymbols` with `_step`, `_runFrom`, `_initCfg`, `_spaceUsed`, `FinTM.liftSymbols`, `FinTM.liftSymbols_computesFunInTimeVia` | all proved |
| `Build/Catalog.lean` (changed: Part 3 added, 528 lines) | the one-tape actions `tapeAction`, `inputMoveAction`; the field layout `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field`; **R8.1** `compareTM_run_ofCfg`; **R8.3** `SeekPhase`, `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg`; **R8.2** `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_{fold,map,shiftRight,shiftLeft,carry}` | 12 sorried: `fieldsTape_field`, compare, the four seek contracts, scan, the five identities |
| `Build/Scan.lean` | **R8.4, R8.4′, R8.5a, R8.5d**: `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | 4 sorried |
| `Build/InputCall.lean` | **R8.5e** `FinTM.exists_inputCallTM`; **R8.5b** `exists_inputSeekTM` | 2 sorried |
| `Build/CounterLoop.lean` (changed) | **R8.6** `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | 1 sorried |
| `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; **R8.7** `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | 5 sorried |
| `Build/Seam.lean` (changed) | **R8.8** `seamCompTM_runFrom_left` (the private `seamComp_left`, promoted verbatim; proved), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | 1 sorried |
| `ClassPSPACE/TQBF.lean` (changed) | `Cfg.InWindow` removed (moved to CfgRecord); imports CfgRecord | statements unchanged |

**Not in this gate** (§12.8a §8, item 10):

- the R8.0 corollaries such as `FinTM.bufferTape_map`;
- R8.5c `exists_inputLengthTM`;
- R8.0b `counterLoopTMVia`. A later batch, after this gate; its target
  signatures are in §8.
- the record rows for validity, init, next, and table append and find. Their
  statements need S1b's table layout.

## Brief for the auditor

1. **Freeze.** From the attached patch, confirm:
   - no existing statement changed;
   - nothing public was removed except `Cfg.InWindow`, whose statement and
     body move to CfgRecord byte-identical, with two sentences added to its
     docstring;
   - `seamComp_left` became `seamCompTM_runFrom_left` with its statement and
     body unchanged;
   - the three privates that cite it changed only in the cited name;
   - no other proved body or private changed.
2. **Truth of the 25.** Blind-restate each sorried statement from its
   signature, then decide whether it is true as stated. Give the argument or
   a counterexample, and check every exact time against the machine's table.
   In particular:
   - **The framed rows** (R8.1, R8.3, R8.4, R8.4′, R8.5a, R8.5d, R8.6). Each
     follows the §12.6 template: exact time, finish configuration, no earlier
     exit, trajectory. Check the degenerate cases: `w = []`, `ws = []`,
     `pat = []`, a counter at value 0, displaced heads, nonblank frames.
   - **`scanTM_run_ofCfg` and `scanResult`.** The forward Mealy pass runs
     first. The backward pass runs on its output reversed, and the result is
     reversed back. Is that the right semantics for a head that turns at the
     right delimiter? Do the five identities say what the fold, the map, the
     two mark shifts and the carry need?
   - **`cfgRecord_inj`.** Is the window hypothesis on both sides necessary
     and sufficient? Is leaving the output out right, given that the vertex
     quotient compares cores?
   - **`recordValid_iff`.** Check both directions, the position-digit clause
     `v ≤ n + 1` and the single-mark clause. Is the right-hand side what a
     fold-based validator can check field by field?
   - **`fieldsTape_field`**, at the first and last field.
3. **The transport R8.0 (proved).** Rule on its public surface:
   - `decodeBool` reads a foreign symbol as a blank. Is that the right
     convention?
   - `liftSymbols_runFrom` is stated on lifted configurations only. Is that
     the strength consumers need?
   - `liftSymbols_spaceUsed` and `liftSymbols_computesFunInTimeVia`.
   - `liftSymbols_step` is public in the landed file; the §12.8a §1 draft
     made it private (§8, change 11). Should it stay public?

   §12.8a §0 shows that a lifted machine's space on foreign inputs is not
   controlled. Decision O6 makes input validation (R8.5d, `inputFoldTM`)
   mandatory for rich space-bounded consumers. Is O6 the right resolution?
4. **The modules as contracts.** The consumers are in §12.8a §4 and §6: S1b,
   Savitch, the space hierarchy, TQBF and G3/G4. For each existential module,
   check three things: vacuity, whether a host can establish the entry
   condition, and whether the exit gives the next phase what it needs.
   - **`exists_recordStepTM`.**
     - The not-windowed branch must leave everything unchanged.
     - The record interval is rewritten in place. The new record must have
       the same length; check this.
     - A halted `c` is handled through `hupd`.
     - The bound is `C·(L + |x| + 1)`.
   - **`exists_recordEqTM`.** `fs` and `gs` are constrained only to `k + 3`
     fields, so a field may be empty, which puts two blanks in a row. Is the
     statement true then? Or should it require nonempty fields, or
     `RecordValid`?
   - **`exists_recordTestTM`.** The host input `y` is arbitrary, and
     separate from `c`'s input `x`.
   - **`exists_inputSeekTM`.**
     - It takes a little-endian value with `p ≤ |x| + 1`.
     - The input head may start anywhere, and the bound is
       `C·(|w| + pos + p + 1)`.
     - Every work tape, work head and the output are restored.
     - The `u = 0` instance of the no-earlier-exit clause forces
       `entry ≠ exit`.
   - **`exists_inputCallTM`.** It starts at the blank seam and ends with `f x`
     installed on tape `0`, within `c·(T|x| + |x| + |f x| + 1)`, with
     `0 < C.k`.
   - **`seamCompTM₂_run_ofCfg`.** Each exit has its own continuation, and
     each continuation runs unboundedly after the dispatch step.
   - **Vacuity.** Every record row carries `yes ≠ no` (§8, change 1).
     Confirm that no contract is satisfiable by a module that never reaches
     a verdict.
5. **The open questions** of §12.8a §8. Give a recommendation on each; the
   user disposes.
   1. The skip-back convention.
   2. The empty table: should tables carry a header field?
   3. The cyclic writer.
   4. The fixed tape layouts of the record rows.
   5. Whether the deferred record rows enter this gate or S1b's.
   6. Facade wiring. `SymbolLift` is not in the facade either. The §12.8a
      §1 draft line saying the facade gains one import is superseded by §8.
   7. G2's agreement to `scanTM` as its core.
6. **Placement and naming.**
   - The field layout lives in Catalog. Is the seek rows' dependence on it
     the right reason?
   - CfgRecord imports Catalog and `SymbolLift`, not CounterLoop.
   - TQBF's import closure gains Catalog, `SymbolLift` and CfgRecord. Is
     that acceptable?
   - `RecSym` lives in `Turing`. Check the names.
7. **Duplication (failure mode 5).** The screen goes from 396 to 408 pairs:
   12 new, all within a file, none across files, none gone.
   - **The first attempt** wrote literal `Action` tuples and had 17 new
     cross-file pairs. The named actions `tapeAction` and `inputMoveAction`
     removed them. Confirm these are honest helpers, naming the action
     vocabulary, and not obfuscation. The R3 tables are unchanged.
   - **`seekEndTM` ← `skipTM` at 100%.** `seekEndTM` is `skipTM`'s table
     plus a `gap` phase. The rest of the seek family sits at 60–84%. Rule:
     these are distinct small tables sharing one phase type, so forced? Or
     should the seeks be derived from skip and skip back? O5's alternative,
     a counter loop over `skipTM`, was rejected as slower.
   - **`writeConstTM` ← `writeAdvTM`** at 58%.

   Is any pair a copy?
8. **Docstrings.** Report any docstring made false. Check:
   - every new docstring and proof sketch;
   - Seam's and Catalog's module documentation;
   - `InWindow`'s two added sentences.
9. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Replay, merged branch** (`audits/logs/s12-8-statements-merged-replay.log`;
  order list `…-merged-order.txt`).
  - 18 modules: the downstream closure of the eight changed and new files, in
    dependency order, with `ComputationalModels` and the root excluded.
  - It ran on the branch at `55bd21df`, which contains the campaign tip
    `29e2ffd5`, into a snapshot of the tip's olean tree. The user ran it from
    the maintainer's command.
  - **0 errors**; every module exits 0.
  - The 35 sorry warnings are the base 10 (SATOracle 3, TQBF 4, Zone 2,
    Codes2Tape 1) plus the 25 new ones (Seam 1, Catalog 12, CfgRecord 5,
    Scan 4, CounterLoop 1, InputCall 2). `SymbolLift` has none.
* **Replay, before the tip merge** (`…-replay.log`, base in
  `…-replay-base.log`).
  - 17 modules, 0 errors, with the base sorry set unchanged: SATOracle 3,
    TQBF 4, Zone 2, Codes2Tape 1.
  - 25 new sorries: Seam 1, Catalog 12, CfgRecord 5, Scan 4, CounterLoop 1,
    InputCall 2.
  - The non-sorry linter output matches the base in count.
* **Transport** (`…-transport-check.log`). `SymbolLift` exits 0 with no errors
  and no warnings. `audits/evidence/s12-8/R80TransportProbe.{lean.txt,out}`
  prints the axioms of its 14 public declarations, all within
  `[propext, Classical.choice, Quot.sound]`.
* **Pre-ship probe** (`audits/evidence/s12-8/S128StatementsPreship.lean.txt`,
  `…-preship.log`). 35 executed examples, 0 errors, 0 warnings. They cover:
  - skip and skip back, each including the empty word;
  - seek end, and seek start including `ws = []`;
  - the field layout;
  - scan: a fold at a displaced head with a nonblank frame, and `w = []`;
  - the five identities on concrete words;
  - the framed compare: equal words, a proper prefix, both empty;
  - the constant writer, and the advancing writer (once, twice, empty);
  - the input copy and the input fold;
  - `expandTM` in three cases;
  - record shapes, `posWidth`/`binDigits` and `fieldsTape`;
  - the two-exit seam, on both exits.

  The existential modules, `cfgRecord_inj` and `recordValid_iff` cannot be
  executed and are not probed.
* **The draft probe** (`S128StatementsProbe.{lean.txt,out}`). This is the S1
  agent's draft of §12.8a, superseded by the landed names in §8.
* **Axioms** (`…-axioms.log`). `cfgRecord_length` and `seamCompTM_runFrom_left`
  print `[propext, Quot.sound]`. Every other new theorem is a sorried
  statement.
* **Freeze** (`…-declfreeze.log`).
* **Lint** (`…-stylelint.log`, `…-transport-stylelint.log`). 0 FAIL. All 14
  WARNs are pre-existing file-size warnings for files over 1,000 lines.
  Catalog is now 11,789 lines and CounterLoop 1,275. Catalog's split is the
  12.2c per-theme split.
* **Screen** (`…-copytext-{before,after,diff}`). It covers Catalog, Seam,
  CounterLoop, Embed, Simulation, `SymbolLift` and TQBF, plus the three new
  files in the after run. The screen script is attached. It was taken before
  the tip merge. In these files the merge changed only one docstring line in
  TQBF, and the screen strips comments.
* **Inputs.** All new and changed sources are attached in their final state,
  with the patch against the campaign base `22b6c84a`. The cited layers are
  attached too: `Configuration`, `Deterministic`, `Finite`, `Simulation`,
  `Build/Convention`, `Build/Embed`, `Build/Loop` (`exists_installCallTM`,
  `stateWord`) and `Robustness/AlphabetReduction`.
* **Evidence boundary.** No delivery zip exists. The maintainer wrote this
  layer from the S1 agent's statement draft (§12.8a). The replay, axiom and
  lint results are maintainer attestations from the attached logs.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-statements-findings.md`.
