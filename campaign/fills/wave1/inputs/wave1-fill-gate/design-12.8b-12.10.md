# Extract of machine-library-design.md at 1691e4d2: §12.8b (R8.5c and the record tables), §12.9 (oracle-machine rows) and §12.10 (the oracle-call simulation), lines 2153–2408

### 12.8b Record tables, the deferred record rows and R8.5c (statements landed 2026-10-11; design W1 accepted by the user as drafted)

**Why.** §12.8a §8 item 10 deferred five record rows. Their statements need S1b's table layout,
the radius digits, the odometer order, and a template that the validity machine compares
against. §12.8a §9 decision 2 fixed the table convention:
- a nonempty header;
- two blank cells before it, and two after the last field;
- an end-to-start adapter.

Decision 5 sent the deferred rows to their own gate. This increment states that layout, the
five rows, R8.5c, and three small additions the rows and their consumers need.

**Homes.**

| Module | Imports | Contents |
|---|---|---|
| `Build/InputLength.lean` | `Build/CounterLoop` | R8.5c, `exists_inputLengthTM`, alone |
| `Build/RecordTable.lean` | `Build/CfgRecord`, `Build/Seam`, `Build/InputLength` | the layout lemmas, the record template, tables, the adapter, field copy, find and append, and the template, init, validity and next rows |

- R8.5c gets its own small module so that the constructibility files can use it without the
  record layer. 12.2c may fold it into `InputCall`.
- No in-flight file was touched, the imports are acyclic, and TQBF's closure is unchanged.
- Both modules are wired into the `TuringMachine` facade.

**Layout.**

| Declaration | Meaning |
|---|---|
| `tableFields h es` | `h :: es.flatten`, the header then the entries' fields |
| `TableAt d r o h es` | the cells `[-2, L+1]` around origin `o` show `fieldsTape (tableFields h es)` |
| `TableWF m h es` | a nonempty header; every entry has `m` nonempty fields |
| `tableOffset h es j` | where entry `j` starts |
| `recordLength k n s` | `k(2s+1) + posWidth n + k + 4`, the length of every valid record |
| `recordTemplate Q T n s` | the bound field `bits (n+1)` and a window of `2s+1` cells |

- `TableAt` is anchored at an origin, not at the head, because find moves the head and append
  changes the table.
- `TableWF` keeps double blanks at the two ends only, so the seek rows apply.
- `tableOffset` has a closed form, and at `j = |es|` it is the second trailing blank, where
  `seekEndTM` stops.
- `recordTemplate` carries what a candidate record cannot reveal.
- `recordValid_iff_exists_cfg` is the bridge Savitch needs: valid records are exactly the
  records of windowed configurations on the actual input.
- `tableRewindTM` is the adapter, as a real machine: `skipBackTM` then `seekStartTM`,
  R2-seamed, with an exact contract (time `D + 7`).

**Rows.** Every row follows the §12.8 gate conventions:
- an existential module;
- `yes ≠ no` for two-verdict rows;
- a first-return time bound;
- an exact finish that restores every head, the input position, the scratch and the output;
- the work-space clause `∀ u ≤ t, ∀ j, |pos_u j − pos_0 j| ≤ C·(size + 1)`;
- fixed local tape layouts hosted by R1.

| Row | Finish | Time |
|---|---|---|
| `exists_inputLengthTM` | `Nat.bits \|x\|` at the output head | `C(\|x\|+1)` |
| `exists_fieldsCopyTM m` | the source's field layout at the destination head | `C(L+1)` |
| `exists_tableFindTM e m δ a₀ acc` (`0 < m`) | the first entry satisfying the fold predicate, by `findIdx?`: `yes` with the head on it, or `no` with nothing changed | `C(L_tab + \|w\| + 1)` |
| `exists_tableAppendTM m suf` | the table extended by one entry | `C(L_tab + L_e + 1)` |
| `exists_recordTemplateTM` | `recordTemplate \|x\| s` | `C(L_tpl + \|ws\| + \|x\| + 1)` |
| `exists_recordInitTM` | `cfgRecord s (Cfg.init q₀ x) τ₀` | `C(L + \|ws\| + s + \|x\| + 1)` |
| `exists_recordValidTM` | `yes` iff `RecordValid`, nothing changed | `C(L_fs + L_tpl + n + 1)` |
| `exists_recordNextTM` | `first`/`next` over an existential duplicate-free enumeration of exactly the valid records | `C ^ (L + L_tpl + 1)` |

**Decisions** (the design's Q1–Q9, as drafted; the user accepted the draft on 2026-10-11, and the statement gate audits them):

1. **Existential order.** The enumeration order of `recordNext` is existential. Savitch needs
   only a duplicate-free walk of exactly the valid records, and an explicit order would need
   a rank of `Option Q` and `T`, which no consumer reads. The fill uses the carry odometer.
2. **Fuel.** Find takes fuel `|es| < val w` and restores it, because the number of entries is
   on no tape and the only rich loop host needs a counter. A dedicated scanner would be a
   second forward trace, against decision 12.8.5.
3. **R8.5c's route.** It uses a dedicated framed counter whose carry writes `true` on the
   first non-`true` cell, the blank delimiter included. That is the counting phase of
   Catalog's private `f2_counterTM`, framed. The pair goes to the duplication ledger for the
   12.2c window. (§12.8a's "increment with width extension" fails, because `seekEndTM` stops
   one cell past the delimiter.)
4. **Validity time includes `n`.** No public row compares two words by `≤`. The bound
   `v ≤ n+1` uses the `Bool` `counterLoopTM`, lifted onto two digit tapes, at cost `O(n)`.
   Space stays `O(L + L_tpl)`.
5. **The three additions are rows:** `fieldsCopy`, `recordTemplate` and the adapter. There is
   no `tableMem` row; S1b keeps its inner loop.
6. **Homes** as above, with facade wiring at landing.
7. **Input convention.** The rows that read the native input enter at position `1` and
   restore it, as `inputCopyTM` and `inputFoldTM` do. Contrast `recordStepTM`, which saves and
   restores an arbitrary position.
8. **`recordNext`'s exponential bound** is honest: gaps between valid records are exponential,
   and `ComputesInSpace` needs only halting.
9. **The table rows are generic over `Γ`.** Find takes `e : Bool ↪ Γ` for its counter.

**Degenerate cases** (checked in the statements or executed by the probe):
- find at `m = 0` would be false, since `tableFields h [] = tableFields h [[]]`; hence `0 < m`;
- validity needs `|fs| = k + 3`, without which the verdict is not a function of the tape;
- the empty table;
- `T` empty: `first` answers `no` through `match`;
- `k = 0`, `s = 0` and `n = 0`.

**Consumers.**
- **S1b (§12.8a §4):** the template, the counters, the initial table, the round's find,
  copy, step, membership and append, and the verdict find.
- **Savitch:** the template, the start vertex, the midpoint enumeration, adjacency through the
  landed step and equality rows, and frame push and pop. Every frame is `O(S n)`.
- **The constructibility files:** `exists_inputLengthTM`.

**Fill dependencies.**

| Rows | Need |
|---|---|
| find and next | R8.0b |
| adapter, fieldsCopy and append | the Catalog Part-3 fill (delivered, PR #42) |
| template, init and valid | R8.5c and R8.6 |

Evidence: `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, which runs the design's
executed checks against the landed definitions.

### 12.9 Oracle-machine rows (landed 2026-10-11 with epoch B1; `Build/OracleCall.lean`)

**Why.** Every §12 row is plain-machine level, and the oracle model (`TuringMachine/Oracle.lean`)
had no run algebra. The B1 one-query constructions needed three capabilities: (i) a computation
captured onto the **query tape** and submitted; (ii) the four-state **answer tail**; (iii) a way for
plain contracts to drive an oracle machine.

**Rows.**

- In `Oracle.lean`:
  - the run algebra: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`,
    `runFrom_comm_of_step`, `ComputesInTime.mono`/`output_unique`;
  - the extraction contract: `queryString_length_le_of_blank` (C1-P1) and `queryString_eq_of_cells`;
  - **the transfer bridge** `runFrom_eq_plainEmptyOracle`, after `runFrom_eq_of_forall_ne_qQuery`.
    On a run segment that avoids `qQuery`, the oracle run is the run of the plain table
    `plainEmptyOracle`, so host-parametric plain contracts apply unchanged.
- In `OracleFinite.lean`: the bundled `mono` and `output_unique`.
- In `Build/OracleCall.lean`:
  - `queryString_bufferTape`;
  - `answerAction`, with `step_of_qQuery`, `step_of_answerAction` and `runFrom_two_of_qQuery`;
  - **query capture** `capture_reaches_qQuery`: W1 with its return state taken to be `qQuery`.
    W1 writes on the host's last tape, which is the query tape.
- In `Finite.lean`, the shared guard discharge: `MultiTapeTM.exists_first_halt`.

**Consumers.**

- `mem_POracle_of_polyTimeReducible`, and through it the `SAT`-oracle corollaries and
  `EXP_subset_POracle_EXPCOM` (B5);
- `unaryWitnessLang_mem_NPOracle`, using the tail through `OracleNDTM.fixChoice`;
- `compl_mem_POracle`, using `runFrom_comm_of_step`.

**Not yet here: oracle-call hosting.** This is a plain host simulating an oracle machine that runs
a decider on the extracted query word. It is the library gap behind `POracle_eq_P_of_mem_P`
(deferred) and B5's `NPOracle_EXPCOM_subset_EXP` dispatcher. Its rows need a design note and a
statement gate:

- the headline simulation;
- the private clean call of `ClassNP/EXP.lean` promoted, without the native-input rewind;
- origin tracking for the query tape;
- query extraction with cell `-1` saved;
- the dispatch host.

The draft headline statement, `FinOracleTM.exists_plain_simulation`, is recorded in
`audits/b1-integration.md`. **Designed and stated in §12.10** (2026-10-11).

### 12.10 Oracle-call simulation (statements landed 2026-10-11; design W2, route and homes accepted by the user)

**Why.** §12.9 records the gap, "not yet here: oracle-call hosting". No public row lets a
plain host simulate an oracle machine by running a decider on each extracted query. Two
targets are blocked:
- B1's last, `POracle_eq_P_of_mem_P`;
- B5's summit, `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and
  `baker_gill_solovay`.

**The decision: one trace, and nondeterminism by choice words.**
- **The deterministic row is the only oracle-call simulation trace.** It is a plain host that
  answers each query by a clean call of the decider.
- **The nondeterministic form is a reduction, not a second simulation:**
  1. the choice-word machine determinizes the oracle NDTM along a word on a work tape;
  2. the deterministic row simulates it;
  3. the plain certificate shell and the proved `exists_proj_decider` enumerate the words.

  The total is `2^O(p)`.
- **Branchwise simulation is rejected.** Branches would consume choice bits through every
  decider run, so the only public determinization would enumerate doubly exponentially many
  words. Avoiding that needs a sparse-guess row, which is a second trace under another name.
- **Virtual input stays at the plain level, after the simulation.** An oracle machine has one
  `qQuery` state, so an oracle-level Z1 would re-prove Z1's lockstep. This forces the
  deterministic row to be stated **from preloaded starts**. The `initCfg` form, the B1b draft
  headline, is a proved corollary.

**Rows.**

| Module | Declaration | Status |
|---|---|---|
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ `_nil`, `_update`), `Cfg.init_eq_ofWords`, `OracleTM.queryString_runFrom_length_le_of_blank` (W2-0) | proved |
| | **`FinOracleTM.exists_plain_simulation`** (W2-S): from any preloaded start, a plain host reproduces the oracle machine's halting output within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(\|query_r\|)` | sorried |
| | `…_of_monotone`, `…_initCfg`, `FinOracleTM.exists_plain_decider` | proved from W2-S |
| | `FinOracleNDTM.choiceOut`, `choiceOut_eq_true_iff`, `mem_iff_exists_choiceOut` | proved |
| | **`FinOracleNDTM.exists_choiceTM`** (W2-C): the choice-word machine, `≤ 2\|u\| + 2` steps, the same queries | sorried |
| `Build/CertShell.lean` | **`FinTM.exists_certificateShell`** (W2-V): the plain shell deciding `{x ++ u \| \|u\| = C(\|x\|+1)^c ∧ out x u = [true]}` | sorried |
| | `FinTM.certificateShell_proj` | proved |

- The exact sum, "`T_D` of the query lengths", needs no monotonicity.
- Both instantiations follow from the monotone corollary:
  - polynomial `τ` gives `P^O = P`;
  - exponential `τ`, at a polynomial-time machine, gives `P^EXPCOM ⊆ EXP`, and the summit
    follows through W2-C.

**Fill routes** (binding sketches in the docstrings).
- **W2-S:**
  - the source's tapes, a shadow tape tracking the query head's side of the origin, the Z1
    bank of the clean call `exists_installCallTM`, and a scratch tape;
  - off `qQuery`, the bridge `runFrom_eq_plainEmptyOracle` plus Z5;
  - at `qQuery`, nine R2-seamed phases: bookmark, origin walk, save and blank cell `-1`,
    `copyTM`, the Z1 call at `y = []`, read the verdict, restore, walk back, answer.
- **W2-C:** lockstep by induction on `u`, in the `toOracleNDTM_runWith` shape. An exhausted
  word answers `false`, so an unhalted branch never shows `[true]`.
- **W2-V:** the native-input call R8.5e (`exists_inputCallTM`) at `splitSolve`, then Z1 inside
  the **returning** R1 capture, then a three-state scan. R8.5e is proved at the tip since PR
  #41, so W2-V's route cites no sorried row.

**Decisions.** The user took the first and third (2026-10-11); the rest are as drafted and
go to the statement gate.

1. **The route:** one trace, choice-word enumeration, no branchwise row.
2. **W2-S in preloaded generality,** with the `initCfg` form derived.
3. **W2-V in its own plain module,** `Build/CertShell.lean`, keeping plain consumers off the
   oracle module. Deduplicating the private 2B shell in `ntime_poly_subset_NP` is the shell's
   second customer, a 12.2c item.
4. **W2-C is public here.** It is the core of a relativized Theorem 2.6. It has one named
   customer, against the rule of admission's two.
5. **Time only.** The oracle layer has no space measure. This is flagged against the §12/§13
   space mandate.
6. **Sequencing.** W2-S and W2-C can be filled at once; W2-V's sorried dependency is gone.

**Mirrors, factored** (disclosed at landing; factored in round 2 of the wave-1 statement gate,
2026-10-11, user decision; `audits/wave1-statements-resolutions.md`):
- W2-0 and the private invariants `runFrom_workTapes_invariant` (`Oracle.lean`) and
  `runWith_headBlank` (`OracleNondeterministic.lean`) now all specialize the promoted
  `OracleTM.step_radius`/`OracleTM.runFrom_radius` (`Oracle.lean`).
- `certificateShell_proj` and `Nondeterminism.lean`'s split callers cite
  `append_split_unique` with `certificateLength_strictMono` or
  `expCertificateLength_strictMono` (new module `ChoiceWords.lean`). The private split lemmas
  are deleted.
- `mem_iff_exists_choiceOut` and `Nondeterminism.lean`'s acceptance argument share
  `choiceBudget_le` and `run_take_of_halted` (`ChoiceWords.lean`).

**Consumers** (derived in `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`):
- `POracle_eq_P_of_mem_P`, which rests on W2-S alone;
- `NPOracle_EXPCOM_subset_EXP`, the summit;
- `baker_gill_solovay`.

Each is `rfl`-identical to its campaign statement, as are the three `EXPCOM` identities the
probe also derives. The probe's deterministic inclusion `POracle_EXPCOM_subset_EXP'` is
probe-local: it is derived from W2-S directly and has no campaign counterpart.

B5's own `exists_EXPCOM_decider` (home `Diagonalization/EXPCOM.lean`) is the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row.

