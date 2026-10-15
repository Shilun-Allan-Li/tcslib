# External audit pack — wave-1 statements: §12.8b record tables, §12.10 oracle-call simulation, §12.11 the B5a code simulator

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). This is one
statement gate over three design increments that landed together (user decision: one PR,
one gate). Each fills a library gap that blocks named fill targets.

| Increment | Gap | Blocked targets |
|---|---|---|
| **§12.8b** | §12.8a deferred five record rows to their own gate. They need the table layout, the template and the odometer order, which this increment states. | S1b (TQBF and `NSPACE ⊆ DTIME`), Savitch, and the constructibility files (R8.5c) |
| **§12.10** | No public row lets a plain host simulate an oracle machine with a decider answering its queries (§12.9's "not yet here"). | B1's `POracle_eq_P_of_mem_P`; B5's summit `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and `baker_gill_solovay` |
| **§12.11** | There is no machine-format-parameterized interpreter. Universal's is one-tape and hard-wired. | B5a: `exists_uniformMachineCode` (EXPCOM) and ZF-B4's `exists_uniformMachineCode2` |

The design text is attached as `audits/evidence/wave1-statements/design-sections.md`, an
extract of `machine-library-design.md` §§12.8b, 12.10 and 12.11.

This PR (`integrate/stmt-w1w2b5a`) lands **26 sorried statements with sketches**, plus proved
definitions, layout facts, corollaries and bridges. **No fill is under audit. What you audit
is the statements:**
- are they true;
- are they adequately strong for their consumers;
- are they free of vacuity;
- are they well placed?

The gate closes on zero blockers and zero majors (`workflow.md` §4). The duplication rule
(`audits/TEMPLATE.md`, failure mode 5) is in force.

## What is proposed (verify)

| File (all new except the facade) | Content | Sorried |
|---|---|---|
| `Build/InputLength.lean` | R8.5c, `exists_inputLengthTM`: `Nat.bits \|x\|` written in `C(\|x\|+1)` | 1 |
| `Build/RecordTable.lean` | the layout and template facts (`joinFields_length`, `fieldOffset_length`, `joinFields_cfgRecord_length`, `cfgRecord_field_ne_nil`, `cfgRecord_init`, `recordValid_iff_exists_cfg`, `joinFields_recordTemplate_length`, `binDigits_posWidth_succ`); tables (`tableFields`, `tableOffset`, `TableWF`, `TableAt`, `TableWF.field_ne_nil`, `tableOffset_eq`, `tableOffset_length`, `TableAt.recordAt_take`); the adapter `tableRewindTM` with its exact contract; the rows `exists_fieldsCopyTM`, `exists_tableFindTM`, `exists_tableAppendTM`, `exists_recordTemplateTM`, `exists_recordInitTM`, `exists_recordValidTM`, `exists_recordNextTM` | 20; `RecordValid.joinFields_length` is proved from one of them |
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ two laws), `Cfg.init_eq_ofWords`, the query-length bound W2-0, all proved; **W2-S** `FinOracleTM.exists_plain_simulation`; its proved corollaries `…_of_monotone`, `…_initCfg` (the B1b draft headline, verbatim) and `exists_plain_decider`; the relativized certificate reading `FinOracleNDTM.choiceOut` (+ two proved laws); **W2-C** `FinOracleNDTM.exists_choiceTM` | 2 |
| `Build/CertShell.lean` | **W2-V** `FinTM.exists_certificateShell`; `FinTM.certificateShell_proj` (proved) | 1 |
| `CodeSimulator.lean` | `Turing.MachineFormat` (a `CodeFormat` with `k`, `machine` and two laws), the generic writers (`workReadsK`, `tableBitsK`, `serializeK`, `codeSkipTableK`) with proved bridges to the frozen two-tape writers, `oneTapeMachineFormat` (proved; `decode = codeDecode` and the machine is `CodeTM.toFinTM`, by `rfl`), **`exists_polyCanonizer`**, and the headline **H1** **`exists_uniformSimulator`** | 2 |
| `TuringMachine.lean` (facade) | five imports and Contents bullets | — |

**Decisions already taken by the user** (2026-10-11):
- W1 accepted as drafted;
- W2's route and homes accepted: one trace with choice-word enumeration, and the shell in its
  own plain module;
- B5a's headline is **H1**. H2, the per-code-linear form, is in `backlog.md`, and H2 ⇒ H1 is
  proved in the B5a probe.

The remaining design choices are **as drafted, and yours to challenge**. They are listed per
increment in `design-sections.md`.

## Brief for the auditor

1. **Truth.** Blind-restate every sorried statement from its signature, then decide whether
   it is true as stated. Give the argument, or a counterexample. Priorities:
   - **W2-S** (`exists_plain_simulation`):
     - preloaded starts `Cfg.ofWords … w` with `w (Fin.last M.k) = []`;
     - the bound `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(|query_r|)`, with `a` uniform in
       `x`, `w` and `t`;
     - `M.k + 1 ≤ P.k`, with `prefixWords` placing the source tapes.

     Is the per-query `a·(t+1)` honest, covering the origin walk, extraction with cell `-1`
     saved, and the restore? Note that the statement must not assume blank ordinary tapes.
   - **W2-C** (`exists_choiceTM`): exactly `2|u| + 2` steps, including exhaustion at a query
     and `N.q₀ = N.qQuery`, with the output equal to `N.choiceOut O x u` under **every**
     oracle.
   - **W2-V** (`exists_certificateShell`): its language `{x ++ u | |u| = C(|x|+1)^c ∧ out x u
     = [true]}`, with malformed lengths rejected, and the bound `b·((m+1)^e + T m)`.
   - **H1** (`exists_uniformSimulator`):
     - deadline-inclusive acceptance;
     - the joint polynomial in `|α| + |x| + t`;
     - **every** `MachineFormat`, with no law on the guard;
   - and `exists_polyCanonizer`.
   - **The §12.8b rows:**
     - find's `findIdx?` verdict, with fuel `|es| < val w` and `0 < m`;
     - append's layout extension, including entries with empty fields;
     - the template's two fields;
     - init's exact record;
     - validity's `|fs| = k + 3` premise;
     - `recordNext`'s existential duplicate-free enumeration, its `first`/`next` `match`
       forms, and the `C ^ (L + L_tpl + 1)` time;
     - R8.5c's framed finish and head range.
   - **The layout facts:** `tableOffset_eq`'s closed form, `tableOffset_length` at
     `j = |es|`, and `recordValid_iff_exists_cfg`. That last one is the bridge Savitch needs.
2. **Adequacy.** Do the rows suffice for their consumers, by the routes in the design text?
   - S1b's round (§12.8a §4) and verdict, from find, fields copy, the landed step and
     equality rows, and append.
   - Savitch's template, start vertex, midpoint enumeration and frame copies, at `O(S n)` per
     frame.
   - `spaceConstructible_logSpace` and its siblings, from R8.5c.
   - B1's `POracle_eq_P_of_mem_P`, and B5's `POracle_EXPCOM_subset_EXP`,
     `NPOracle_EXPCOM_subset_EXP` and `baker_gill_solovay`. Each is restated verbatim and
     derived in the §12.10 probe, `rfl`-identical to the campaign statement. B5's own
     `exists_EXPCOM_decider` is sorried there, as a B5 obligation.
   - EXPCOM's and ZF-B4's uniform schemes, assembled from H1 and the canonizer in the B5a
     probe.

   Is anything left implicit that a fill would have to invent: a length bound, a tape
   layout, a head position, a canonicality, or behaviour on malformed input?
3. **Vacuity and degenerate cases.** Check that no row is vacuously satisfiable, for example
   a host that never reaches its verdict, or a `yes`/`no` pair that may coincide. The designs
   list their own checks: `m = 0` (find would be false without `0 < m`); the empty table;
   `T` empty; `k = 0`, `s = 0` and `n = 0`; `x = []`; `u = []`; an `M` that never queries;
   `t = 0`; non-monotone `τ`; and an unsatisfiable `hD`.
4. **The as-drafted choices.** Rule on each:
   - W1's existential enumeration order, find's fuel tape, R8.5c's dedicated framed counter
     (a sibling of Catalog's private `f2_counterTM`, for the ledger), validity time `O(L + n)`,
     the input-position-1 convention, and generic `Γ`.
   - W2's preloaded generality and time-only bounds (the oracle layer has no space measure:
     flagged against the §12/§13 space mandate). Also W2-C being public with one named
     customer.
   - B5a's `MachineFormat` laws (`serialize_eq`, `skipTable_eq`), and that NDCodes is not an
     instance.
5. **Placement and naming.** Five new modules:
   - R8.5c on its own, importing only CounterLoop, so that the constructibility files do not
     pull the record layer;
   - the shell separate from the oracle module;
   - `CodeSimulator` at `TuringMachine/`, not `Build/`.

   Is each home and name right, and is the facade wiring right?
6. **Duplication** (`audits/logs/wave1-statements-screen-{before,after}.txt`). The
   population is the new modules' imports plus the designs' named mirror hazards. It goes
   from 540 to 545 pairs. The **5 new pairs are all cross-file**, and none reaches 90%:
   - `CodeSimulator.tableBitsK` is reproduced by the frozen `oneTapeFormat` (85%),
     `codeTable2Bits` (67%) and `Code2TM.serialize` (56%). These are forced, because the
     frozen bodies cannot be redefined, and `tableBitsK_two` proves the equalities. This is
     item 8's pre-named watch item.
   - `CertShell.certificateShell_proj` reproduces `Nondeterminism.lean`'s private
     `certificate_split_strictMono` (83%) and `e3_split_strictMono` (51%). This is the
     disclosed split-uniqueness mirror, a 12.2c item.

   Rule on whether either is a copy that should be factored now, or acknowledged (ledger and
   12.2c). Also, is any proved helper a re-proof of a received lemma? See §12.10's disclosed
   mirrors: W2-0 against two private invariants, and `mem_iff_exists_choiceOut` against
   `choice_certificate_iff`.
7. **Docstrings.** Every new declaration has a docstring and every sorried one a sketch.
   Check them for accuracy against the statements, the design text and the cited rows.
8. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/wave1-statements-replay.log`).
  - **Run:** the five new modules and the facade, at `1a227c8d`, with fresh `.olean`s on a
    snapshot of a tip-consistent tree; the user ran it from the maintainer's command.
  - **Result:** all exit 0 with 0 errors. 26 sorry warnings: `InputLength` 1, `RecordTable`
    20, `CertShell` 1, `OracleSim` 2, `CodeSimulator` 2.
  - **The later tip merge:** the branch then merged the campaign tip `c280727c`. That merge
    changes no new module and not the facade. The tip's changes are proof bodies of the
    imported §12.8 files, with byte-identical statements, so the replay stands.
* **Probes** (`audits/logs/wave1-statements-probes.log`; sources in
  `audits/evidence/wave1-statements/`). All three import the **landed** modules and give 0
  errors.
  - `S128bStatementsProbe`: W1's executed checks, by `decide`.
    - The layout lengths, offsets and closed forms.
    - `TableAt` on concrete tapes with frames just beyond the sentinels.
    - `tableRewindTM` in three instances.
    - Find's `findIdx?` semantics, and append's extension.
    - `posWidth` and `binDigits_posWidth_succ`, and the template at degenerate sizes.
    - R8.5c's witness candidate on seven inputs, with its negative controls.
  - `S1210StatementsProbe`: the consumer derivations above, with axiom prints and a
    sorry-source census. Every cited existing row is sorry-free, except
    `exists_inputCallTM` at the PR's base, which is proved at the current tip since PR #41.
    The negative controls are detected.
  - `B5aStatementsProbe`: the cited declarations, H2 and its proved corollary to H1, and both
    uniform schemes assembled from the contracts. The sorry sources of both instances are
    exactly `exists_polyCanonizer` and `exists_uniformSimulator`.
* **Axioms** (`audits/logs/wave1-statements-axioms.log`). Every public of the five modules is
  printed, 57 in all, and `sorryAx` appears exactly at:
  - the 26 sorried statements;
  - four proved corollaries. The admission walk (`…-admissions.log`) shows that
    `RecordValid.joinFields_length` rests only on `joinFields_cfgRecord_length`, and the
    three OracleSim corollaries only on `exists_plain_simulation`.

  The rest are within `[propext, Classical.choice, Quot.sound]`.
* **Freeze** (`…-freeze.log`). No existing declaration changed. The only existing source
  touched is the facade: imports and Contents bullets.
* **Lint** (`…-stylelint.log`). 0 FAIL, and 15 WARN as at the tip; the new modules add none.
  Sizes: `InputLength` 108 lines, `RecordTable` 769, `CertShell` 109, `OracleSim` 428,
  `CodeSimulator` 237.
* **Inputs.** The bundle attaches:
  - the five new modules, the facade and the design extract;
  - the probes and logs;
  - the files the statements build on: `Build/CfgRecord`, `Build/Seam`, `Build/InputCall`,
    `Build/CounterLoop`, `Build/OracleCall`, `Build/VirtualInput`, `Oracle`, `OracleFinite`,
    `OracleNondeterministic`, `CodeFormat` and `Codes2Tape`;
  - the consumer statements in `ClassOracle/Classes` and `Diagonalization/EXPCOM`;
  - `Build/Catalog`, whose Part 3 rows (the seeks, scan and compare) the §12.8b sketches
    cite. They are now proved, in PR #42.

  `machine-library-design.md` is attached in full, for §12.8a's context.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/wave1-statements-findings.md`.
