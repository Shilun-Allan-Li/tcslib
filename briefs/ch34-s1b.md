# Ch3–4 fill campaign — S1b: the configuration-graph simulation (`NSPACE ⊆ DTIME(2^{O(S)})`, `NL ⊆ P`, Exercise 4.3)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 3ba353460e2d7a877cada66de214dbd3152fe8a7 HEAD`
  succeeds. That commit contains:
  - S1a's four graph lemmas in `SpaceComplexity/ConfigGraph.lean` (proved; epoch C1 + S1a gate closed);
  - the §12.8 rich-alphabet layer, all proved: R8.0 (`SymbolLift`), R8.0b (`counterLoopTMVia`),
    R8.6 (`expandTM_run_ofCfg`), Catalog Part 3, Seam (R8.8), Scan, InputCall and CfgRecord,
    including `exists_recordStepTM`;
  - R8.5c (`exists_inputLengthTM`), proved;
  - the §12.8b table layer (`Build/RecordTable.lean`) at **13/20**: the layout facts and the
    end-to-start adapter proved; its seven deferred rows still sorried (continuation in flight);
  - this round's order list `briefs/orders/ch34-s1b.txt`, base sorry set `audits/logs/ch34-s1b-base-sorries.txt`, screen base
    `audits/logs/ch34-s1b-screen-base.txt` and pre-ship log.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (`fill/ch34-s1b`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-s1b.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| **S1b, the configuration-graph simulation** | `briefs/ch34-s1b.md` | `SpaceComplexity/ConfigGraph.lean` |
| B3a, constructibility | `briefs/ch34-b3a.md` | `SpaceComplexity/Constructible.lean` |
| B4, TQBF membership | issues later, after a pre-issue promotion | `ClassPSPACE/TQBF.lean` (target `TQBF_mem_PSPACE` only) |
| B5b, the `EXPCOM` summit | `briefs/ch34-b5b.md` | `Diagonalization/EXPCOM.lean`, by declaration: the summit, its new privates and imports (the module header is not theirs) |

Also in flight: the §12.10 W2-S continuation (`briefs/w2-fill-oraclesim-cont.md`,
`Build/OracleSim.lean`); the §12.8b record-table continuation
(`briefs/w1-fill-recordtable-cont.md`, `Build/RecordTable.lean`), **which fills the five rows this
brief cites modulo**; the B5a continuation (`briefs/b5a-fill-cont.md`, `CodeSimulator.lean`, plus
status text in `Codes2Tape.lean` and `EXPCOM.lean`); and maintainer PRs touching
`TuringMachine.lean` (the facade), `Build/Embed.lean` (one additive export) and an audit program. A further maintainer PR, B4's pre-issue promotion, will add public CNF-grammar facts to `Formulas/CNFEncoding.lean` and one head-interval lemma to a core file; it is additive.
**Not yours** (the §12.8 A–C files; their fill gate has closed): `Build/Catalog.lean`, `Build/Seam.lean`,
`Build/Scan.lean`, `Build/CfgRecord.lean`, `Build/InputCall.lean`. Cite them; never edit them.
A parallel batch's work is invisible to your base and your screen.

## What this is

**Summit batch S1b** (plan §4e, group B2; split from S1 on 2026-10-10, decision log: "S1a now;
S1b, the summit, after the §12.8 library extension"). The user chose **design A**: a
configuration-level deterministic simulator built on §12 rows, because Savitch, TQBF ∈ PSPACE and
the space hierarchy need the exact contracts only §12 rows carry. §12.8 (design, statements,
gate, fill) and §12.8b (the table rows) are that extension. Fill:
- `Complexity.NSPACE_subset_exp_dtime` ([AB09, Theorem 4.2, third inclusion]): the summit, a
  breadth-first search over configuration records;
- `Complexity.NL_subset_P`: the summit at `logSpace` plus exponent normalization;
- `Complexity.polyTimeReducible_of_mem_NL` ([AB09, Exercise 4.3], hardness only; textbook
  erratum recorded in its docstring).

**The docstrings predate the §12.8 route.** They were written on 2026-10-08 and name the bit codec
`Turing.MultiTapeTM.ConfigCount.coreCode` and "the catalog copy/compare/increment routines and the
loop combinator". The binding machine route is now the **rich-alphabet recomposition** of design
§12.8a §4 with the §12.8b table rows. A flagged **Fill appendix** naming the §12.8 route is
therefore **required** on `NSPACE_subset_exp_dtime`, and on `NL_subset_P` (which routes through the
theorem, see below).

**Proved modulo (exactly):**
- for all three targets: the five §12.8b rows the route uses, `Turing.exists_fieldsCopyTM`,
  `Turing.exists_tableFindTM`, `Turing.exists_tableAppendTM`, `Turing.exists_recordInitTM`, and
  `Turing.exists_recordTemplateTM` **if** you build the outer counter from the template (design
  §12.8a §4 step 5; see "Design decisions" item 5: if you build it from the initial record instead,
  the template drops out of the set; report which);
- additionally, for `NL_subset_P` and `polyTimeReducible_of_mem_NL`:
  `Complexity.spaceConstructible_logSpace` (B3a, parallel).
`Turing.exists_recordValidTM` and `Turing.exists_recordNextTM` are **not** used (they are
Savitch's). Every other cited row is proved.

**Read first:**
- `SpaceComplexity/ConfigGraph.lean` in full (the module docstring's design notes are binding);
- design §12.8 ("S1b's machine plan as a composition of these rows"), §12.8a §4 (the rich
  recomposition, **the route**), §12.8a §§8–9 (decisions O1–O7 and the gate decisions), §12.8b
  ("Layout", "Rows", "Decisions", "Consumers");
- `audits/ch4-p42-findings.md` (rows 67–69; **Question 5**, the exponent ledger; **Question 7**,
  Exercise 4.3) and `audits/ch4-p42-resolutions.md` (minors 4–5, notes 6–7): your **binding audit**;
- `audits/s12-8-statements-resolutions.md` (the row conventions; round-2 note 7) and
  `audits/wave1-statements-resolutions.md` (note 39, binding on this brief; notes 25 and 15);
- `Build/RecordTable.lean`'s five cited statements and `Build/CfgRecord.lean`'s record step,
  equality and test statements;
- `policy.md`; `workflow.md` §4; plan §4e.

**Pre-ship check (maintainer, executed at this brief's ancestor):** re-run at the issue tree (`audits/logs/ch34-wave5-preship.log`): 0 errors, 0 warnings
(`audits/evidence/ch34-wave5/S1bPreShip.lean.txt`: every cited name and every target `#check`ed, under the sanctioned
import added to the target's import set).

## Design decisions settled for this brief

1. **Rich records (decision 12.8.1, user).** The host is a `FinTM Γ` with
   `Γ := Turing.RecSym N.State (Fin 3)` and `e := Turing.RecSym.digitEmb N.State (Fin 3)`. It is
   finished by `Turing.FinTM.alphabet_reduction e` into a `FinTM Bool`.
2. **The tag is the `Fin 3` code of `Turing.OutSummary` (O4, maintainer).** Reuse the file's
   private `sumCode`/`sumCode_injective` (`ConfigGraph.lean:370`, `:376`); do not add a `Fintype
   OutSummary` instance and do not copy the code.
3. **Radius normalization (new at this brief; no binary multiplier row exists).** §12.8b's
   template and initial-record rows take the radius as a digit word `ws` of value `s`. §12.8a §4
   step 3's "the pattern length carries `c₀`" no longer applies. Choose `j` with `c₀ ≤ 2 ^ j` and
   use the radius `r n := 2 ^ j * S n`. Its word is `replicate j false ++ Nat.bits (S n)`, which is
   correct because `S n ≥ logSpace n ≥ 1`. Write it by `Turing.writeConstTM` (j digits `e false`),
   then `Turing.copyTM` of the captured constructor output. Then restate `N.DecidesInSpace L` at
   `fun n => 2 ^ j * S n`, by the three-line argument of `Complexity.NSPACE.mono`'s body; there is
   no public `FinNDTM.DecidesInSpace.mono`. Escalate if this fails.
4. **Input validation (R8.5d) is optional here.** O6 makes it mandatory for rich
   *space*-bounded consumers. This target is a time class, and `alphabet_reduction` quantifies only
   over inputs `x.map e`. Omit it unless it simplifies a phase.
5. **Outer counter and fuel.** Follow §12.8a §4 step 5: copy a record-length word `c_N` times onto
   `Cnt` (the last tape, as `counterLoopTMVia` requires) and map it to `e true` (`Turing.scanTM`
   with `Turing.scanResult_map`). Then `2^{c_N·W} − 1 > V` with
   `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`, using `2^{posWidth n} ≥ n + 2` and
   `8^{2s+1} ≥ 3^{2s+1}(2s+1)`. The word may come from the template (`exists_recordTemplateTM`) or
   from the initial record; report which. Keep **one fuel word** for `exists_tableFindTM` on its own
   digit tape, a copy of `Cnt`'s initial word (§12.8b decision 2). Find restores it, so it is never
   decremented.
6. **No `tableMem` row** (§12.8b decision 5). Membership is S1b's inner `counterLoopTMVia` over the
   table with `Turing.exists_recordEqTM`.

## Owned file and targets (modify this file and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `SpaceComplexity/ConfigGraph.lean:568` | `Complexity.NSPACE_subset_exp_dtime` | BFS over rich configuration records (§12.8a §4 + §12.8b), then `alphabet_reduction` | S1a 1–4; the five §12.8b rows (modulo) |
| 2 | `SpaceComplexity/ConfigGraph.lean:588` | `Complexity.NL_subset_P` | 1 at `logSpace`, then the Q5 normalization and `mem_P_of_dtime_le` | 1; `spaceConstructible_logSpace` (B3a, modulo) |
| 3 | `SpaceComplexity/ConfigGraph.lean:608` | `Complexity.polyTimeReducible_of_mem_NL` | 2, `mem_P_iff`, `polyTimeComputable_ite` over two constants | 2 |

- **Owned:** `SpaceComplexity/ConfigGraph.lean`, for the three targets' bodies, new `private`
  declarations, the sanctioned import, and the sanctioned `InWindow` replacement (ground rule 10).
- **Not yours:** every `Build/*` file, `SymbolLift`, `CounterLoop`, `ConfigCount`, `Constructible`
  (B3a), `TQBF` (B4), `Savitch`, `Hierarchy`, `Logspace/*`, and both facades.
- S1a's proved declarations (`ConfigGraph.lean:112–531`) are frozen, except as ground rule 10
  sanctions.
- **Fill order:** 3, then 2. Both are short, and each is proved modulo the next. Then 1, which is
  the summit.

### Proof routes (binding; the docstrings' sketches, the P4.2 audit, and design §12.8a §4 / §12.8b)

**Target 3, Exercise 4.3** (findings Q7).
1. Choose `y₀ ∈ L` and `z₀ ∉ L` classically.
2. `Complexity.mem_P_iff` on `NL_subset_P hL'` gives `C d M` with
   `M.DecidesInTime L' (C·(n+1)^d)`, which is literally
   `PolyTimeComputable (fun x => [MultiTapeTM.indicator L' x])`.
3. Let `f x := if MultiTapeTM.indicator L' x then y₀ else z₀`. It is polynomial-time by
   `Complexity.polyTimeComputable_ite` with two `Complexity.polyTimeComputable_const`.
4. The equivalence follows by cases on membership. The reduction never decides `L`.

**Target 2, `NL ⊆ P`.**
- `NL = NSPACE logSpace`. Apply target 1 at `S := logSpace` with
  `Complexity.spaceConstructible_logSpace` (the auditor's route, findings row 68).
- For each component `c`, use the Q5 chain (findings :181–192):
  `2^{c(logSpace n + 1)} = 2^{2c}·(2^{Nat.log 2 n})^c ≤ 2^{2c}(n+1)^c ≤ 2^{3c}(n^c + 1)`. It uses
  `2^{Nat.log 2 n} ≤ n + 1` (`Nat.pow_log_le_self`; `n = 0` separately) and `n + 1 ≤ 2n` for
  `n ≥ 1`.
- Conclude with `Complexity.mem_P_of_dtime_le`.
- **Minor 4:** the appendix must not call `LOGSPACE_subset_P` the deterministic special case of
  the search; the shared ingredient is only the count arithmetic.

**Target 1, the summit.** Design §12.8a §4, steps 1–10, with these §12.8b substitutions.

- **A. Data.**
  - `rintro L ⟨c₀, N, hN⟩`.
  - Unpack `hS = ⟨hdom, a, ha, M_S, hMS⟩`.
  - Normalize the radius (decision 3).
  - Membership is `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` at
    `r` with `Turing.NDTM.reflTransGen_cfgStep_iff`.
- **B. The radius phase.**
  - Run `M_S.tm.liftSymbols e` under `Turing.embedSilentRetTM` with its output captured on a
    digit tape, then rewind the native input (`Turing.FinTM.timed_rewind`, lifted).
  - Time: `Turing.FinTM.ComputesInTime.of_spaceUsed_le` bounds `M_S`'s halting time by
    `M_S.configBound n (a·S n)`, transported by `Turing.MultiTapeTM.liftSymbols_runFrom`. This is
    received and deterministic, so not circular (**note 7**).
  - Then write the radius word (decision 3).
- **C. The initial table.**
  - A fixed nonempty header, then `Turing.exists_recordInitTM` at `q₀ := N.tm.q₀` and
    `τ₀ := sumCode (outSummary [])`, then the flag field `[e false]` ("unprocessed").
  - Every entry has `m := k + 4` fields: the record's `k + 3`, then the flag.
  - The layout is `Turing.TableAt`/`Turing.TableWF` (two blanks before the header and after the
    last field; §12.8a §9 decision 2).
- **D. Counter and fuel** (decision 5).
- **E. The round** (the `counterLoopTMVia e Round a (some ex)` body, both exits wired by R8.8
  `Turing.seamCompTM₂_run_ofCfg`, or the phase host `Turing.phaseHostTM`):
  1. `Turing.exists_tableFindTM e m` with `δ` reading the flag field. On `no`, escape to `ex`.
  2. On `yes` (head at the entry): copy the entry's first `k + 3` fields to `Cur₀` and `Cur₁`
     (`Turing.exists_fieldsCopyTM (k+3)`).
  3. **Note 39:** set the flag **while its location is known**. Skip the `k + 3` record fields
     (`Turing.skipTM_run_ofCfg`), write `[e true]` (`Turing.writeConstTM_run_ofCfg`), and skip
     back. Then `Turing.tableRewindTM_run_ofCfg` to the origin **before** any table-wide find or
     append.
  4. Run `Turing.exists_recordStepTM` at `N.tm.fixChoice false` on `Cur₀` and at
     `N.tm.fixChoice true` on `Cur₁` (`Turing.NDTM.stepWith_eq_fixChoice_step`). The tag update is
     the summary's append table on the `Fin 3` code (`Turing.outSummary_append_congr`). A `no`
     verdict means the successor leaves the window: no edge (note 6).
  5. For each `yes`: membership by an inner `counterLoopTMVia` over the entries with
     `Turing.exists_recordEqTM`. If the successor is absent, append it with
     `Turing.exists_tableAppendTM (k+3) [[e false]]`. The appended fields are nonempty, so
     `TableWF` is preserved (**note 25 / round-2 note 15**).
  6. Clear `Cur₀`/`Cur₁` and the scratch (`Turing.clearTM_run_ofCfg`), rewind the table, and
     return to the anchor.
- **F. Verdict.**
  - `Turing.exists_tableFindTM` with `δ` reading the state field (field 0) and the tag field
    (field `k + 2`), and `acc := state = st none ∧ tag = sumCode accept`.
  - Emit `e true`/`e false` and halt. The emitting halt must be forwarded before the control dies:
    the R1 "final emission" lesson (`vhostEmitTM_emitting_halt` is the positive precedent).
- **G. Correctness** (the BFS invariant, then **note 6 verbatim**). Records are identified with
  `coreSum`s by `Turing.cfgRecord_inj` at `T := Fin 3` with `sumCode_injective`. The bridge must
  cover:
  - canonical decoding;
  - outside-window edge rejection, which is `recordStepTM`'s `no`;
  - quotient path lifting from the **true initial configuration**;
  - enumeration of **all** accepting vertices: the verdict find, with no unique-target assumption;
  - the reflexive base case of bounded reachability.

  Then S1a's four lemmas finish. `Turing.Cfg.InWindow` is CfgRecord's window predicate, which
  ground rule 10 aligns with S1a's.
- **H. Time.**
  - `Turing.counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
    nested membership loop.
  - Add the constructor bound and the startup terms, then `alphabet_reduction`'s `c(T+1)`.
  - Everything is at most `K·2^{c'(S n + 1)}`, by the **`S`-generalized configuration-count
    arithmetic** (below) and `n + 2 ≤ 2^{S n + 1}`, from `hdom` (Q5). Every budget is evaluated at
    `n`; **no monotonicity of `S`**.
  - **Minor 5:** the `+ 1`'s job is the input-head absorption, not positivity of the exponent.
- **The `S`-generalized count is an in-file private obligation.** Write **one formula-level
  private lemma**: `(q+1)(n+2)·3^{k(2s+1)}(2s+1)^k ≤ 2^{…}` at `s = r n`, given `logSpace ≤ S`.
  Instantiate it twice:
  - at `Turing.FinTM.configBound`, for the constructor;
  - at `Turing.FinNDTM.configBound` (three times the formula), for the vertex count.

  Derive it from the Q5 ledger (`3 ≤ 2²`, `2s+1 ≤ 2^{s+1}`, `n + 2 ≤ 2^{S n + 1}`). **Do not
  transcribe** `Turing.FinTM.configBound_logSpace_le`'s proof (duplication governance).

## Gate guidance (binding)

- **P4.2 minors 4–5** (above): keep the swept prose true in every appendix.
- **P4.2 note 6** (the carrier bridge): the five obligations in step G, verbatim in your appendix.
- **P4.2 note 7** (the resource ledgers):
  - the constructor's exponential time comes through the received
    `ComputesInTime.of_spaceUsed_le`;
  - the ledger counts constructor execution and every table operation, under sequential access,
    with no unit-cost lookup (the auditor's banked BFS ledger, findings Q5).
- **§12.8 statement gate, round-2 note 7:** intercept every verdict. The contracts bound nothing
  after a module's own verdict or exit. Redirect at each sub-module's exit time; never run a
  sub-module past it.
- **Wave-1 note 39:** the flag/rewind bookkeeping of step E.3, explicitly in the appendix.
- **Wave-1 note 25 / round-2 note 15:** append only nonempty fields when a later seek follows.
- **R1 isolation of dedicated digit tapes** (wave-1 statement gate, round-1 note 32 and round-2
  notes 31–32): never apply `liftSymbols_runFrom` to a configuration with a foreign symbol on a
  selected tape. The overlay transport (`Turing.MultiTapeTM.liftSymbols_runFrom_over`) is the
  alternative for input-oblivious rows.
- **Input convention** (§12.8b decision 7): the rows that read the native input
  (`exists_recordInitTM`, `exists_recordTemplateTM`) enter at position `1` and restore it.
  `recordStepTM` saves and restores an arbitrary position.
- **No termination hypothesis:** each contract supplies its finite `t`.

## Cited infrastructure (public and proved at the issue commit)

- **S1a (this file):** `Turing.NDTM.CfgStep`, `Turing.NDTM.coreSum`,
  `Turing.NDTM.reflTransGen_cfgStep_iff`, `Turing.NDTM.coreSum_stepWith`,
  `Turing.NDTM.coreSum_runWith`, `Turing.FinNDTM.configBound`,
  `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le`,
  `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound`,
  `Turing.FinNDTM.not_acceptsWithin_zero`, `Turing.OutSummary`, `Turing.outSummary`,
  `Turing.outSummary_eq_accept_iff`, `Turing.outSummary_append_congr`.
- **Classes and counts:** `Complexity.NSPACE`, `Complexity.NSPACE.mono`, `Complexity.NL`,
  `Complexity.DTIME`, `Complexity.DTIME.mono`, `Complexity.P`, `Complexity.mem_P_iff`,
  `Complexity.mem_P_of_dtime_le`, `Complexity.SpaceConstructible`, `Complexity.logSpace`,
  `Complexity.PolyTimeComputable`, `Complexity.PolyTimeReducible`, `Complexity.polyTimeComputable_ite`,
  `Complexity.polyTimeComputable_const`, `Turing.FinNDTM.DecidesInSpace`, `Turing.FinNDTM.AcceptsWithin`
  (`.mono`), `Turing.FinTM.DecidesInTime`, `Turing.FinTM.ComputesInSpace`, `Turing.MultiTapeTM.indicator`,
  `Turing.FinTM.ComputesInTime.of_spaceUsed_le`, `Turing.FinTM.configBound`,
  `Turing.FinTM.configBound_logSpace_le` (the template for the arithmetic, not to be transcribed),
  `Turing.MultiTapeTM.ConfigCount.coreCode`, `Turing.MultiTapeTM.ConfigCount.coreCode_inj`.
- **Nondeterminism:** `Turing.NDTM.fixChoice`, `Turing.NDTM.stepWith_eq_fixChoice_step`.
- **CfgRecord (R8.7):** `Turing.RecSym`, `Turing.RecSym.digitEmb`, `Turing.recSymFintype`,
  `Turing.binDigits`, `Turing.posWidth`, `Turing.cfgRecord`, `Turing.cfgRecord_length`,
  `Turing.cfgRecord_inj`, `Turing.RecordValid`, `Turing.recordValid_iff`, `Turing.RecordAt`,
  `Turing.Cfg.InWindow`, `Turing.exists_recordStepTM`, `Turing.exists_recordEqTM`,
  `Turing.exists_recordTestTM`.
- **RecordTable (proved part):** `Turing.recordLength`, `Turing.recordTemplate`, `Turing.cfgRecord_init`,
  `Turing.joinFields_cfgRecord_length`, `Turing.cfgRecord_field_ne_nil`, `Turing.tableFields`,
  `Turing.tableOffset`, `Turing.TableWF`, `Turing.TableAt`, `Turing.TableWF.field_ne_nil`,
  `Turing.tableOffset_eq`, `Turing.tableOffset_length`, `Turing.TableAt.recordAt_take`,
  `Turing.tableRewindTM`, `Turing.tableRewindTM_run_ofCfg`.
- **RecordTable (proved modulo, statements frozen by the closed wave-1 gate):**
  `Turing.exists_fieldsCopyTM`, `Turing.exists_tableFindTM`, `Turing.exists_tableAppendTM`,
  `Turing.exists_recordInitTM`, `Turing.exists_recordTemplateTM` (decision 5).
- **CounterLoop (R8.0b, R8.6):** `Turing.counterLoopTM`, `Turing.counterLoopTMVia`, `Turing.lastEmb`,
  `Turing.counterLoopTMVia_run_done`, `Turing.counterLoopTMVia_run_escape`, `Turing.counterLoop_time_le`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit`, `Turing.counterWord`, `Turing.counterWord_value`,
  `Turing.counterOverhead`, `Turing.counterOverhead_le`, `Turing.counterOverhead_le_of_le`,
  `Turing.expandTM`, `Turing.expandTM_run_ofCfg`.
- **Catalog (Part 1 and Part 3):** `Turing.joinFields`, `Turing.fieldsTape`, `Turing.fieldOffset`,
  `Turing.fieldsTape_field`, `Turing.copyTM`/`_run_ofCfg`, `Turing.clearTM`/`_run_ofCfg`,
  `Turing.skipTM`/`_run_ofCfg`, `Turing.skipBackTM`/`_run_ofCfg`, `Turing.seekEndTM`/`_run_ofCfg`,
  `Turing.seekStartTM`/`_run_ofCfg`, `Turing.scanTM`/`_run_ofCfg`, `Turing.scanResult_map`,
  `Turing.scanResult_fold`, `Turing.incrementTM`, `Turing.incrementTM_run_succ_ofCfg`.
- **Scan:** `Turing.writeConstTM`/`_run_ofCfg`, `Turing.writeAdvTM`/`_run_ofCfg`,
  `Turing.inputFoldTM`/`_run_ofCfg` (only if you validate; decision 4).
- **Seam (R2, R8.8, phase host):** `Turing.seamCompTM`, `Turing.seamCompTM_run_ofCfg`,
  `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.seamCompTM_visitedByTapeHead_ofCfg`,
  `Turing.seamCompTM₂`, `Turing.seamCompTM₂_run_ofCfg`, `Turing.seamReleaseTM`,
  `Turing.seamReleaseTM_firstReturn`, `Turing.phaseHostTM`, `Turing.phaseHostTM_run`.
- **R1 and transport:** `Turing.embedSilentRetTM`, `Turing.embedSilentRetTM_run`, `Turing.embedEmitTM`,
  `Turing.embedEmitTM_runFrom`, `Turing.embedEmitTM_frame`, `Turing.embedEmitCfg_selected_tape`/`_pos`,
  `Turing.MultiTapeTM.liftSymbols`, `Turing.MultiTapeTM.liftSymbols_runFrom`,
  `Turing.MultiTapeTM.liftSymbols_initCfg`, `Turing.MultiTapeTM.liftSymbols_runFrom_over`,
  `Turing.FinTM.bufferTape`, `Turing.FinTM.bufferTape_map`, `Turing.FinTM.bufferTape_map_decode`,
  `Turing.FinTM.timed_rewind`.
- **Finish:** `Turing.FinTM.alphabet_reduction`, `Turing.FinTM.ComputesFunInTimeVia`.
- **Do not cite:**
  - `exists_recordValidTM` or `exists_recordNextTM` (Savitch's; not on this route);
  - `alphabet_reduction_spaceUsed` (a space finish, not needed here);
  - anything in `ClassPSPACE`, `Savitch`, `Hierarchy` or `Logspace/*`.

## Ground rules (binding)

1. **File ownership.** Only `SpaceComplexity/ConfigGraph.lean`. Change only the three targets'
   bodies, and add new `private` helpers there. List every new declaration with its role. A lemma
   that genuinely belongs in a shared file is written privately, flagged in `REPORT.md` as a
   promotion candidate, and promoted by the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay. A flagged
   **"Fill appendix"** is **required** on targets 1 and 2 (the route post-dates their sketches), and
   expected wherever else your proof refines a sketch's route.
3. **Status text.** Only your file's status text may change: the module's "Status" paragraph
   ("the three class results remain sorried for S1b") and its "Main results" heading, each to
   "proved" (or "proved modulo …", naming the set). Flag each. No new public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest. A §12.8b row whose frozen statement does not fit the route is an escalation to the
   maintainer, never a local workaround.
5. **No touching other sorries.** Cite proved material; never re-prove it. The five §12.8b rows and
   `spaceConstructible_logSpace` are cited, never filled here.
6. **Imports.** **Sanctioned addition, exactly:** `import TCSlib.Complexity.TuringMachine.Build.RecordTable`.
   It brings `CfgRecord`, `CounterLoop`, `Seam`, `Embed`, `InputLength`, `InputCall`, `Scan`,
   `Catalog` and `SymbolLift`. `Robustness/AlphabetReduction` is already in the file's closure. It
   is acyclic at the issue tree: no module in its closure imports any `SpaceComplexity` module
   (maintainer-checked by reading the import lines). Flag it. No other TCSlib import may be added.
   A Mathlib import is allowed only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts.
9. **Continuation budget** (anticipated in the docstring: "continuation budget anticipated"). If
   your budget runs out, deliver a partial zip whose `REPORT.md` states which targets are proved,
   which `private` helpers remain `sorry` (each with a literal "Proof sketch"), and which proved
   targets are proved modulo them. A partial is expected and fine; an unreported gap is not.
10. **Sanctioned replacement (D4-style): the private `InWindow`.**
    - **What:** `InWindow` (`ConfigGraph.lean:143`, private) may be **deleted** and replaced by the
      public `Turing.Cfg.InWindow` (`Build/CfgRecord.lean:100`).
    - **Why it is sound:** the two are logically equivalent on this file's carrier. The private one
      is `∀ i, |pos i| ≤ s ∧ ∀ z, cell i z ≠ none → |z| ≤ s`; the public one is
      `(∀ i, |pos i| ≤ s) ∧ ∀ i z, s < |z| → cell i z = none`. They agree by `forall_and` plus
      contraposition. The universes also match: the file's `S : Type` (`:92`) meets
      `Cfg.InWindow`'s `{Symbol State : Type}`.
    - **Not definitional:** `runWith_take_inWindow` (`:302`), `inWindow_of_coreSum_eq` (`:322`),
      `count_windowed_vertices` (`:386`) and the **body** of `acceptsWithin_of_spaceUsedWith_le`
      (`:445`) must be restated over it. Their statements stay unchanged apart from the predicate;
      `acceptsWithin_of_spaceUsedWith_le`'s statement is byte-identical.
    - **The bridge:** add one private bridge to the hypothesis form of
      `MultiTapeTM.ConfigCount.coreCode_inj`.
    - **Fallback:** if the replacement costs more than it saves, keep the private predicate and add
      a single private `iff` with `Cfg.InWindow` instead.
    - **Either way:** list the change, and note the effect on the screen (the pair against
      `Cfg.InWindow` disappears or remains).

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/ch34-s1b-screen-base.txt`: **1,175 declarations, 761 pairs, 273,131 characters**.

Population (`audits/evidence/ch34-wave5/ch34-s1b-screen-population.txt`): the owned file, every
file a route reuses, and every duplication hazard.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean \
  TCSlib/Complexity/SpaceComplexity/NSPACE.lean \
  TCSlib/Complexity/SpaceComplexity/Constructible.lean \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean \
  TCSlib/Complexity/SpaceComplexity/Savitch.lean \
  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean \
  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean \
  TCSlib/Complexity/ClassPSPACE/TQBF.lean \
  TCSlib/Complexity/ClassNP/NTIME.lean \
  TCSlib/Complexity/ClassNP/PolyTimePairing.lean \
  TCSlib/Complexity/ClassP/P.lean \
  TCSlib/Complexity/ClassP/DTIME.lean \
  TCSlib/Complexity/ClassP/TimeConstructible.lean \
  TCSlib/Complexity/TuringMachine/Nondeterministic.lean \
  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean \
  TCSlib/Complexity/TuringMachine/SymbolLift.lean \
  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean \
  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/Scan.lean \
  TCSlib/Complexity/TuringMachine/Build/InputCall.lean \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Loop.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it). **Pre-disclosed:** none.
- **Known hazards:**
  - `Turing.FinTM.configBound_logSpace_le` (ConfigCount) against your `S`-generalized count. Derive
    it from the Q5 ledger. If a pair of 90% or more still arises, report it as a promotion
    candidate: the maintainer re-derives the `logSpace` instance from yours.
  - CfgRecord's private record-step helpers, InputCall's private seek helpers, RecordTable's
    privates (`rt_copyMachine` and the continuation's helpers) and Catalog's `f2_*` hosts: never
    copy them.
  - A second loop host, forward scanner or table walker: the outer and inner loops run under
    `counterLoopTMVia`, and find and append are the §12.8b rows.
  - TQBF's codec (`exists_adjacency_codec_cnf`, its window/adjacency helpers): never copy it.
  - S1a's own privates (`sumCode`, the visited-set lemmas, `splice_vertices`): reuse them in place.
- **Savitch promotion candidates (flag them; do not make them public).** Savitch (B3, a later
  batch) needs the same three pieces:
  - the **radius phase** (constructor capture, its time bound, the radius normalization);
  - the **note-6 bridge** (records ↔ `coreSum` ↔ choice-word runs, outside-window rejection, path
    lifting from the true initial configuration);
  - the **`S`-generalized configuration-count arithmetic**.

  Write each as a self-contained `private` helper with a docstring, and list it in `REPORT.md` as a
  promotion candidate, so that Savitch can cite it after maintainer promotion instead of copying
  it.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-s1b.txt` (**114 modules**: the upstream closure of
  your owned file, including the sanctioned import, and every module downstream of it, at the issue
  tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-s1b.txt )
  ```

  **Base sorry-warning set, 27** (`audits/logs/ch34-s1b-base-sorries.txt`, one entry per declaration). Yours:
  `SpaceComplexity/ConfigGraph` 3. Record the base list by name first. If anything else has landed
  by your base (a parallel batch, or the record-table continuation), report the difference.
- **Final checks:**
  1. Your owned module: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours. The new import enlarges the closure of every downstream module (`TQBF`,
     `Hierarchy`, `Logspace/Path`, `Savitch` and the `SpaceComplexity` facade), so they must all
     still elaborate. A name clash there is an escalation, not a rename.
  3. Re-run the pre-ship probe `audits/evidence/ch34-wave5/S1bPreShip.lean.txt` (copied to a scratch `.lean` path): 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through the named proved-modulo citations. Target 1 prints it only through the
  §12.8b rows; targets 2 and 3 also through `spaceConstructible_logSpace`. Report which §12.8b rows
  actually occur.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `SpaceComplexity/Constructible`: spaceConstructible_logSpace, spaceConstructible_linear
- `TuringMachine/Build/RecordTable`: exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `ClassPSPACE/TQBF`: TQBF_mem_PSPACE, TQBF_PSPACEHard, TQBF_PSPACEComplete
- `SpaceComplexity/Savitch`: spaceConstructible_poly, savitch, PSPACE_eq_NPSPACE
- `SpaceComplexity/Hierarchy`: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
- `SpaceComplexity/Logspace/Path`: PATH_mem_NL, PATH_NLComplete
- `SpaceComplexity/Logspace/ImmermanSzelepcsenyi`: compl_PATH_mem_NL, NL_eq_coNL, NSPACE_compl_eq

(The base set minus the three targets. Note in particular: the seven `Build/RecordTable` rows,
which the continuation is filling and five of which you cite; `Constructible`'s two targets, which
are B3a's and one of which you cite; `TQBF`, `Savitch`, `Hierarchy`, `Path` and
`ImmermanSzelepcsenyi` downstream.)

If a proof seems to *need* one of these beyond the named citations, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 3/3, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and the import;
      the ground-rule-10 change (replacement or bridge), listed.
- [ ] The proved-modulo set exactly as the axiom prints show it, and the template's use (decision 5).
- [ ] Requested shared lemmas, escalations and **promotion candidates** (the three Savitch pieces at
      least), or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned file.
- [ ] Sanity cases, executed or proved as lemmas in your evidence:
  - the empty input;
  - a zero-work-tape `N` (`k = 0`: records with no window field);
  - a machine whose first step halts accepting;
  - a machine that never accepts (the verdict find answers `no`).

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Γ S x)`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `Nat.bits` is little-endian. `Nat.bits (2 ^ j * m) = List.replicate j false ++ Nat.bits m` holds
  only for `m > 0`, which is why decision 3 needs `S n ≥ 1`.
- `Turing.OutSummary` derives only `DecidableEq`, so `RecSym _ OutSummary` is not `Fintype`: use
  the `Fin 3` code (decision 2). `recSymFintype` needs `[Fintype Q] [Fintype T]`.
- `ComputesFunInTimeVia e f T` quantifies over inputs `x.map e` and outputs `(f x).map e`. The host
  reads digits, never `Bool`.
- `exists_tableFindTM` needs:
  - `0 < m`;
  - `TableWF`;
  - fuel value `> |es|`;
  - tapes `≥ 2` blank.

  Its `yes` leaves the head at `o + tableOffset h es j`; its `no` leaves everything unchanged.
- `counterLoopTMVia`'s counter is the last tape. `counterWord` freezes at zero while the machine
  wraps: stay at `r ≤ value + 1`. `counterLoopCfg` ignores the body configuration's state.
- `embedEmitCfg`'s output is `pre ++ c.output`. Start every lifted `Bool` configuration with
  output `[]` and `pre :=` the host's output.
- `phaseHostTM` takes its start state `q0` explicitly. A composite `FinTM` whose real entry is a
  module's `entry` state sets `q₀` there: `runFrom` ignores `q₀`, but `initCfg` uses it. Its states
  `Σ i, Ph i` need `[Fintype I]` and `[∀ i, Fintype (Ph i)]`, and `DecidableEq` likewise.
  `FinTM` wants `State : Type`.
- `simp` unfolds a machine's definition inside `counterLoopOrbit M …` arguments too, so terms
  stop matching. `generalize counterLoopOrbit M τ c r = o at …` first.
- `RecordAt`/`TableAt` constrain only the stated interval around the origin. A field's own
  delimiters come from `fieldsTape_field` and the span bound, never from cells beyond the layout.
