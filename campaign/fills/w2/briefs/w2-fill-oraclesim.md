# Ch3–4 fill campaign — wave-1 fill: §12.10 oracle-call simulation, W2-S and W2-C (`Build/OracleSim.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`);
  - R8.0b (`counterLoopTMVia`, PR #38) and R8.6 (`expandTM_run_ofCfg`), both proved;
  - the §12.8 Catalog Part 3, Scan, InputCall and Seam rows, all proved;
  - this round's order lists, base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/w2-oraclesim`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-w2-oraclesim.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| R8.5c, the input length | `briefs/w1-fill-inputlength.md` | `TuringMachine/Build/InputLength.lean` |
| §12.8b record tables | `briefs/w1-fill-recordtable.md` | `TuringMachine/Build/RecordTable.lean` |
| §12.10 W2-S and W2-C | `briefs/w2-fill-oraclesim.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.10 W2-V | `briefs/w2-fill-certshell.md` | `TuringMachine/Build/CertShell.lean` |
| B5a, the code simulator | `briefs/b5a-fill.md` | `TuringMachine/CodeSimulator.lean`, `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean` |
| The ND code scheme | `briefs/ndcodes-fill.md` | `TuringMachine/NDCodes.lean` |
| B4a, the TQBF codec | `briefs/b4a-fill-codec.md` | `ClassPSPACE/TQBF.lean` (one target) |

Also in flight: §12.8 C continuation 3 (`Build/CfgRecord.lean`), B7 continuation 3
(`Logspace/QueryReshape.lean`, `Logspace/Reductions.lean`) and the B7 multiplication batch
(`Logspace/Mult.lean`); and a maintainer PR filling `POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`) and `baker_gill_solovay` (`Diagonalization/Relativization.lean`).
A parallel batch's work is invisible to your base and your screen.

## What this is

Fill the two sorried rows of the **oracle-call simulation layer** (`machine-library-design.md`
§12.10, design W2; statements audited true at the wave-1 statement gate):
- **W2-S**, `FinOracleTM.exists_plain_simulation`: from any preloaded start, a plain host
  reproduces an oracle machine's halting output, answering each query by a clean call of a
  decider, within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(|query_r|)`;
- **W2-C**, `FinOracleNDTM.exists_choiceTM`: the choice-word machine that determinizes an oracle
  NDTM along a word on a work tape, within `2|u| + 2` steps.

They unblock B1's last target `POracle_eq_P_of_mem_P` (filled by the maintainer, proved modulo
W2-S), and B5's summit `NPOracle_EXPCOM_subset_EXP`.

**Read first:** `Build/OracleSim.lean` in full (both sketches are binding); design §12.10; the
wave-1 findings rounds 1–2 and resolutions; `Oracle.lean`, `OracleNondeterministic.lean`,
`Build/OracleCall.lean`; `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w3-preship.log`): 0 errors; output identical to round 2's. It derives every
consumer from the two rows and runs the reuse census: every row the routes cite prints `[]`.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/OracleSim.lean:212` | `Turing.FinOracleTM.exists_plain_simulation` | the dispatch host (W2-S) | — |
| 2 | `TuringMachine/Build/OracleSim.lean:398` | `Turing.FinOracleNDTM.exists_choiceTM` | lockstep by induction on `u` (W2-C) | — |

- **Owned:** `TuringMachine/Build/OracleSim.lean`, for the two targets' bodies and new `private` declarations.
- **Not yours:** `Build/CertShell.lean` (parallel batch, W2-V), `Oracle.lean`, `OracleNondeterministic.lean`, `Build/OracleCall.lean`, `ClassOracle/*`, and the facade.

### Proof routes (binding; the docstrings' sketches, amplified)

- **W2-S, the dispatch host.** Tapes: the source's `k + 1` tapes first; a **shadow tape** whose
  head mirrors the query head, with an origin marker written on the first step; the bank of the
  install-mode clean call `C := Turing.FinTM.exists_installCallTM D (fun z => [χ_O z]) τ hD`,
  hosted by Z1 at the **empty** virtual input (`vhostEmitTM_runFrom` with `y = []`) and relocated
  by R1; a scratch tape carrying the saved cell `-1` and the side bit across the seams.
  - (i) **Off `qQuery`**, one host step per source step: the host table agrees on simulated
    states with the shadowed transport of `M.tm.plainEmptyOracle`, so the bridge
    `OracleTM.runFrom_eq_plainEmptyOracle` and Z5 (`MultiTapeTM.runFrom_eq_of_agreeOn`) carry
    `M`'s run.
  - (ii) **At `qQuery`**, nine R2-seamed phases (`seamCompTM_run_ofCfg`, `seamReleaseTM`):
    bookmark the shadow cell; walk to the origin by the side; save and blank cell `-1`; copy the
    delimited query to `C`'s argument tape (`copyTM_run_ofCfg`, `OracleTM.queryString_eq_of_cells`);
    run `C`; read and clear the verdict; restore cell `-1`; walk back and erase the bookmark;
    enter the embedded `M.qYes`/`M.qNo` (`OracleTM.step_of_qQuery`).
  - (iii) **Ledger:** from a blank query tape the query at step `r` has length at most `r`
    (W2-0, `OracleTM.queryString_runFrom_length_le_of_blank`), the query head is within `r` of
    the origin, each query costs `a·(t + 1) + a·τ |z|`, and there are at most `t` of them. The
    host halts exactly when `M` does; first-halt cuts by `MultiTapeTM.exists_first_halt`.
- **W2-C.** States `N.State ⊕ Fin 3`; tapes `N`'s ordinary tapes, the choice tape, then `N`'s
  query tape last (shared verbatim). Lockstep by induction on `u` in the
  `OracleTM.toOracleNDTM_runWith` shape, with `OracleTM.step_of_qQuery` against `stepWith` at the
  query state; a blank choice cell emits `false` and halts (`OracleTM.answerAction false`). Per
  **minor 4**, at exhaustion on `N`'s query state the host may submit that query and discard its
  answer: the contract is the I/O statement, not the query trace.

## Gate guidance (binding)

- **Decisions (user, 2026-10-11).** One oracle-call trace (the deterministic row); nondeterminism
  by choice words, never a branchwise row; W2-S in preloaded generality (`initCfg` derived);
  **time only** — the oracle model has no space measure, so add no space clause (note 45).
- **Virtual input stays at the plain level**, after the simulation: an oracle-level Z1 would
  re-prove Z1's lockstep.
- **Note 50:** permanent sanity case **at fill**: query-word exhaustion for W2-C, as an
  executed example in your evidence.
- **Mirrors, factored** (user decision, round 2): W2-0 and the oracle run invariants already
  specialize the public `OracleTM.step_radius`/`runFrom_radius`; cite them, never restate them.

## Cited infrastructure (public and proved at the issue commit)

- `Oracle.lean`: the run algebra, `step_of_qQuery`, `step_eq_of_ne_qQuery`, `queryString_eq_of_cells`,
  `runFrom_eq_plainEmptyOracle`, `step_radius`, `runFrom_radius`; `OracleNondeterministic.lean`:
  `toOracleNDTM_runWith`, `stepWith`, `fixChoice`; `Build/OracleCall.lean`: `answerAction` and the
  query tail.
- `FinTM.exists_installCallTM` (Loop), `vhostEmitTM`, `vhostEmitTM_runFrom` (Z1), R1 and R2
  (Embed, Seam), `copyTM_run_ofCfg`, `clearTM_run_ofCfg` (Catalog), `MultiTapeTM.runFrom_eq_of_agreeOn`,
  `exists_first_halt`, `FinTM.prefixWords` and its lemmas, `Cfg.init_eq_ofWords`, W2-0.
- **Proved modulo: none.**

## Ground rules (binding)

1. **File ownership.** Only `Build/OracleSim.lean`. Change only the two targets' bodies, and add new `private` helpers
   there. List every new declaration with its role. A lemma that genuinely belongs in a shared
   file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by
   the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your files' status text may change: the module's "Status" paragraph,
   its "Main results" tag, and your targets' "(statement)"/"(spec, fill pending …)" tags, each to
   "proved" (or to the new count, for a file you share with later targets); flag each. No new
   public declaration unless this brief names it.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
   it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report each owned
   file's final line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/w1-fill-screen-base.txt`:
**1,331 declarations, 1,717 pairs, 574,720 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean \
  TCSlib/Complexity/TuringMachine/Build/CertShell.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean \
  TCSlib/Complexity/TuringMachine/CodeSimulator.lean \
  TCSlib/Complexity/TuringMachine/ChoiceWords.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/InputCall.lean \
  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean \
  TCSlib/Complexity/TuringMachine/Oracle.lean \
  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean \
  TCSlib/Complexity/ClassNP/Nondeterminism.lean \
  TCSlib/Complexity/TuringMachine/CodeFormat.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
  TCSlib/Complexity/ClassP/DTIME.lean \
  TCSlib/Complexity/TuringMachine/Universal.lean \
  TCSlib/Complexity/TuringMachine/UniversalBlock.lean \
  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean \
  TCSlib/Complexity/TuringMachine/UniversalStartup.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - a second oracle-call trace, a branchwise simulation, or an oracle-level Z1 (decisions above);
  - the off-query lockstep against Z5 and the bridge: cite them;
  - the query extraction against `Build/OracleCall`'s capture and B1's private oracle helpers (`ClassOracle/*`): never copy them;
  - W2-C's induction against `toOracleNDTM_runWith`'s: cite its shape, do not restate it.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/w1-fill.txt` (**55 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/w1-fill.txt )
  ```

  **Base sorry-warning set, 28** (`audits/logs/w1-fill-base-sorries.txt`, one entry per declaration).
  Yours: `Build/OracleSim` 2. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**26** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `TuringMachine/NDCodes`: exists_effectiveNDMachineCode
- `TuringMachine/Build/InputLength`: exists_inputLengthTM
- `TuringMachine/Build/RecordTable`: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/Build/CertShell`: FinTM.exists_certificateShell
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 2/2, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] Note 50: the W2-C exhaustion example, executed.

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare lifted positions by `.val`.
- A halted source has `M.step c = c` and `M.outputSymbol c = none` (`step_of_halt`,
  `outputSymbol_of_halt`).
- `seamCompTM_firstReturn_ofCfg` needs the callee's cut at `t = 0` as well;
  `exists_installCallTM` gives it only for `0 < t`.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `decide` cannot evaluate `Nat.bits`/`Nat.size`, hence `posWidth`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them); `nlinarith` is
  rarely needed. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
- `OracleTM.runFrom` takes the oracle `O` explicitly; a plain machine's `runFrom` does not.
  The bridge `runFrom_eq_plainEmptyOracle` is the link off `qQuery`.
- Oracle answers are classical: use `simp only [this, decide_eq_true_eq]`; `rw` fails inside
  `ite` (motive not type correct).
