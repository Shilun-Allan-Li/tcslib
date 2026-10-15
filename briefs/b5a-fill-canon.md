# Ch3–4 fill campaign — B5a, the polynomial canonizer (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 13957bf73eb37763259be1fd01a5cca9bd03c21f HEAD`
  succeeds. That commit contains:
  - the previous continuations of this round's three batches and their reports (`audits/wave1-fill-agent-reports/{oraclesim,recordtable}-2-REPORT.md`, `audits/b5a-fill-agent-reports/cont-1-REPORT.md`), with the integration record `audits/fills-5-integration.md`;
  - the `exists_tableFindTM` universe fix (`Γ : Type`, user option (b), flagged in its docstring) and the 12.2c T2a export `Turing.embedEmitTM_tr`;
  - the B4 pre-issue promotion: twelve CNF-grammar publics in `Formulas/CNFEncoding.lean`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc` moved from `Build/Zone.lean` to `Build/Catalog.lean` (same name and statement);
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont2.txt`), base sorry sets, screen bases and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-canon`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| B4, TQBF membership | `briefs/ch34-b4-mem.md` | `ClassPSPACE/TQBF.lean`: `TQBF_mem_PSPACE` only |
| §12.10 W2-S, continuation 2 | `briefs/w2-fill-oraclesim-cont2.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation 2 | `briefs/w1-fill-recordtable-cont2.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, the canonizer | `briefs/b5a-fill-canon.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, the uniform simulator H1 | `briefs/b5a-fill-h1.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

Also in flight (wave 5): S1b (`SpaceComplexity/ConfigGraph.lean`), which cites five record-table
rows; B3a (`SpaceComplexity/Constructible.lean`); and B5b (`Diagonalization/EXPCOM.lean`, by
declaration), which cites W2-S and B5a's two rows. A parallel batch's work is invisible to your
base and your screen.

## What this is

**B5a, split** (user, 2026-10-12). The two remaining §12.11 rows now run as two parallel
batches carved by declaration out of `CodeSimulator.lean`. **This batch is the canonizer**:
`MachineFormat.exists_polyCanonizer`, a polynomial-time machine computing
`F.serialize (F.decode α)`. The other batch builds H1 and cites your target modulo.

The first continuation built and proved the **physical binary-header loader**
(`exists_canonHeaderCall`) and the **fail-fast binary length guard** (`binaryGuardTM`, an
instance of `counterLoopTM` over the input-block controller `guardBlockTM`, with `_done` and
`_escape` contracts whose bounds do not depend on the counter's value). They are not yet
composed. **Assemble them into the canonizer and finish the grammar parser.** When your target
lands, targets 3–5 and `baker_gill_solovay` lose one modulo row each; nothing else changes.

**Read first:** the first continuation's report (`audits/b5a-fill-agent-reports/cont-1-REPORT.md`),
especially its "Continuation frontier", steps 1–2; the earlier briefs `briefs/b5a-fill-cont.md` and
`briefs/b5a-fill.md` (routes, gate guidance and pitfalls still bind); design §12.11;
`CodeSimulator.lean` in full.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the import
probe `audits/evidence/b5a/B5aContPreShip.lean.txt` and the S1210 probe, re-run at the issue tree
(`audits/logs/b5a-fill-cont2-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:727` | `Turing.MachineFormat.exists_polyCanonizer` | the loaded header, the guards, the fixed grammar, emit or fallback | the header loader and length guard |

- **Owned:** the regions of ground rule 1, and nothing else.
- **Frozen (both B5a batches):** the six filled targets 3–8 and their privates
  (`twoTape_serialize_eq`, `twoTapeMachineFormat`, `expcom_padding_bound`); and, in
  `CodeSimulator.lean`, the **35 inherited privates**:
  - the first delivery's 17: the canonizer preparation (`skipRepeat_consumes`, `skipSymbols_consumes`,
    `skipTable_consumes`, `scan_grammar_guard`, `guardedScan`, `guardedScan_eq`,
    `decode_of_grammar_guard`, `grammar_guard_states`) and the D4 output summary and semantic clock
    (`outputSummary`, `summaryEmit`, `outputSummary_append`, `outputSummary_true`,
    `summaryEmit_other`, `summaryClock`, `summaryClock_correct`, `summaryClock_accepts`,
    `summaryClock_zero`);
  - the first continuation's 18: the physical header loader (`canonHeader`, `canonHeader_length`,
    `exists_canonHeaderCall`) and the fail-fast length guard (`guardBlockTM` and its lemmas,
    `binaryGuardTM`, `binaryGuardStart`, `binaryGuard_done`, `binaryGuard_escape`, `guardCfg`,
    `guardPhase`, `guardTime`).

  Cite them; never change them. Both batches may cite any of them.
- **Not yours:** `MachineFormat.exists_uniformSimulator` (the H1 batch), `NPOracle_EXPCOM_subset_EXP`
  (B5b), `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`,
  and the facades.

### Proof routes (binding; the original brief's route 1)
 (binding; the original brief's routes 1–2)

- **1, the canonizer.** Implement `F.scan` and emit `F.canonical` (`CodeFormat.canonical_eq`).
  Copy `α`; parse the doubled state count (`pairDecode`) and check it is canonical; check the
  guard `F.guard·(n + 1) ≤ |rest|` **in binary before any state-indexed work** (count `rest` in
  blocks against a decrementing copy of `bits n`, never expanding `n` in unary). Then the fixed
  grammar (`F.skipTable_eq`, `codeSkipTableK`): `n + 1` rounds of `3^(k+1)` records. **The guard
  may be `0`** (minor 5): add the grammar-derived necessary check
  `(4k + 5)·3^(k+1)·(n + 1) ≤ |table bits|`, in binary with fail-fast; early rejection yields
  exactly the fallback, because `F.scan` fails on the same inputs. Check the all-`true` suffix;
  copy the consumed prefix or emit `F.serialize F.fallback`.

### The frontier you inherit (the first continuation's, steps 1–2)

1. **Compose the loaded header with validation and the guard.** Reuse `exists_canonHeaderCall`.
   Validate `pairDecode` success separately from its empty-word fallback, and validate the
   canonical binary representation. Keep whatever copy of the header is needed after the
   destructive countdown. Arrange the `n + 1` blocks the grammar guard requires, for example one
   initial block and then `n` decrements: `binaryGuard_*` counts exactly the value already on its
   counter tape. Position the native input at the header's remainder and instantiate the positive
   grammar block size. Apply the format's own guard too, bypassing a zero guard. The guard accepts
   any input starting offset, and its counter value is `Nat.ofDigits 2 (w.map Bool.toNat)`.
2. **Finish the physical grammar parser.** Check the initial-state range, the fixed action
   records and successor ranges, and the all-`true` suffix. Record the consumed prefix, and emit
   it on success or the fixed fallback on any failure. `guardedScan_eq`, `decode_of_grammar_guard`
   and `CodeFormat.canonical_eq` are the semantic bridges. Prove the combined polynomial ledger and
   discharge `exists_polyCanonizer`.

`exists_canonHeaderCall` inherits the public call's positive-time cut. A later R2 composition
needs the time-zero cut, as the original brief warns: use the existing release row when entry
and exit coincide.

## Gate guidance (binding)

- **Minor 5** (zero guard), above.
- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family, with its bridges; it is not new debt.
- **Note 50:** permanent sanity cases **at fill**, executed in your evidence: zero-guard huge
  headers (canonizer), and exact-deadline acceptance (H1: a machine halting at exactly `t` steps
  with output `[true]` is accepted at deadline `t`). The first delivery executed both on the
  semantic preparation only; execute them on the **physical** canonizer and H1.
- **Round-2 note 17:** keep a detecting control when `EXP_subset_POracle_EXPCOM` is filled: the
  S1210 probe's census should still detect an admission (the summit) after you land.

## Cited infrastructure (public and proved at the issue commit)

- `CodeFormat` (generic parse layer, `canonical_eq`, `decode_serialize_pad`, `codeReadActionK(_append)`),
  `CodeSimulator`'s proved layer (`serializeK`, `tableBitsK`, `workReadsK`, `codeSkipTableK`, the
  bridges `tableBitsK_two`, `codeSkipTable2_eq_codeSkipTableK`, `oneTapeMachineFormat`).
- `counterLoopTM` and contracts, `counterLoop_time_le`, `decrementTM` rows (CounterLoop);
  `vhostEmitTM`, `vhostEmitTM_runFrom` (Z1); `FinTM.exists_installCallTM` (Loop); R1, R2, the §12
  Catalog rows; `FinTM.one_work_tape_binary`, `exists_codeTM`, `expCode`; the chapter-2 padding
  cluster (`polyTimeComputable_const`, `_id`, `_polyUnary`, `PolyTimeComputable.pairEncode`);
  `mem_POracle_of_polyTimeReducible`, `POracle_subset_NPOracle`.
- **Proved modulo:** `NPOracle_EXPCOM_subset_EXP` (B5b), for targets 6–8 only.
- **Newly sanctioned** (rule 6): `FinTM.computesFunInTime_pairFst`/`_pairSnd` (`Build/Primitives`), for
  the nested input; `FinTM.exists_inputCallTM` and `exists_inputSeekTM` (`Build/InputCall`), if the
  loader needs a native-input call.
- The first delivery's 17 privates (above).

## Ground rules (binding)

1. **File ownership, by declaration** (user-approved split). In `TuringMachine/CodeSimulator.lean`,
   and nowhere else, you own exactly these regions. Line numbers are at the issue commit.
   - **(a) New `private` declarations,** inserted in the blank gap at line 685: after the
     length-guard section's last declaration and before `exists_polyCanonizer`'s docstring
     (line 686). `private` only, and no `section` or `open` that leaks past your region.
   - **(b) `exists_polyCanonizer`'s docstring,** lines 686–726. The existing text does not
     change. Append a flagged **Fill appendix** before the closing `-/`.
   - **(c) Its body,** the `sorry` on line 730. The signature, lines 727–729, is frozen.
   **Not yours:** every other line of the file, including the module header (its Status and
   "Main results"), every section heading, every existing declaration, and the other B5a batch's
   target and gap. The maintainer updates the module header and the status text in
   `Codes2Tape.lean`/`EXPCOM.lean` at integration. Report any header text that reads wrong; do not
   edit it. List every new declaration with its role. A lemma that genuinely belongs in a shared
   file is written privately, flagged in `REPORT.md` as a promotion candidate, and promoted by the
   maintainer (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay; a flagged
   **"Fill appendix"** is expected wherever your proof refines or replaces a sketch's route.
3. **Status text.** Only your target's "(spec, fill pending …)" tag, inside your target's docstring
   region, may change, to "proved" (or "proved modulo …"); flag it. No new public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. The first continuation added the two sanctioned imports
   (`Build/Primitives`, `Build/InputCall`); no other TCSlib import may be added. A Mathlib import is
   allowed only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report each owned
   file's final line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.
10. **D4 is complete** (the first delivery's ledger): no further deletions or moves.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/b5a-fill-cont2-screen-base.txt`:
**1,572 declarations, 1,801 pairs, 591,421 characters**.

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
  TCSlib/Complexity/TuringMachine/UniversalStartup.lean \
  TCSlib/Complexity/Diagonalization/EXPCOM.lean \
  TCSlib/Complexity/TuringMachine/MathlibBridge.lean \
  TCSlib/Complexity/TuringMachine/CodeParser.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - **the parallel H1 batch** writes privates in the other gap; you cannot see them. Never build an interpreter, a step block or a host clock here (they are H1's);
  - the header loader and length guard: cite them; never write a second header parser or block counter;
  - the first delivery's pre-disclosed mirror pair (`exists_uniformMachineCode2` ↔ `exists_uniformMachineCode`, 75%) is recorded (`backlog.md` CH34-D3); add nothing to it;
  - the semantic clock: cite `summaryClock_accepts`, never restate it inside the physical trace;
  - `universalInterpreter` and the `Universal*` files: never copy their step or parse proofs (the one interpreter trace is new and generic);
  - the D4-moved output summary and clock: cite them, never duplicate them;
  - **pre-disclosed:** the forced writer pairs (`oneTapeFormat` 85%, `codeTable2Bits` 67%, `Code2TM.serialize` 56%: item 8's residual watch item) and the two instance assemblies (a forced mirror pair);
  - `MathlibBridge`'s arbitrary-time canonizer route: not reused for the polynomial canonizer.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-cont2.txt` (**79 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-cont2.txt )
  ```

  **Base sorry-warning set, 18** (`audits/logs/b5a-fill-cont2-base-sorries.txt`, one entry per declaration).
  Yours: `CodeSimulator` 1 (your target). Record the base list by name first. If anything else has landed by your base
  (a parallel batch), report the difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, the other B5a batch's target
     (plus your own target's, for a partial).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**17** for a complete delivery).
  3. Re-run the pre-ship probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt` and
     `audits/evidence/b5a/B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting the summit.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine and TCSlib/Complexity/Diagonalization (two runs)`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation
- `TuringMachine/CodeSimulator`: exists_uniformSimulator
- `Diagonalization/EXPCOM`: NPOracle_EXPCOM_subset_EXP
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] Note 50: the zero-guard huge-header case, executed on the physical canonizer.
- [ ] Targets 3–8: the re-run axiom prints and admission walks.

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
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`; `counterWord` freezes at
  zero while the machine wraps: stay at `r ≤ value + 1`.
- `vhostEmitTM`'s virtual input has both boundary positions; the buffer interval is `[-1, 0]`
  when empty.
- The frozen `UniformMachineCode`/`UniformMachineCode2` field shapes are exactly H1's two
  clauses: transcribe the probe's Part D rather than re-deriving them.
