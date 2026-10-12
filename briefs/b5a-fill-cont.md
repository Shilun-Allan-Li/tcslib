# Ch3–4 fill campaign — B5a, continuation: the polynomial canonizer and the uniform simulator H1 (`TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 820d23121a5847808d079f26bfe7efe0aee36ca3 HEAD`
  succeeds. That commit contains:
  - the first B5a delivery (targets 3–8 filled, proved modulo the two §12.11 rows) and its report `audits/b5a-fill-agent-reports/REPORT.md`, with the integration record `audits/fills-4-integration.md`;
  - W2-V (`FinTM.exists_certificateShell`), R8.5c and every §12.8 row, proved;
  - this brief's order list `briefs/orders/b5a-fill-cont.txt`, base sorry set, screen base, pre-ship log and the import probe `audits/evidence/b5a/B5aContPreShip.lean.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-cont`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-cont.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| §12.10 W2-S, continuation | `briefs/w2-fill-oraclesim-cont.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation | `briefs/w1-fill-recordtable-cont.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, continuation | `briefs/b5a-fill-cont.md` | `TuringMachine/CodeSimulator.lean` (and status text in `TuringMachine/Codes2Tape.lean`, `Diagonalization/EXPCOM.lean`) |

A parallel batch's work is invisible to your base and your screen.

## What this is

**A continuation** (`workflow.md` §4). The first B5a delivery filled six of the eight targets:
the two uniform-scheme instances (targets 3–4, route Z), the padding reduction
`EXP_subset_POracle_EXPCOM` (5) and the three `EXPCOM` identities (6–8). All six are **proved
modulo** the two §12.11 rows, which keep their original `sorry`; 6–8 also rest on B5's summit.
It also proved the semantic preparation for both rows. Fill the **two remaining rows**:
- **1:** `MachineFormat.exists_polyCanonizer`, a physical polynomial-time canonizer;
- **2:** `MachineFormat.exists_uniformSimulator` (**H1**), the hosted, clocked generic interpreter.

When both land, targets 3–5 are admission-free, and 6–8 and `baker_gill_solovay` rest on the
summit alone. This is B5's headline construction and is expected to be large: a partial is fine
(rule 9), an unreported gap is not.

**Read first:** the first delivery's report (`audits/b5a-fill-agent-reports/REPORT.md`, through
"Archive contents"; the rest quotes the two screens), especially its "Continuation frontier",
which is written for you; the original brief `briefs/b5a-fill.md`, whose routes, gate guidance
and pitfalls still bind; design §12.11; `CodeSimulator.lean` in full.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the S1210
probe and the import probe `audits/evidence/b5a/B5aContPreShip.lean.txt` (the two sanctioned
imports below, the two frozen statements, and every row the routes cite), re-run at the issue
tree (`audits/logs/b5a-fill-cont-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:346` | `Turing.MachineFormat.exists_polyCanonizer` | binary-guard parser, fixed grammar, fallback | — |
| 2 | `…:476` | `Turing.MachineFormat.exists_uniformSimulator` | H1: one step block under `counterLoopTM`, hosted by Z1 | 1 |

- **Owned:** `TuringMachine/CodeSimulator.lean`, for the two bodies and new `private`
  declarations; and, **for status text only**, `TuringMachine/Codes2Tape.lean` and
  `Diagonalization/EXPCOM.lean`. There, the first delivery's "B5a partial" and "proved modulo
  §12.11" tags and Status paragraphs become "proved" (the three identities: "proved modulo B5b's
  summit"), each flagged. Nothing else in those two files changes.
- **Frozen:** the six filled targets and their privates (`twoTape_serialize_eq`,
  `twoTapeMachineFormat`, `expcom_padding_bound`); and, in your file, the first delivery's 17
  privates:
  - the canonizer preparation: `skipRepeat_consumes`, `skipSymbols_consumes`,
    `skipTable_consumes`, `scan_grammar_guard`, `guardedScan`, `guardedScan_eq`,
    `decode_of_grammar_guard`, `grammar_guard_states`;
  - the D4 output summary and semantic clock: `outputSummary`, `summaryEmit`,
    `outputSummary_append`, `outputSummary_true`, `summaryEmit_other`, `summaryClock`,
    `summaryClock_correct`, `summaryClock_accepts`, `summaryClock_zero`.

  Cite them; never change them.
- **Not yours:** `NPOracle_EXPCOM_subset_EXP` (B5b), `CodeFormat.lean`, `Universal*.lean`,
  `MathlibBridge.lean`, `NDCodes.lean`, `ClassOracle/*`, `Relativization.lean`, and the facades.
- Fill 1, then 2.

### Proof routes (binding; the original brief's routes 1–2)

- **1, the canonizer.** Implement `F.scan` and emit `F.canonical` (`CodeFormat.canonical_eq`).
  Copy `α`; parse the doubled state count (`pairDecode`) and check it is canonical; check the
  guard `F.guard·(n + 1) ≤ |rest|` **in binary before any state-indexed work** (count `rest` in
  blocks against a decrementing copy of `bits n`, never expanding `n` in unary). Then the fixed
  grammar (`F.skipTable_eq`, `codeSkipTableK`): `n + 1` rounds of `3^(k+1)` records. **The guard
  may be `0`** (minor 5): add the grammar-derived necessary check
  `(4k + 5)·3^(k+1)·(n + 1) ≤ |table bits|`, in binary with fail-fast; early rejection yields
  exactly the fallback, because `F.scan` fails on the same inputs. Check the all-`true` suffix;
  copy the consumed prefix or emit `F.serialize F.fallback`.
- **2, H1.** Parse the nested input onto tapes (deadline `bits t`, table `α`, buffer `x`); canonize
  in place by 1 through `FinTM.exists_installCallTM`; by `F.serialize_eq` the table is
  `serializeK (F.machine (F.decode α))`. **Exactly one private interpreter trace**: a step block
  for one simulated transition of a `k`-tape coded table (seek the record at
  `q·3^(k+1) + rank(inp, w)`, read it by `codeReadActionK`, apply it to `k` mirrored tapes and the
  simulated input head, update a finite output summary instead of emitting). Its properties:
  states independent of the code; per-round cost `B·(|table| + 1)`, independent of `t` and `x`;
  input read only through its own head; silent; proved at the relation level. It is hosted by
  `vhostEmitTM` and clocked by `counterLoopTM` over `bits t` (`_run_done` at timeout, `_run_escape`
  at a simulated halt). **It is not a copy of `universalInterpreter`.**

### The frontier you inherit (the first delivery's; resume at step 1)

1. **The physical canonizer.** Implement the binary header loader and the guard in finite
   control and tapes, keeping the count binary. Fail as soon as the input cannot supply the
   positive grammar minimum, including for zero-guard formats. Check the original guard, the
   initial-state range, the fixed record grammar and the all-`true` suffix. Emit exactly the
   consumed prefix, or the fixed fallback. Prove polynomial time and fill
   `exists_polyCanonizer`. `guardedScan_eq` and `decode_of_grammar_guard` fix the extensional
   target and justify early failure; they supply no runtime bound.
2. **Exactly one generic step block.** Look the record up at the prescribed state/read index,
   read it with `codeReadActionK`'s public laws, apply it to the `k` mirrored tapes and the
   simulated input head, and update `outputSummary` by `summaryEmit`. Prove the silent
   relation-level trace and the per-round bound linear in the table length.
3. **H1.** Load the nested input; install the canonizer through the public call row; host by
   `vhostEmitTM` and clock by `counterLoopTM`. Prove both the returning and the escaping cases
   with the public host contracts: an exact-deadline halt escapes on the last permitted round.
   The verdict comes from `summaryClock_accepts`; prove the joint polynomial ledger.
4. Targets 3–8 then need no new assembly: re-run their axiom prints and admission walks, and
   update the status text.

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

1. **File ownership.** Only `CodeSimulator.lean`: change only the two targets' bodies, and add new
   `private` helpers there. In `Codes2Tape.lean` and `EXPCOM.lean`, only the flagged status text.
   List every new declaration with its role. A lemma that genuinely belongs in a shared
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
6. **Imports.** **Sanctioned additions, exactly:** `import TCSlib.Complexity.TuringMachine.Build.Primitives` and `import TCSlib.Complexity.TuringMachine.Build.InputCall` in `TuringMachine/CodeSimulator.lean` (both acyclic at the issue tree; add each only if used). Flag each. The first delivery's two imports stand. No other TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
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
10. **D4 is complete** (the first delivery's ledger): no further deletions or moves.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/b5a-fill-cont-screen-base.txt`:
**1,511 declarations, 1,789 pairs, 589,285 characters**.

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
- **Bootstrap once** from `briefs/orders/b5a-fill-cont.txt` (**77 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-cont.txt )
  ```

  **Base sorry-warning set, 17** (`audits/logs/b5a-fill-cont-base-sorries.txt`, one entry per declaration).
  Yours: `CodeSimulator` 2. Record the base list by name first. If anything else has landed by your base
  (a parallel batch), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**15** for a complete delivery).
  3. Re-run the pre-ship probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt` and
     `audits/evidence/b5a/B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting the summit.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine and TCSlib/Complexity/Diagonalization (two runs)`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation
- `Diagonalization/EXPCOM`: NPOracle_EXPCOM_subset_EXP
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/RecordTable`: exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 2/2, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] Note 50: the two sanity cases, executed on the physical canonizer and H1.
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
