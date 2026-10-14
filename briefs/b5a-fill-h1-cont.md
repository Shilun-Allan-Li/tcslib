# Ch3–4 fill campaign — B5a, H1, continuation (`MachineFormat.exists_uniformSimulator`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor c0eefa8be8c277777dfecd8d2510d8e57218ce4c HEAD`
  succeeds. That commit contains:
  - the fills-6 integration (`audits/fills-6-integration.md`), with H1's previous report
    `audits/b5a-fill-agent-reports/h1-1-REPORT.md` and the canonizer's `audits/b5a-fill-agent-reports/canon-1-REPORT.md`;
  - W2-S and B5b, both landed: `NPOracle_EXPCOM_subset_EXP` now rests only on the two §12.11 rows;
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont3.txt`), base sorry sets, screen
    bases, screen populations and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-h1-cont`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-h1-cont.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| §12.8b record tables, continuation 3 | `briefs/w1-fill-recordtable-cont3.md` | `TuringMachine/Build/RecordTable.lean`: rows 17–18 only |
| B5a, the canonizer, continuation | `briefs/b5a-fill-canon-cont.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, H1, continuation | `briefs/b5a-fill-h1-cont.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

A parallel batch's work is invisible to your base and your screen.

## What this is

**H1's first continuation.** Your target is `MachineFormat.exists_uniformSimulator`: one machine
that, given `⟨⟨bits t, α⟩, x⟩`, decides whether the machine coded by `α` accepts `x` within `t`
steps, in time `d·(|α| + |x| + t + 1)^d`. It is the generic efficient universal machine of
[AB09, Theorem 1.9]. **It is proved modulo `exists_polyCanonizer`**, which the parallel batch
fills: cite the canonizer's frozen statement through `FinTM.exists_installCallTM`.

**What is proved, privately, in your file** (the previous delivery's 16 declarations): the
selected-record component `h1RecordTM`. Given a canonized record with the table head at its first
bit, it reads the record's `4k + 4` fixed bits into finite control and executes them on the `k`
mirrored tapes and the native input in exactly `4k + 5` steps, recording the emission in a
stationary summary cell (`summaryEmit`). Its control depends only on `k`. Its contract is
`h1Record_effect`, including addendum 1's head envelope for this component (`h1Record_envelope`):
only the last step moves a mirrored or input head, by at most one; the table head advances by
`min u (4k + 4)`; the summary head is fixed. The table head is left at the record's successor
field.

Also proved: the semantic output summary and clock (`outputSummary`, `summaryClock`,
`summaryClock_accepts`, the verdict's target) and the header loader `exists_canonHeaderCall`.

**What remains** is the previous report's "Continuation frontier", items 1–6 (below): the rest of
the **one** generic step block, then the hosted, clocked assembly. Build them in that order.

**Read first:** that report (`audits/b5a-fill-agent-reports/h1-1-REPORT.md`), whose frontier is
written for you; the earlier briefs `briefs/b5a-fill-h1.md` with `briefs/b5a-fill-h1-addendum-1.md`,
`briefs/b5a-fill-cont.md` and `briefs/b5a-fill.md` (route 2, gate guidance and pitfalls still bind);
design §12.11 and §14 (host H2, the step block); `CodeSimulator.lean` in full; the contracts of
`Build/VirtualInput.lean` and `Build/CounterLoop.lean`.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the import
probe `audits/evidence/b5a/B5aContPreShip.lean.txt` and the S1210 probe, re-run at the issue tree
(`audits/logs/b5a-fill-cont3-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 2 | `TuringMachine/CodeSimulator.lean:1705` | `Turing.MachineFormat.exists_uniformSimulator` | H1: one step block under `counterLoopTM`, hosted by Z1 | `exists_polyCanonizer` (modulo; parallel batch) |

- **Owned:** the regions of ground rule 1, and nothing else.
- **Frozen (both B5a batches):** the six filled targets 3–8 and their privates
  (`twoTape_serialize_eq`, `twoTapeMachineFormat`, `expcom_padding_bound`); and, in
  `CodeSimulator.lean`, **all 78 privates** present at the issue tree: the first delivery's 17, the
  first continuation's 18, the canonizer's 23 (`canonBitsOK` … `canonGuard_run`), your previous
  16 (`h1RecordWidth` … `h1Record_effect`) and the four layout lemmas. Cite them; never change them.
- **Not yours:** `MachineFormat.exists_polyCanonizer` and its gap (the canonizer batch);
  `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`, and
  the facades.
- **Proved modulo, exactly:** `MachineFormat.exists_polyCanonizer`.

### The step block (binding: host H2, design §14)

The step block is **one** private machine for one simulated transition of a `k`-tape coded
table, with one relation-level contract. It is the reusable piece: U-1 (the chapter-1 universal
machine), B6's self-application universal and C1 (with a choice-bit-indexed table) plan to reuse
it. Its contract must give:
- the silent relation-level step: the mirrored bank and the simulated input head move as
  `Action.apply` does, the summary cell is updated by `summaryEmit`, and a simulated halt is a
  live exit (the halting action's fields are still applied, as `h1Record_effect` already does);
- a per-round time bound `B·(|table| + 1)`, with `B` depending only on `k`, independent of `t`,
  `x` and the state count;
- **addendum 1's head envelope for the whole round**, in the library's
  `∀ u ≤ t, ∀ j, |pos_j(u) − pos_j(0)| ≤ …` form: each mirrored head and the simulated input head
  stays between its round-start and round-end positions, which differ by at most one; every
  other real tape stays within `B·(|table| + 1)` of its round start and returns to its home at the
  round's end. Do not prove the simulator's space ledger;
- control independent of the coded state count;
- input access in one place: one sub-step reads the simulated input cell and moves the simulated
  input head (non-binding, from addendum 1, so that an input-device interface can replace it).

State it self-contained, flag it **"promotion candidate (host H2, step block;
`machine-library-design.md` §14)"**, and give its full contract verbatim in `REPORT.md`.

### The frontier you inherit (the previous report's, binding)

1. **Complete the step block.** Keep the simulated state, observe the simulated input cell and
   the `k` mirrored work cells, select the record at index `q·3^(k+1) + rank(inp, w)` in
   `tableBitsK`'s order (states, then the input read, then `workReadsK`, tape `0` outermost), and
   feed its fixed prefix to `h1RecordTM`. The successor fields have variable length, so the seek
   walks whole records; do not confuse it with `h1RecordTM`'s fixed-width read.
2. **Install the successor and restore the round.** After the fixed-field component, read the
   successor field: `[false]` is a simulated halt (the block's live exit); `true` followed by
   `true^s ++ [false]` is the successor `s`. Install it, return the table head and every
   auxiliary head home, and prove the step relation and the per-round bound.
3. **Finish addendum 1 for the whole round**, as above.
4. **Load the nested input** with the sanctioned public rows (`computesFunInTime_pairFst`/`_pairSnd`,
   `exists_inputCallTM`, `exists_inputSeekTM`) and the inherited header loader; install the
   canonizer through `FinTM.exists_installCallTM` at `exists_polyCanonizer`'s frozen witness. Do not
   add a private canonizer, header validator or grammar parser.
5. **Host and clock:** host the single block by `vhostEmitTM` (`vhostEmitTM_runFrom`) and clock it
   by `counterLoopTM` over `bits t`. Prove `_run_done` (timeout: the answer is `false`) and
   `_run_escape` (a simulated halt within `t`: the answer is the summary's `[true]` test),
   including a halt on the last permitted round. Take the verdict from `summaryClock_accepts` and
   prove the joint polynomial ledger: polynomial startup, `t` rounds of at most
   `B·(|table| + 1)` (`counterLoop_time_le`), and the verdict.
6. **Discharge the target** only after the construction and the physical exact-deadline case
   (note 50) are verified.

**Recommended, not binding.** Keep the simulated state in unary on its own state tape (the
canonical code stores `q₀` as `unaryFin q₀`, after the header, so it can be copied there). The
seek can then loop once per `true` on the state tape, skipping `3^(k+1)` records each time with a
count held in finite control, and then skip `rank(inp, w)` more. A generic **one-record skipper**
(the fixed `4k + 4` bits, then the unary successor field; no validation, since the table is
canonized) serves the seek; list it as a promotion candidate next to `h1RecordTM`. Installing the
successor is then a clear and a unary copy. Both the state tape and the skip are bounded by
`|table|`. The public `seekStartTM` returns a head to the start of a blank-delimited word from a
nonblank cell; step back first when the head is past the end.

**Pre-disclosed parallel overlap.** The canonizer batch also walks records, to validate them. If
both batches write a fixed-field walk, the maintainer factors it at integration. Do not try to
coordinate.

## Gate guidance (binding)

- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family, with its bridges; it is not new debt.
- **Note 50:** permanent sanity case **at fill**, executed in your evidence on the **physical**
  H1: a machine halting at exactly `t` steps with output `[true]` is accepted at deadline `t`,
  and rejected at deadline `t − 1`. Include a `k ≥ 2` code and a code whose machine halts on its
  first step (deadline `1`).
- **Round-2 note 17:** keep a detecting control: the S1210 probe's census must still detect its
  probe-local admission after you land.
- **Not a copy of `universalInterpreter`:** never copy the chapter-1 interpreter's step or parse
  proofs (`UniversalBlock`, `UniversalInterpreter`); the step block is new and generic.

## Cited infrastructure (public and proved at the issue commit)

- `CodeFormat` (`codeReadActionK(_append)`, `codeSkipActionK`, `codeActionK_length`, `canonical_eq`,
  `decode_serialize_pad`); `CodeSimulator`'s proved public layer (`serializeK`, `tableBitsK`,
  `workReadsK`, `codeSkipTableK`, the bridges); `actionBitsK`, `optStateBits`, `unaryFin`.
- **Build:** `counterLoopTM`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`,
  `counterLoop_time_le`, `decrementTM` rows (CounterLoop); `vhostEmitTM`, `vhostEmitTM_runFrom` (Z1);
  `FinTM.exists_installCallTM` (Loop); `FinTM.exists_inputCallTM`, `exists_inputSeekTM` (InputCall);
  `FinTM.computesFunInTime_pairFst`/`_pairSnd` (Primitives); `seamCompTM`, `seamReleaseTM`,
  `phaseHostTM` and their contracts (Seam); `embedEmitTM_runFrom` (Embed); `copyTM`, `clearTM`,
  `seekStartTM`, `tapeAction`, `step_of_tapeAction_move`, `step_of_tapeAction_write` (Catalog);
  `writeConstTM` (Scan).
- **Head bounds:** `workTapePos_step_le`, `workTapePos_apply_le`.
- `FinTM.one_work_tape_binary`, `exists_codeTM`, `expCode`; the chapter-2 padding cluster.

## Ground rules (binding)

1. **File ownership, by declaration** (user-approved split). In `TuringMachine/CodeSimulator.lean`,
   and nowhere else, you own exactly these regions. Line numbers are at the issue commit.
   - **(a) New `private` declarations,** inserted in the blank gap at line 1650: after
     `h1Record_effect` and before `exists_uniformSimulator`'s docstring (line 1651). `private`
     only, and no `section` or `open` that leaks past your region.
   - **(b) `exists_uniformSimulator`'s docstring,** lines 1651–1704. The existing text does not
     change. Append a flagged **Fill appendix** before the closing `-/`, as its own paragraph.
   - **(c) Its body,** the `sorry` on line 1713. The signature, lines 1705–1712, is frozen.
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
   region, may change, to "proved modulo `exists_polyCanonizer`"; flag it. No new public
   declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import is allowed only if a
   needed lemma requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second host, loop, trace or layout
   lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not. **If you stop early, stop at a complete step block**: its
   contract is the most valuable intermediate result.
10. **D4 is complete** (the first delivery's ledger): no further deletions or moves.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is widened this round, to the Build files you compose and to the
two files where the review found overlapping bit lemmas
(`audits/evidence/fills-6/b5a-fill-cont3-screen-population.txt`, 34 files). The base, at this
brief's issue tree, is `audits/logs/b5a-fill-cont3-screen-base.txt`: **1,920 declarations, 2,209 pairs, 735,760 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  $(cat audits/evidence/fills-6/b5a-fill-cont3-screen-population.txt)
```

- **No new cross-file pair** with an owned-file declaration on one side, except the pre-disclosed
  overlap above (measure it if it appears).
- **Known hazards:**
  - **the parallel canonizer batch** writes privates in the other gap; you cannot see them. Never build a canonizer, a header validator or a grammar parser here;
  - the chapter-1 interpreter (`UniversalBlock`, `UniversalInterpreter`): never copy its step or parse proofs;
  - the semantic clock: cite `summaryClock_accepts`, never restate it inside the physical trace;
  - `guardBlock_orbit` against `Games.playOut_eq_iterate` (74%, found by the fills-6 combined screen; F6-1(i)): add nothing to it;
  - the pre-disclosed mirror pair (`exists_uniformMachineCode2` against `exists_uniformMachineCode`, 75%; backlog CH34-D3): add nothing to it;
  - the forced writer pairs of item 8's residual family (`oneTapeFormat` 85%, `codeTable2Bits` 67%, `Code2TM.serialize` 56%).
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/b5a-fill-cont3.txt` (**80 modules**: the upstream closure of
  your owned file and of every module downstream of it, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-cont3.txt )
  ```

  **Base sorry-warning set, 16** (`audits/logs/b5a-fill-cont3-base-sorries.txt`, one entry per
  declaration). Yours: `CodeSimulator` 1 (your target). Record the base list by name first, and
  report any difference.
- **Final checks:**
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, the canonizer batch's target
     (plus your own target's, for a partial).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**15** in all for a complete delivery).
  3. Re-run the pre-ship probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt` and
     `audits/evidence/b5a/B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors, its census
     still detecting its probe-local admission.
- **Axiom prints** for your target and for targets 3–8: within `[propext, Classical.choice,
  Quot.sound]`, with `sorryAx` only through `exists_polyCanonizer`.
- **Lint:** `python3 scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/Diagonalization` (two runs), 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/CodeSimulator`: exists_polyCanonizer (the canonizer batch)
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] The step block's full contract verbatim, as the H2 promotion candidate, with any other
      promotion candidates (the record skipper).
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every target's axiom print; the lint
      lines. The diff touches only your owned regions.
- [ ] Note 50: the exact-deadline cases, executed on the physical H1.
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
- `decide` cannot evaluate `Nat.bits`/`Nat.size`: use `Nat.size_eq_bits_len`,
  `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `omega` with products and powers as atoms (`ring` first to expose them). The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
- `counterLoopTM M` has `k + 1` tapes with the counter at `Fin.last k`; `counterWord` freezes at
  zero while the machine wraps: stay at `r ≤ value + 1`.
- `vhostEmitTM`'s virtual input has both boundary positions; the buffer interval is `[-1, 0]`
  when empty.
- The frozen `UniformMachineCode`/`UniformMachineCode2` field shapes are exactly H1's two
  clauses: transcribe the probe's Part D rather than re-deriving them.
- `h1Record_effect` leaves the table head at the successor field, not at the next record: the
  successor walk must start there.
