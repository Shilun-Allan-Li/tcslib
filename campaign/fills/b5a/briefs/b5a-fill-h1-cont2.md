# Ch3–4 fill campaign — B5a, H1, continuation 2 (`MachineFormat.exists_uniformSimulator`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 235de34386638aeab7d24424a69ae0a6d96c15b6 HEAD`
  succeeds. That commit contains:
  - the fills-7 integration (`audits/fills-7-integration.md`), with H1's previous report `audits/b5a-fill-agent-reports/h1-2-REPORT.md` and the canonizer's
    `audits/b5a-fill-agent-reports/canon-2-REPORT.md`;
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont4.txt`), base sorry sets, screen
    bases and pre-ship logs (the screen populations are last round's, unchanged).

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-h1-cont2`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-h1-cont2.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's)

| Batch | Brief | Owns |
|---|---|---|
| §12.8b record tables, continuation 4 | `briefs/w1-fill-recordtable-cont4.md` | `TuringMachine/Build/RecordTable.lean`: rows 17–18 only |
| B5a, the canonizer, continuation 2 | `briefs/b5a-fill-canon-cont2.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_polyCanonizer` and new privates in its gap |
| B5a, H1, continuation 2 | `briefs/b5a-fill-h1-cont2.md` | `TuringMachine/CodeSimulator.lean`, by declaration: `MachineFormat.exists_uniformSimulator` and new privates in its gap |

A parallel batch's work is invisible to your base and your screen.

## What this is

**H1's second continuation.** Your target is `MachineFormat.exists_uniformSimulator`: one machine
that, given `⟨⟨bits t, α⟩, x⟩`, decides whether the machine coded by `α` accepts `x` within `t`
steps, in time `d·(|α| + |x| + t + 1)^d` ([AB09, Theorem 1.9], time-bounded form). **It is proved
modulo `exists_polyCanonizer`**, which the parallel batch fills: cite the canonizer's frozen
statement through `FinTM.exists_installCallTM`.

**What is proved, privately, in your file** (your two previous deliveries, 114 declarations):
- the selected-record component `h1RecordTM` (`h1Record_effect`, with its head envelope);
- **the complete generic step block** `h1RoundTM k`, one finite machine per work-tape count `k`,
  with control independent of the coded state count. It looks up the record in the serializer's
  read order, executes the selected record's payload, installs the successor and restores the
  round seam. Its contract `h1Round_effect` gives `0 < T ≤ 50·(|table| + 1)`, a strict interior
  that visits neither exit, unchanged output at every prefix, the head envelope (each mirrored
  and input head at its start or its end, at distance at most one; auxiliary heads within the
  same linear bound and back home), and the representation `h1RoundRep` at the endpoint;
- the whole-record skipper `h1SkipTM` (`h1Skip_run`, `h1Skip_spec`), the successor leaf `h1SuccTM`
  and its lemmas, and `h1Run_headBound`;
- the semantic summary and clock (`outputSummary`, `summaryClock`, `summaryClock_accepts`) and the
  header loader `exists_canonHeaderCall`.

**The step block is host H2** (design §14) and will be promoted to a public module by the
maintainer (backlog F7-1(a)). Its statements are frozen: cite them as they are.

**What remains** is your previous report's "Continuation frontier", items 1–4 (below): the startup
and the canonizer's installation, the hosted clock, the ledger, then note 50 and the headline.

**Also this round (rule 11):** clean up your previous delivery's style debt: its 67 Lean linter
warnings and its 83 lines over 100 characters, without changing any statement.

**Read first:** your previous report (`audits/b5a-fill-agent-reports/h1-2-REPORT.md`), whose
frontier is written for you; the earlier briefs `briefs/b5a-fill-h1-cont.md`,
`briefs/b5a-fill-h1.md` with `briefs/b5a-fill-h1-addendum-1.md`, `briefs/b5a-fill-cont.md` and
`briefs/b5a-fill.md` (routes, gate guidance and pitfalls still bind); design §12.11 and §14;
`CodeSimulator.lean` in full; the contracts of `Build/VirtualInput.lean` and
`Build/CounterLoop.lean`.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the import
probe `audits/evidence/b5a/B5aContPreShip.lean.txt` and the S1210 probe, re-run at the issue tree
(`audits/logs/b5a-fill-cont4-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 2 | `TuringMachine/CodeSimulator.lean:4938` | `Turing.MachineFormat.exists_uniformSimulator` | H1: the proved step block under `counterLoopTM`, hosted by Z1 | `exists_polyCanonizer` (modulo; parallel batch) |

- **Owned:** the regions of ground rule 1, and the style clean-up of rule 11. Nothing else.
- **Frozen (both B5a batches):** the six filled targets 3–8 and their privates
  (`twoTape_serialize_eq`, `twoTapeMachineFormat`, `expcom_padding_bound`); and, in
  `CodeSimulator.lean`, **all 188 privates** present at the issue tree: the first delivery's 17,
  the first continuation's 18, the canonizer's 35 (`canonBitsOK` … `exists_canonGuardFront`), your
  114 (`h1RecordWidth` … `h1Round_effect`) and the four layout lemmas. Cite them; never change
  them, apart from rule 11's style clean-up of your own 98.
- **Not yours:** `MachineFormat.exists_polyCanonizer` and its gap (the canonizer batch);
  `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`, and
  the facades.
- **Proved modulo, exactly:** `MachineFormat.exists_polyCanonizer`.

### The frontier you inherit (your previous report's, binding)

1. **Startup and the canonizer's installation.** Load `⟨⟨bits t, α⟩, x⟩` with the sanctioned pair
   projections (`computesFunInTime_pairFst`/`_pairSnd`), `FinTM.exists_inputCallTM`,
   `exists_inputSeekTM` and the inherited `exists_canonHeaderCall`. Install the canonizer through
   `FinTM.exists_installCallTM` at `exists_polyCanonizer`'s frozen witness. Establish the round
   seam `h1RoundRep`: the canonical `tableBitsK` copied to the table tape, the initial unary state
   at auxiliary cell 2, the empty summary at cell 0, zero auxiliary heads, the initial mirrored
   bank, and the correct simulated input position. Do not add a private canonizer, grammar parser
   or header validator.
2. **Z1 and the binary clock.** Compose the one proved round with `vhostEmitTM_runFrom` and
   `counterLoopTM` over `bits t`. Prove both `counterLoopTM_run_done` (timeout: the answer is
   `false`) and `counterLoopTM_run_escape` (a simulated halt: the answer is the summary's `[true]`
   test), including a halt on the last permitted round and the input device's boundary tag. The
   step block supplies a positive first return, a live escape, silence and a uniform per-round
   bound. Do not introduce a new host, and do not assume an unproved fixed boundary tag at a loop
   seam.
3. **The verdict and the joint ledger.** Use the inherited `summaryClock_accepts`, not another
   semantic acceptance proof. Combine the polynomial startup with `t` rounds of at most
   `50·(|table| + 1)` (`counterLoop_time_le`), the canonical code-length bound and the verdict's
   cost, to reach the frozen joint polynomial in `|α| + |x| + t + 1`.
4. **Note 50, then the headline.** Execute the physical **hosted and clocked** H1 on a machine
   accepting at exactly deadline `t` and rejecting at `t − 1`, including a `k ≥ 2` code and a first-
   step halt at deadline `1`. Only then replace `exists_uniformSimulator`'s body.

**Pre-disclosed parallel overlap.** The canonizer batch also walks records (to validate them); the
maintainer factors a common fixed-field walk later (backlog F7-1(c)). Do not try to coordinate.

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
   - **(a) New `private` declarations,** inserted in the blank gap at line 4868: after
     `h1Round_effect` and before `exists_uniformSimulator`'s docstring (line 4869). `private`
     only, and no `section` or `open` that leaks past your region.
   - **(b) `exists_uniformSimulator`'s docstring,** lines 4869–4937. The existing text, including
     the two earlier fill appendices, does not change. Append a flagged **Fill appendix** before
     the closing `-/`, as its own paragraph.
   - **(c) Its body,** the `sorry` on line 4946. The signature, lines 4938–4945, is frozen.
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
   fine; an unreported gap is not. **If you stop early, stop at a complete phase** (the startup
   seam, the hosted clock, or the ledger), each with its own contract.
10. **D4 is complete** (the first delivery's ledger): no further deletions or moves.
11. **Style clean-up of your own previous delivery** (backlog F7-1(e); this round only). In the
    declarations your previous delivery added (the 98 from `h1WorkReads_mem` to `h1Round_effect`,
    which carry all 67 of the file's linter warnings and 83 lines over 100 characters, in 29
    declarations), and nowhere else, you may change proof bodies **only** to remove Lean linter
    warnings (unused `simp` arguments, unreachable tactics, `<;>` where `;` suffices, no-op
    `omega`/`congr`, `simpa` → `simp`, unused variables) and to wrap lines over 100 characters. No
    statement, name, docstring or definition body changes; every such declaration must still
    elaborate. Report the before and after counts of linter warnings and over-width lines in those
    declarations, and list each declaration you touched.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The population is widened this round, to the Build files you compose and to the
two files where the review found overlapping bit lemmas
(`audits/evidence/fills-6/b5a-fill-cont3-screen-population.txt`, 34 files). The base, at this
brief's issue tree, is `audits/logs/b5a-fill-cont4-screen-base.txt`: **2,020 declarations, 2,221 pairs, 742,099 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  $(cat audits/evidence/fills-6/b5a-fill-cont3-screen-population.txt)
```

- **No new cross-file pair** with an owned-file declaration on one side, except the pre-disclosed
  overlap above (measure it if it appears).
- **Known hazards:**
  - **the parallel canonizer batch** writes privates in the other gap; you cannot see them. Never build a canonizer, a header validator or a grammar parser here;
  - your previous delivery's nine in-file pairs (50–71%, justified in `h1-2-REPORT.md`) are recorded; add nothing to them;
  - **the R1 configuration-reconstruction family** (backlog F7-1(b), the wave-1 gate's acknowledged major; one public lemma lands with MIG-0b): if a proof needs "an embedded configuration is determined by its selected-bank projections and its unchanged frame", cite the canonizer's `canonEmbedEq` (same file), never write another;
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
- **Bootstrap once** from `briefs/orders/b5a-fill-cont4.txt` (**80 modules**: the upstream closure of
  your owned file and of every module downstream of it, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill-cont4.txt )
  ```

  **Base sorry-warning set, 16** (`audits/logs/b5a-fill-cont4-base-sorries.txt`, one entry per
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
- [ ] Rule 11: the linter warnings and over-width lines in your previous delivery's declarations,
      before and after, and the list of declarations touched.

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
