# Ch3–4 fill campaign — B5a, the canonizer, continuation (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor c0eefa8be8c277777dfecd8d2510d8e57218ce4c HEAD`
  succeeds. That commit contains:
  - the fills-6 integration (`audits/fills-6-integration.md`), with the canonizer's previous report
    `audits/b5a-fill-agent-reports/canon-1-REPORT.md` and H1's `audits/b5a-fill-agent-reports/h1-1-REPORT.md`;
  - W2-S and B5b, both landed: `NPOracle_EXPCOM_subset_EXP` now rests only on the two §12.11 rows;
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont3.txt`), base sorry sets, screen
    bases, screen populations and pre-ship logs.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-canon-cont`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont.zip`, containing
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

**The canonizer's second continuation** (user, 2026-10-12: continue at machine level). Your target
is `MachineFormat.exists_polyCanonizer`, a polynomial-time machine computing
`F.serialize (F.decode α)`. It is on chapter 3's critical path: when it lands, `EXPCOM`, the
scheme instances, `EXP ⊆ P^EXPCOM`, the summit, the chained identities and
`baker_gill_solovay` each lose one of their two remaining admissions. H1 (the parallel batch)
cites your target through its frozen statement.

**What is proved, privately, in your file:**
- the physical binary-header loader `exists_canonHeaderCall`, and the fail-fast length guard
  `binaryGuardTM` with `binaryGuard_done` and `binaryGuard_escape`;
- the canonical-header check: the last-bit scan `canonBitsTM` (`canonBitsTM_run`), the seam
  `exists_canonHeaderSeam`, the verdict `exists_canonHeaderBitsTM`, and `exists_canonHeaderOKTM`,
  which checks pair success separately from the empty-header fallback;
- the nonoverflowing successor counter `exists_canonCountTM` (`canonCount`, value `n + 1`);
- the single positive block size `canonGuardBlock F = max F.guard ((4k + 5)·3^(k+1))`, its
  rejection law `decode_of_canonGuard`, and `canonGuard_run`, the inherited guard specialized to
  the post-header offset from a **preloaded** configuration.

**What remains** is the previous report's "Exact continuation frontier", steps 1–5 (below).

**Read first:** that report (`audits/b5a-fill-agent-reports/canon-1-REPORT.md`), whose frontier is
written for you; the earlier briefs `briefs/b5a-fill-canon.md`, `briefs/b5a-fill-cont.md` and
`briefs/b5a-fill.md` (routes, gate guidance and pitfalls still bind); design §12.11;
`CodeSimulator.lean` in full.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the import
probe `audits/evidence/b5a/B5aContPreShip.lean.txt` and the S1210 probe, re-run at the issue tree
(`audits/logs/b5a-fill-cont3-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:1202` | `Turing.MachineFormat.exists_polyCanonizer` | load, check and guard the header; parse the fixed grammar; emit or fall back | the proved loader, header check, counter and guard |

- **Owned:** the regions of ground rule 1, and nothing else.
- **Frozen (both B5a batches):** the six filled targets 3–8 and their privates
  (`twoTape_serialize_eq`, `twoTapeMachineFormat`, `expcom_padding_bound`); and, in
  `CodeSimulator.lean`, **all 78 privates** present at the issue tree: the first delivery's 17, the
  first continuation's 18, your previous continuation's 23 (`canonBitsOK` … `canonGuard_run`), H1's
  16 (`h1RecordWidth` … `h1Record_effect`) and the four layout lemmas. Cite them; never change them.
- **Not yours:** `MachineFormat.exists_uniformSimulator` and its gap (the H1 batch);
  `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`, and
  the facades.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators**: R2 seams (`seamCompTM`, `seamReleaseTM`), the phase host
  (`phaseHostTM`), R1 embedding (`embedEmitTM`), the counter loop (`counterLoopTM`), the native-input
  seek (`exists_inputSeekTM`) and the install call (`FinTM.exists_installCallTM`). Do not write a
  hand controller for a phase that a public row provides.
- **The record parser is the reusable piece.** Build the validation of one action record (its
  fixed fields' grammar, then the successor field's unary range against the binary state count)
  as one generic component with its own contract, independent of the format, and list it as a
  promotion candidate. Then run it `(n + 1)·3^(k+1)` times under one public loop.
- **Pre-disclosed parallel overlap.** The H1 batch also walks canonized records (to seek one). It
  needs no validation; you need it. If both batches write a fixed-field walk, the maintainer
  factors it at integration. Do not try to coordinate.

### The frontier you inherit (the previous report's, binding)

1. **Connect the loaded tapes to the preloaded guard.** Use the proved validator or its
   lower-level contracts (`exists_canonHeaderSeam`, `canonBitsTM_run`). Preserve an original
   header bank with public tape embedding and copy rows, and capture `canonCount` on a separate
   counter bank: **extract the count, then install it by an install call**. The standalone
   validator emits its Boolean result; it is not itself a clean live seam carrying the header.
2. **Position and restore the native head.** Construct the binary offset `2·|header| + 3` and use
   the public native-input seek. The paired-input length identity proves the position is in range.
   Apply `canonGuard_run` through public embedding. A successful guard consumes the compared prefix
   of the remainder, so seek back before the grammar parser. No load, copy or seek work is hidden
   in `canonGuard_run`'s time bound.
3. **Implement the physical grammar.** Check the unary initial-state range; perform `n + 1` state
   rounds, each of `3^(k+1)` fixed action records with binary-bounded successor ranges; check the
   all-`true` suffix; keep the consumed-prefix boundary. The positive guard runs before any
   state-indexed work. Cite the frozen parser laws (`guardedScan_eq`, `decode_of_grammar_guard`,
   `skipTable_consumes`, `codeSkipTableK`, `F.skipTable_eq`).
4. **Emit and account.** Copy the consumed input prefix on success, or emit
   `F.serialize F.fallback` on any failure. Use `CodeFormat.canonical_eq`, the inherited semantic
   bridges, and a combined polynomial ledger to discharge the unchanged headline.
5. **Complete note 50.** Execute the zero-guard and huge-header cases on the complete physical
   canonizer.

## Gate guidance (binding)

- **Minor 5** (zero guard): `canonGuardBlock` already enforces both necessary conditions in one
  pass; early rejection yields exactly the fallback.
- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family, with its bridges; it is not new debt.
- **Note 50:** permanent sanity cases **at fill**, executed in your evidence on the **physical**
  canonizer: zero-guard huge headers (for example the header of `2^128` with a short remainder),
  an empty header, a malformed pair encoding, and one small well-formed code that round-trips.
- **Round-2 note 17:** keep a detecting control: the S1210 probe's census must still detect its
  probe-local admission after you land.
- **The time-zero cut:** `exists_canonHeaderCall` and `exists_installCallTM` give the positive-time
  cut only. An R2 composition needs the time-zero cut as well: use the release adapter when entry
  and exit coincide.

## Cited infrastructure (public and proved at the issue commit)

- `CodeFormat` (generic parse layer, `canonical_eq`, `decode_serialize_pad`, `codeReadActionK(_append)`,
  `codeSkipActionK`, `codeActionK_length`), `CodeSimulator`'s proved public layer (`serializeK`,
  `tableBitsK`, `workReadsK`, `codeSkipTableK`, the bridges).
- **Build:** `counterLoopTM` and its contracts, `counterLoop_time_le`, `decrementTM` rows
  (CounterLoop); `seamCompTM`, `seamReleaseTM`, `phaseHostTM` and their contracts (Seam);
  `embedEmitTM_runFrom` (Embed); `FinTM.exists_installCallTM` (Loop); `FinTM.exists_inputCallTM`,
  `exists_inputSeekTM` (InputCall); `FinTM.computesFunInTime_pairFst`/`_pairSnd`, `_pairValid`,
  `_incFixed`, `_appendBit` (Primitives); `copyTM`, `clearTM`, `scanTM`, `compareTM` and the §12
  Catalog rows; `writeConstTM`, `inputCopyTM` (Scan).
- **Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in your target.

## Ground rules (binding)

1. **File ownership, by declaration** (user-approved split). In `TuringMachine/CodeSimulator.lean`,
   and nowhere else, you own exactly these regions. Line numbers are at the issue commit.
   - **(a) New `private` declarations,** inserted in the blank gap at lines 1144–1145: after
     `canonGuard_run` and before `exists_polyCanonizer`'s docstring (line 1146). `private` only,
     and no `section` or `open` that leaks past your region.
   - **(b) `exists_polyCanonizer`'s docstring,** lines 1146–1201. The existing text does not
     change. Append a flagged **Fill appendix** before the closing `-/`, as its own paragraph.
   - **(c) Its body,** the `sorry` on line 1205. The signature, lines 1202–1204, is frozen.
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
   region, may change, to "proved"; flag it. No new public declaration.
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
   fine; an unreported gap is not.
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
  - **the parallel H1 batch** writes privates in the other gap; you cannot see them;
  - the canonical-bit lemmas against `NotTimeConstructible`'s private `ntc_bits_codeBitsNat_append_true` and `ntc_codeBitsNat_eq_ofDigits`, and `UHaltMachine`'s `bits_foldr_bit_one` (recorded as F6-1(c)): cite the public digit-fold laws, never restate them again;
  - your previous in-file pair (`canonHeader_length` against `canonHeaderOK_iff`, 56%) is recorded;
  - the chapter-1 parser (`CodeParser`, `MathlibBridge`): never copy its parse proofs; the frozen grammar laws are the bridge;
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
  1. `CodeSimulator`: zero errors, and exactly one sorry warning, the other B5a batch's target
     (plus your own target's, for a partial).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**15** in all for a complete delivery).
  3. Re-run the pre-ship probes `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt` and
     `audits/evidence/b5a/B5aContPreShip.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors, its census
     still detecting its probe-local admission.
- **Axiom prints** for your target and for targets 3–8: within `[propext, Classical.choice,
  Quot.sound]`, with `sorryAx` only through `exists_uniformSimulator`.
- **Lint:** `python3 scripts/campaign_style_lint.py` over `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/Diagonalization` (two runs), 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `TuringMachine/CodeSimulator`: exists_uniformSimulator (the H1 batch)
- `TuringMachine/Build/RecordTable`: exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/Zone`: exists_zoneShiftInTM, exists_zoneShiftOutTM

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] The record-parser component's contract, as a promotion candidate.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probes; every target's axiom print; the lint
      lines. The diff touches only your owned regions.
- [ ] Note 50: the physical canonizer's sanity cases, executed.

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
- `canonCount` appends a high zero before incrementing, so the counter's width is `|header| + 1`
  and its value is `n + 1`, also for the empty header.
- A failed `pairDecode` and an encoded empty header both yield `[]` as the first component:
  keep the separate pair-validity test.
