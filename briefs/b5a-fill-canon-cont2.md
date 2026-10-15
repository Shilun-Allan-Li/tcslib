# Ch3–4 fill campaign — B5a, the canonizer, continuation 2 (`MachineFormat.exists_polyCanonizer`, by declaration in `TuringMachine/CodeSimulator.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 235de34386638aeab7d24424a69ae0a6d96c15b6 HEAD`
  succeeds. That commit contains:
  - the fills-7 integration (`audits/fills-7-integration.md`), with the canonizer's previous report `audits/b5a-fill-agent-reports/canon-2-REPORT.md` and H1's
    `audits/b5a-fill-agent-reports/h1-2-REPORT.md`;
  - this round's order lists (`briefs/orders/{w1,b5a}-fill-cont4.txt`), base sorry sets, screen
    bases and pre-ship logs (the screen populations are last round's, unchanged).

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a-canon-cont2`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a-canon-cont2.zip`, containing
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

**The canonizer's third continuation** (user, 2026-10-12: continue at machine level). Your target
is `MachineFormat.exists_polyCanonizer`, a polynomial-time machine computing
`F.serialize (F.decode α)`. It is on chapter 3's critical path: when it lands with H1, the
`EXPCOM` cluster and `baker_gill_solovay` lose their last admissions. H1 (the parallel batch) cites
your target through its frozen statement.

**What is proved, privately, in your file** (your previous deliveries, 35 declarations):
- the physical binary-header loader `exists_canonHeaderCall` and the fail-fast length guard
  (`binaryGuardTM`, `binaryGuard_done`, `binaryGuard_escape`);
- the canonical-header check (`canonBitsTM_run`, `exists_canonHeaderSeam`,
  `exists_canonHeaderBitsTM`, `exists_canonHeaderOKTM`), the nonoverflowing successor counter
  `exists_canonCountTM`, the block size `canonGuardBlock` with `decode_of_canonGuard`, and
  `canonGuard_run`;
- **the guard front end** (last round): from blank work tapes, `exists_canonReadySeam` prepares the
  header on tape 0, its successor count on tape 1 and the native remainder address
  `canonOffset (canonHeader α)` on tape 2; `exists_canonGuardFront` then seeks there, runs the guard
  and seeks back on success, in linear time, with the non-counter frame. Its limits are listed in
  your report: it assumes a successful pair decode, does not check the header's canonicality, and
  does not expose first-return cuts for both final ports.

**What remains** is your previous report's "Exact continuation frontier", steps 1–6 (below).

**Also this round (rule 10):** wrap the one line over 100 characters in `exists_canonGuardFront`.

**Read first:** your previous report (`audits/b5a-fill-agent-reports/canon-2-REPORT.md`), whose
frontier is written for you; the earlier briefs `briefs/b5a-fill-canon-cont.md`,
`briefs/b5a-fill-canon.md`, `briefs/b5a-fill-cont.md` and `briefs/b5a-fill.md` (routes, gate
guidance and pitfalls still bind); design §12.11; `CodeSimulator.lean` in full.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe, the import
probe `audits/evidence/b5a/B5aContPreShip.lean.txt` and the S1210 probe, re-run at the issue tree
(`audits/logs/b5a-fill-cont4-preship.log`): 0 errors.

## Owned files and targets (modify these and nothing else)

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:1945` | `Turing.MachineFormat.exists_polyCanonizer` | the proved front end; header validity; the generic record validator under one loop; emit or fall back | the proved loader, header check, counter, guard and front end |

- **Owned:** the regions of ground rule 1, and the style clean-up of rule 10. Nothing else.
- **Frozen (both B5a batches):** the six filled targets 3–8 and their privates
  (`twoTape_serialize_eq`, `twoTapeMachineFormat`, `expcom_padding_bound`); and, in
  `CodeSimulator.lean`, **all 188 privates** present at the issue tree: the first delivery's 17,
  the first continuation's 18, your 35 (`canonBitsOK` … `exists_canonGuardFront`), H1's 114
  (`h1RecordWidth` … `h1Round_effect`) and the four layout lemmas. Cite them; never change them,
  apart from rule 10's one-line wrap.
- **Not yours:** `MachineFormat.exists_uniformSimulator` and its gap (the H1 batch);
  `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `Codes2Tape.lean`, `EXPCOM.lean`, and
  the facades.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Compose by the public combinators**: R2 seams (`seamCompTM`, `seamReleaseTM`), the phase host
  (`phaseHostTM`), R1 embedding (`embedEmitTM`), the counter loop (`counterLoopTM`), the native-input
  seek (`exists_inputSeekTM`) and the install call (`FinTM.exists_installCallTM`). Do not write a
  hand controller for a phase that a public row provides.
- **The record validator is the reusable piece** (step 3 below): one generic component with its own
  contract, independent of `MachineFormat`, listed as a promotion candidate.
- **Install calls with arbitrary witnesses** may have coincident entry and exit anchors (the MIG-0a
  gate, round 1, minor 5): your `canonStrictInstall` handles that case; reuse it.
- **Pre-disclosed parallel overlap.** The H1 batch also walks canonized records (to seek one); the
  maintainer factors a common fixed-field walk later (backlog F7-1(c)). Do not try to coordinate.

### The frontier you inherit (your previous report's, binding)

1. **Attach total header validity and composable exits.** Reuse `exists_canonHeaderOKTM`, or the
   inherited lower-level pair and canonical-header contracts. Keep a failed pair decode distinct
   from an encoded empty header, and connect failure to the fixed fallback. Supply a separate,
   stronger composition contract with both first-return cuts needed for further branching. Do not
   change any landed statement; escalate if one would need revising. The preparation,
   installation and seek seams already have time-zero cuts; the composite guard-front contract
   does not provide them.
2. **Prepare the parser's binary bound after the guard.** Tape 0 still holds the original header.
   Recreate `canonCount bits` through the proved count machine and a public install call on a
   properly isolated bank; do not assume the guard restored tape 1 or its head. Protect the saved
   address and the other live words with the public frame. On success, the native head is already
   back at the remainder's beginning.
3. **The generic physical action-record validator** (a promotion candidate). Independent of
   `MachineFormat`, parameterized only by the work-tape count `k` and a tape-resident binary
   successor bound. Its success contract consumes exactly the prefix described by
   `codeSkipActionK k n`, leaves the native head at the returned suffix, preserves a reusable binary
   bound and the ambient frame, exposes distinct strict success and failure ports, and has a
   polynomial ledger uniform in `n` and the native input. Validate the fixed fields first
   (`codeSkipPair`, `k` repetitions of `codeSkipWork`, the output field), then the optional unary
   successor against the binary bound.
4. **The physical grammar.** Check the initial-state unary bound; run one public loop over the
   `(n + 1)·3^(k+1)` records, with the validator as its body; check the all-`true` suffix and keep
   the consumed-prefix boundary. The positive guard precedes any state-indexed work. Cite
   `guardedScan_eq`, `decode_of_grammar_guard`, `skipTable_consumes`, `codeSkipTableK` and
   `F.skipTable_eq`; do not copy the chapter-1 parser proofs.
5. **Emit and close the unchanged headline.** Copy the consumed prefix on success, emit exactly
   `F.serialize F.fallback` on every failure, apply `CodeFormat.canonical_eq` and the inherited
   bridges, and discharge the combined polynomial ledger.
6. **Note 50 on the full physical machine.** Execute a zero-format-guard case with the `2^128`
   header and a short remainder, an empty header, a malformed pair, and a small well-formed round
   trip.

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
   - **(a) New `private` declarations,** inserted in the blank gap at line 1875: after
     `exists_canonGuardFront` and before `exists_polyCanonizer`'s docstring (line 1876). `private`
     only, and no `section` or `open` that leaks past your region.
   - **(b) `exists_polyCanonizer`'s docstring,** lines 1876–1944. The existing text, including the
     earlier fill appendix, does not change. Append a flagged **Fill appendix** before the closing
     `-/`, as its own paragraph.
   - **(c) Its body,** the `sorry` on line 1948. The signature, lines 1945–1947, is frozen.
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
10. **Style clean-up of your own previous delivery** (backlog F7-1(e); this round only). In the
    declarations your previous delivery added (the 12 from `canonStrictInstall` to
    `exists_canonGuardFront`; one line over 100 characters, in `exists_canonGuardFront`), and
    nowhere else, you may change proof bodies **only** to remove Lean linter warnings (unused
    `simp` arguments, unreachable tactics, `<;>` where `;` suffices, no-op `omega`/`congr`, `simpa`
    → `simp`, unused variables) and to wrap lines over 100 characters. No statement, name,
    docstring or definition body changes; every such declaration must still elaborate. Report the
    before and after counts of linter warnings and over-width lines in those declarations, and list
    each declaration you touched.

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
  - your previous continuation's three in-file pairs (`exists_canonOffsetTM` against `exists_canonCountTM`, and `canonStrictInstall` against `exists_canonHeaderSeam` both ways; 57–68%, justified in `canon-2-REPORT.md`) are recorded; add nothing to them;
  - **the R1 configuration-reconstruction family** (backlog F7-1(b), the wave-1 gate's acknowledged major; one public lemma lands with MIG-0b): your `canonEmbedEq` is a member; cite it, never write another reconstruction proof;
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

- [ ] Rule 10: the linter warnings and over-width lines in your previous continuation's
      declarations, before and after, and the list of declarations touched.
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
