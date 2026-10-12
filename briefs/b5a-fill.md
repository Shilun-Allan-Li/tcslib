# Ch3–4 fill campaign — B5a: the format-parameterized code simulator, both uniform schemes, and `EXP ⊆ P^EXPCOM`

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`);
  - R8.0b (`counterLoopTMVia`, PR #38) and R8.6 (`expandTM_run_ofCfg`), both proved;
  - the §12.8 Catalog Part 3, Scan, InputCall and Seam rows, all proved;
  - this round's order lists, base sorry sets, screen bases and pre-ship logs.
  - the B5a statement layer (`TuringMachine/CodeSimulator.lean`) and its probe `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`;
  - this brief's order list `briefs/orders/b5a-fill.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/b5a`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b5a.zip`, containing
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

**Batch B5a** (plan §4e decision 2; `machine-library-design.md` §12.11). One format-parameterized
uniform interpreter discharges both frozen uniform schemes (EXPCOM's and ZF-B4's), so the
chapter-1 interpreter is not copied a third time. Fill:
- the two §12.11 rows: `MachineFormat.exists_polyCanonizer` and the headline
  `MachineFormat.exists_uniformSimulator` (**H1**);
- the two instances: `exists_uniformMachineCode` (EXPCOM, at `oneTapeMachineFormat`) and
  `exists_uniformMachineCode2` (ZF-B4, at a private two-tape format in `Codes2Tape`);
- `EXP_subset_POracle_EXPCOM`, the padding reduction (design D9);
- the three `EXPCOM` identities, which are short corollaries **proved modulo** B5's summit.

**Not yours:** B5's summit `NPOracle_EXPCOM_subset_EXP` (a later batch, B5b, after the oracle
layer lands). Leave its `sorry`.

**Read first:** `TuringMachine/CodeSimulator.lean` in full; design §12.11; the B5a probe (its
Part D derives both frozen targets from the two contracts: `uniform_one`, `uniform_two`); the
wave-1 findings and resolutions; `EXPCOM.lean` and `Codes2Tape.lean`; the P3.2 round-2 and
A-S2 audit records for the frozen schemes; `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):** the B5a probe and
`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`, re-run at the issue tree
(`audits/logs/w3-preship.log`): 0 errors; output identical to round 2's apart from R8.0b's three
generalized signatures. The S1210 probe derives the three identities.

## Design decisions settled for this brief (dossier recommendations; maintainer, 2026-10-11)

The design left D2 and D4–D9 to the fill brief. They are settled as the B5a dossier recommends:
- **D2, route Z:** `exists_uniformMachineCode` is the instance of H1 at `oneTapeMachineFormat`.
  Route W (the received `Universal` plus a post-processor) is an **escalation fallback only**:
  escalate rather than take it.
- **D3, H1** (user, 2026-10-11). H2 stays in `backlog.md`.
- **D4, sanctioned deletions in `Codes2Tape`:** the ZF-B3 semantic layer's private declarations
  may be deleted where the generalized layer replaces them, and moved, generalized, into
  `CodeSimulator` (the dossier counts 16 privates, 7 of which move). Keep
  `zfBFallback_serialize_length`, the 354-bit regression. List every deletion and move.
- **D5:** proved-modulo citations are allowed (§4e citation rule). Every §12.8 row the route
  needs is proved anyway.
- **D6:** the ND code scheme is a separate rider (`briefs/ndcodes-fill.md`), not yours.
- **D7:** the names and the home stand (`CodeSimulator.lean`, `Turing.MachineFormat`).
- **D8:** no facade change here (FAC-1 stays a 12.2c item).

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/CodeSimulator.lean:205` | `Turing.MachineFormat.exists_polyCanonizer` | binary-guard parser, fixed grammar, fallback | — |
| 2 | `TuringMachine/CodeSimulator.lean:239` | `Turing.MachineFormat.exists_uniformSimulator` | H1: one step block under `counterLoopTM`, hosted by Z1 | 1 |
| 3 | `TuringMachine/Codes2Tape.lean:547` | `Turing.exists_uniformMachineCode2` | instance of 1–2 at a private two-tape format (probe `uniform_two`) | 1, 2 |
| 4 | `Diagonalization/EXPCOM.lean:145` | `Complexity.exists_uniformMachineCode` | instance of 1–2 at `oneTapeMachineFormat` (probe `uniform_one`) | 1, 2 |
| 5 | `Diagonalization/EXPCOM.lean:201` | `Complexity.EXP_subset_POracle_EXPCOM` | one padded query (the docstring) | — |
| 6 | `Diagonalization/EXPCOM.lean:262` | `Complexity.POracle_EXPCOM_eq_EXP` | S1210 probe; modulo the summit | 5 |
| 7 | `Diagonalization/EXPCOM.lean:270` | `Complexity.NPOracle_EXPCOM_eq_EXP` | S1210 probe; modulo the summit | 5 |
| 8 | `Diagonalization/EXPCOM.lean:279` | `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` | S1210 probe | 6, 7 |

- **Owned:** `TuringMachine/CodeSimulator.lean`, `TuringMachine/Codes2Tape.lean` and `Diagonalization/EXPCOM.lean`, for these targets' bodies, new `private` declarations, the D4 moves, and the sanctioned imports.
- **Not yours:** `NPOracle_EXPCOM_subset_EXP` (in your file EXPCOM, but B5b's), `CodeFormat.lean`, `Universal*.lean`, `MathlibBridge.lean`, `NDCodes.lean` (parallel batch), `Relativization.lean` (maintainer PR), and the facades.
- Fill 1, 2, then 3–4, then 5–8.

### Proof routes (binding; the docstrings' sketches and design §12.11)

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
- **3–4, the instances.** Transcribe the B5a probe's Part D (`uniform_one`, `uniform_two`): each
  frozen structure's fields from the two contracts. The two assemblies are a forced mirror pair,
  as their target structures are. `exists_uniformMachineCode`'s docstring sketch predates route Z:
  add a flagged **Fill appendix** naming route Z.
- **5, `EXP ⊆ P^EXPCOM`.** The docstring's padding reduction: a fixed code `α_L := expCode.encode N`,
  `f x := pairEncode α_L (pairEncode x 1^(Q |x|))`, polynomial by the chapter-2 padding cluster,
  forced witnesses by `pairEncode_injective`, `Complexity.mem_POracle_of_polyTimeReducible`.
- **6–8.** The S1210 probe's derivations (`POracle_EXPCOM_eq_EXP'`, `NPOracle_EXPCOM_eq_EXP'`,
  `POracle_EXPCOM_eq_NPOracle_EXPCOM'`), each proved modulo `NPOracle_EXPCOM_subset_EXP`.

## Gate guidance (binding)

- **Minor 5** (zero guard), above.
- **Note 47:** the generic writer `tableBitsK` against the frozen serializers stays in the item-8
  residual family, with its bridges; it is not new debt.
- **Note 50:** permanent sanity cases **at fill**, executed in your evidence: zero-guard huge
  headers (canonizer), and exact-deadline acceptance (H1: a machine halting at exactly `t` steps
  with output `[true]` is accepted at deadline `t`).
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

## Ground rules (binding)

1. **File ownership.** Only `CodeSimulator.lean`, `Codes2Tape.lean` and `EXPCOM.lean`. Change only the eight targets' bodies (plus the D4 deletions and moves), and add new `private` helpers
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
6. **Imports.** **Sanctioned additions, exactly:** `import TCSlib.Complexity.TuringMachine.CodeSimulator` in `Diagonalization/EXPCOM.lean` and in `TuringMachine/Codes2Tape.lean` (both acyclic at the issue tree). Flag both. No other TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
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
10. **D4 moves** may add declarations to `CodeSimulator`: each is either `private` or a flagged public with one `## Main results` bullet; list every move with its old name.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/b5a-fill-screen-base.txt`:
**1,420 declarations, 1,769 pairs, 582,877 characters**.

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
  - `universalInterpreter` and the `Universal*` files: never copy their step or parse proofs (the one interpreter trace is new and generic);
  - the ZF-B3 layer in `Codes2Tape`: generalize and move it (D4), never duplicate it;
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
- **Bootstrap once** from `briefs/orders/b5a-fill.txt` (**77 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/b5a-fill.txt )
  ```

  **Base sorry-warning set, 43** (`audits/logs/b5a-fill-base-sorries.txt`, one entry per declaration).
  Yours: `CodeSimulator` 2, `Codes2Tape` 1, `EXPCOM` 6 minus the summit (5). Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**35** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`: 0 errors.
  4. Re-run `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`: 0 errors, its census still detecting the summit.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine and TCSlib/Complexity/Diagonalization (two runs)`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `ClassOracle/Classes`: POracle_eq_P_of_mem_P
- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `Diagonalization/Relativization`: baker_gill_solovay
- `TuringMachine/NDCodes`: exists_effectiveNDMachineCode
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/InputLength`: exists_inputLengthTM
- `TuringMachine/Build/RecordTable`: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/Build/CertShell`: FinTM.exists_certificateShell
- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
- `Diagonalization/EXPCOM`: `NPOracle_EXPCOM_subset_EXP` (B5b; leave it)

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 8/8, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.
- [ ] D4: every deletion and move. Note 50: the two executed sanity cases.

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
