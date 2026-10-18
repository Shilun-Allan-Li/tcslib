# Ch3–4 fill campaign — the ND code scheme rider (`Turing.exists_effectiveNDMachineCode`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`
  succeeds. That commit contains:
  - the closed wave-1 statement gate (PR #43) and its records (`audits/wave1-statements-*`);
  - 12.2c T1 item 8 (the format-parameterized parse layer `CodeFormat`) and its closed gate (`audits/12.2c-t1-codeformat-*`);
  - this brief's order list `briefs/orders/ndcodes-fill.txt` and pre-ship probe `audits/evidence/ndcodes/NDCodesRiderProbe.lean.txt`.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/ndcodes`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ndcodes.zip`, containing
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

Fill `Turing.exists_effectiveNDMachineCode` (phase P3.3; audited true), the nondeterministic
mirror of `exists_effectiveMachineCode`. It was blocked on a format-parameterized parse layer;
12.2c item 8 landed it (`CodeFormat`), and that gate's note 11 records that the ND scheme **fits
as a third instance without new generic machinery**. Its consumers are the NTIME hierarchy
(group C1) and ZF-B4's two-tape scheme.

**Read first:** `NDCodes.lean`; `CodeFormat.lean` (the structure, `decode`,
`decode_serialize_pad`, `canonical_eq`, the two-tape table layer); `MathlibBridge.lean`'s
`CodeFormat.exists_canonizer` and `exists_effectiveMachineCode` (your template); the P3.3 audit
records (findings 3 and 4); `audits/12.2c-t1-codeformat-resolutions.md` (note 11); `policy.md`;
`workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/ndcodes/NDCodesRiderProbe.lean.txt` (`audits/logs/w3-preship.log`): 0 errors. It
imports `NDCodes` with `MathlibBridge`, and proves the route's central law: `CodeNDTM.serialize`
is the state count, the unary initial state, then the `false` and `true` choice tables in
`codeTable2Bits` order (`probe_ndSerialize`, one `simp`, axioms `[propext, Quot.sound]`). It
`#check`s every row below.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/NDCodes.lean:179` | `Turing.exists_effectiveNDMachineCode` | a private `ndFormat : CodeFormat`, then `exists_canonizer` | — |

- **Owned:** `TuringMachine/NDCodes.lean`, for the target's body, new `private` declarations and the sanctioned import.
- **Not yours:** `CodeFormat.lean`, `MathlibBridge.lean`, `Codes2Tape.lean` (B5a; its private `twoTapeFormat` is a model, not citable), and the facade.

### Proof route (binding; item-8 gate note 11 and the B5a dossier's D6)

1. **Import** `TCSlib.Complexity.TuringMachine.MathlibBridge` (sanctioned: acyclic; it adds
   `TMToPartrec` to NTIME's closure).
2. **A private `ndFormat : CodeFormat`**, the third instance:
   - `Code := CodeNDTM`; `Table n := CodeTable2 n × CodeTable2 n`, the `false` choice first;
   - `assemble n q (t₀, t₁)` the two-work-tape NDTM with initial state `q` whose choice-`b` table
     is `t_b` (read `workPair`'s two cells), and `numStates` its state count;
   - `serialize := CodeNDTM.serialize`; `tableBits (t₀, t₁) := codeTable2Bits t₀ ++ codeTable2Bits t₁`;
   - `readTable` by `codeReadTable2` twice; `skipTable` by `codeSkipTable2` twice;
   - `guard := 702` (twice the two-tape `351`), `fallback` the single-state do-nothing NDTM.
   - The laws: `serialize_assemble` is the probe's `probe_ndSerialize`; the reader laws from
     `codeReadTable2_append`, its soundness and erasure lemmas, twice; `tableBits_length` from
     `codeTable2Bits_length` twice; `assemble_surj` by `workPair`'s extensionality over `Fin 2`.
3. **The scheme:** `encode := CodeNDTM.serialize`, `decode := ndFormat.decode`,
   `decode_encode_pad` from `CodeFormat.decode_serialize_pad`, and the canonizer from
   `ndFormat.exists_canonizer`, whose `Primrec₂ ndFormat.skipTable` comes from `codePrimRepeat` and
   `codePrimSkipTable2`. The canonizer is **arbitrary-time** (P3.3 round-1 finding 4): no
   polynomial ND canonizer is claimed or needed.
4. The docstring's sketch names the received `CodeParser` retargeted; add a flagged **Fill
   appendix** naming this route through `CodeFormat`.

## Gate guidance (binding)

- **P3.3 round-1 finding 3:** the table is `2 · 27 = 54` records per state; the guard scales
  accordingly.
- **Finding 4:** the canonizer takes the arbitrary-time computability route of the received
  construction; `canonizerTime` is arbitrary.
- **Item-8 note 11:** no new generic machinery; the ND scheme is an instance.

## Cited infrastructure (public and proved at the issue commit)

`CodeFormat` and its lemmas; `CodeTable2`, `codeTable2Bits`, `codeReadTable2`, `codeSkipTable2`,
`codeReadTable2_append` and the two-tape soundness, erasure and length lemmas;
`actionBits₂_eq_actionBitsK`; `workPair`; `MathlibBridge`'s `codePrimRepeat`, `codePrimSkipTable2`,
`CodeFormat.exists_canonizer`, `CodeFormat.primrec_scan`. **Proved modulo: none.**

## Ground rules (binding)

1. **File ownership.** Only `NDCodes.lean`. Change only the target's body, and add new `private` helpers
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
6. **Imports.** **Sanctioned addition, exactly:** `import TCSlib.Complexity.TuringMachine.MathlibBridge`. Flag it. No other TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it; flag
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
**Duplication**). The base, at this brief's issue tree, is `audits/logs/ndcodes-fill-screen-base.txt`:
**177 declarations, 82 pairs, 13,040 characters**.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/NDCodes.lean \
  TCSlib/Complexity/TuringMachine/CodeFormat.lean \
  TCSlib/Complexity/TuringMachine/MathlibBridge.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/CodeParser.lean \
  TCSlib/Complexity/TuringMachine/CodeSimulator.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it).
- **Known hazards:**
  - **pre-disclosed:** `ndFormat` against `oneTapeFormat` (CodeFormat) and `Codes2Tape`'s private `twoTapeFormat`: instance boilerplate, a forced pair; measure and report it;
  - any parser, reader or skipper: use `CodeFormat`'s, never a private copy (that was CH34-D2's debt);
  - the canonizer assembly against `MathlibBridge`'s `codeCanonical_machine`: cite `exists_canonizer`.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ndcodes-fill.txt` (**77 modules**: the upstream closure of
  your owned files and of every module downstream of them, at the issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ndcodes-fill.txt )
  ```

  **Base sorry-warning set, 43** (`audits/logs/ndcodes-fill-base-sorries.txt`, one entry per declaration).
  Yours: `NDCodes` 1. Record the base list by name first. If anything else has landed by your base
  (a parallel batch, or the maintainer's corollary PR), report the difference.
- **Final checks:**
  1. Your owned modules: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**42** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/ndcodes/NDCodesRiderProbe.lean.txt`: 0 errors.
- **Axiom prints** for every target: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` only through a named proved-modulo citation.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `ClassOracle/Classes`: POracle_eq_P_of_mem_P
- `TuringMachine/Build/CfgRecord`: exists_recordStepTM
- `Diagonalization/EXPCOM`: exists_uniformMachineCode, EXP_subset_POracle_EXPCOM, NPOracle_EXPCOM_subset_EXP, POracle_EXPCOM_eq_EXP, NPOracle_EXPCOM_eq_EXP, POracle_EXPCOM_eq_NPOracle_EXPCOM
- `Diagonalization/Relativization`: baker_gill_solovay
- `Diagonalization/NTimeHierarchy`: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
- `TuringMachine/Build/InputLength`: exists_inputLengthTM
- `TuringMachine/Build/RecordTable`: joinFields_length, fieldOffset_length, joinFields_cfgRecord_length, cfgRecord_field_ne_nil, cfgRecord_init, recordValid_iff_exists_cfg, joinFields_recordTemplate_length, binDigits_posWidth_succ, TableWF.field_ne_nil, tableOffset_eq, tableOffset_length, TableAt.recordAt_take, tableRewindTM_run_ofCfg, exists_fieldsCopyTM, exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
- `TuringMachine/Build/CertShell`: FinTM.exists_certificateShell
- `TuringMachine/Build/OracleSim`: FinOracleTM.exists_plain_simulation, FinOracleNDTM.exists_choiceTM
- `TuringMachine/CodeSimulator`: exists_polyCanonizer, exists_uniformSimulator
- `TuringMachine/Codes2Tape`: exists_uniformMachineCode2

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; every target's axiom print; the lint
      line. The diff touches only your owned files.

## Known pitfalls at this pin (hard-won)

- `CodeNDTM.serialize` uses `actionBits₂`; `codeTable2Bits` uses `actionBitsK`. They agree by
  `actionBits₂_eq_actionBitsK` (the probe's `simp` set).
- `workPair w₀ w₁ : Fin 2 → Option Bool`; recover `w = workPair (w 0) (w 1)` by `funext` and
  `Fin.cases`/`fin_cases`.
- `NDCodes` is imported by `Codes2Tape`: you cannot import or cite anything of `Codes2Tape`.
