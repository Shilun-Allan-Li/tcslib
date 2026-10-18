# External audit pack — 12.2c tranche T1, item 8 (CH34-D2): the format-parameterized machine-code parse layer

Campaign: Arora-Barak chapters 3-4. **12.2c** is the maintainer's refactor
window, run as three tranches (`AroraBarakChapters3-4Plan.md` §4e). Each
tranche gets a PR the user merges and **its own audit gate**. This item
discharges the human-acknowledged debt **CH34-D2** (`backlog.md`;
`audits/duplication-ledger.md`): after ZF-B2, 23 two-tape declarations of
`Codes2Tape.lean` were structural copies of `CodeParser.lean`'s and
`MathlibBridge.lean`'s one-tape top layer, and `NDCodes`' pending ND scheme
would have needed a third copy.

The change is PR #19 (`integrate/12.2c-t1-codeformat`): Codex commits
`603b3a35` (the shared layer and the one-tape side) and `beb76cdb` (the
two-tape instance), on base `b4be0717`, plus the maintainer's records commit.
**Statements are frozen.** The gate closes on zero blockers and zero majors.
The duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

## What changed (verify)

- **New `TuringMachine/CodeFormat.lean`** (45 public, 3 private), with three
  levels:
  - **T:** the structure `Turing.CodeFormat` over the *table* grammar, and the
    generic `parseFull`, `decode`, `scan` and `canonical` with their laws;
  - **R:** a record reader generic in the work-tape count `k`, built with
    `codeReadVec`;
  - **W:** the shared 27-record two-work-tape table.
- **Instances.** `CodeParser`'s one-tape names (`codeDecode`, `codeScan`,
  `codeCanonical`) become one-format instances, with their statements
  verbatim. `Codes2Tape`'s format is `twoTapeFormat`. The generic primrec and
  canonizer lemmas live in `MathlibBridge`.
- **The move.** `workPair` and `actionBits₂` move verbatim from the chapter
  file `NDCodes.lean` into `CodeFormat.lean`, with one import added to
  NDCodes. This is the maintainer's sanctioned exception; its purpose is
  that their bridge lemma exists once, not as a forced duplicate.
- **Deletions:** 16 in CodeParser, 3 in MathlibBridge and 21 in Codes2Tape,
  among them the dead `codeParse_sound`, `codeAllTrue_eq` and
  `codePairDecode_sound`.
- **Facade.** `TuringMachine.lean` gains the `CodeFormat` import and one
  Contents bullet (sanctioned).
- **Frozen surface.** All 79 base public statements are byte-identical; the
  public-name comparison runs over the union of files, because names move.
  The 44 new publics are exactly the brief's list, and their statements match
  the maintainer's pre-ship probe. Only the brief's sanctioned changes appear:
  definition and proof bodies, docstring appendices, one private statement,
  and imports.

## Brief for the auditor

1. **Freeze over the union.** From the attached base and after sources,
   confirm:
   - every base public declaration still exists, possibly in another file,
     with a byte-identical statement;
   - the definitions whose bodies changed are exactly the sanctioned three;
   - no consumer outside the six files was edited.
2. **The abstraction.** Blind-restate `Turing.CodeFormat` and each new public
   declaration.
   - Are the structure's fields and laws exactly what the generic proofs
     need, with nothing format-specific hidden in them?
   - Do the one-tape and two-tape instances satisfy them honestly (no law
     discharged by `sorry` or by a trivializing choice)?
   - Will the ND format, `NDCodes`' pending `exists_effectiveNDMachineCode`,
     fit as a third instance without new generic machinery? Its sketch is
     attached in `NDCodes.lean`.
3. **Re-derivations.** For each public theorem whose proof now instantiates
   the generic layer (for example `codeDecode_serialize_pad` and the two
   effective schemes), confirm that the instantiation is genuine and the
   statement unchanged.
4. **The move.** Confirm that `workPair` and `actionBits₂` are verbatim, that
   every former consumer resolves to the same constants, and that the
   exception is justified (no forced duplicate remains).
5. **Duplication (failure mode 5).** The screen over CodeParser, CodeFormat,
   Codes2Tape, NDCodes, MathlibBridge and Encoding goes from 117 pairs /
   29,824 characters to 77 / 12,563. All CH34-D2 member pairs are gone.
   - Of the 28 new pairs, 25 are on the brief's pre-sanctioned list. These
     are the generic layer resembling the frozen one-tape definitions it
     bridges, for example `actionBitsK` ↔ `actionBits`, `codeSkipActionK` ↔
     `codeSkipAction`, and the table writer against the frozen `serialize`
     bodies.
   - Three are unlisted, all in-file and under 90%:
     `codePrimSkipTable1` ↔ `codePrimSkipTable2` (67% and 54%), and
     `zfB3_decode_length` → `zfB3_decode_states` (50%).

   Is CH34-D2 discharged? Is any remaining pair a copy that should have been
   factored? Are the pre-sanctioned resemblances forced by frozen bodies, as
   claimed?
6. **Downstream.** 23 modules, with `Codes2Tape` checked directly because no
   facade imports it. The sorry set is unchanged by module and declaration:
   22, the delivery's 23 minus C1d's since-proved enumeration. Confirm from
   the logs.
7. **Docstrings.** Report any docstring made false. Check the new module's
   documentation, the appendices, and the stale references in
   `MathlibBridge` and `CodeParser` to deleted private names.
8. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Integrity.** The zip's `SHA256SUMS` is OK (the zip is not attached). The
  C shim is excluded and unreferenced. The integrated files are
  byte-identical to the delivered sources.
* **Freeze** (`audits/logs/12.2c-t1-codeformat-freeze.log`, the union
  comparison).
* **Replay** (`…-replay.log`): 23 modules, 0 errors at both commits.
* **Axioms** (`…-axioms-{base,after}.{lean.txt,log}`):
  - the 79 pre-existing prints are byte-identical after;
  - the 44 new ones are within the standard triple;
  - `sorryAx` appears only on `exists_effectiveNDMachineCode` and
    `exists_uniformMachineCode2`, as at base.
* **Lint** (`…-stylelint.log`): 0 FAIL.
* **Screens** (`…-screen-{before,after}.txt`). The screen script and all
  screened sources are attached at base and after.
* **A stale legacy program, out of scope.**
  `audits/programs/ch1-infra-BridgeExportAxioms.lean` fails identically at
  base and after, because it still expects `TMSAT_mem_NP` to be sorried,
  which it has not been since 2026-10-04. It is queued for a refresh.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/12.2c-t1-codeformat-findings.md`.
