# Gate 148 · Closeout MIG-3: `one_work_tape` through the demand-grown witness (PR #337)

**Not yet clear to merge** · PR #337 is a draft. Seyoon dispatches and merges.

- Lean head: `8e89f6e69616fff8e16286468ce5b20eb5e26e00`.
- Base: campaign Lean `68cba664`, records `967cde57`.
- This is the first audit. The PR is independent of #334–#336.

## Scope

Wave R6, item MIG-3 (`campaign/closeout/R3-R6-MEASUREMENT.md`, bundled). It was done under the
overnight cleanup authorization of 2026-11-16, in Seyoon's file
`TuringMachine/Robustness/SingleTape`. No statement changes.

The file proved [AB09, Claim 1.6] twice:
- The first sweep witness (`sweepTM` run through `sweep_run_to_halt`) proved the time-only
  `one_work_tape`.
- The demand-grown witness (`dgTM`) proved `one_work_tape_spaceUsed`. It was added after audit
  A-S2-2 found that the first witness fails the space bound.

This PR proves both through the second witness:

- `dg_all_inputs` (private): the space hypothesis `hS` moves from the parameters into the space
  conjunct (`∀ S, hS → …`); the time conjunct never used it. This is listed as `header_changed`.
- New private `one_work_tape_witness`: the former body of `one_work_tape_spaceUsed`, with its
  space clause quantified over every source space bound. Its three cases are unchanged:
  - `k = 0`: the unused-tape embedding;
  - nonempty `Γ`: `dgTM` with the finite-control retraction;
  - empty `Γ`: the halting machine.
- `one_work_tape` and `one_work_tape_spaceUsed` keep their statements and read their witness off
  the new lemma.
  - `one_work_tape`'s docstring now describes the demand-grown witness. The same tag,
    [AB09, Claim 1.6], applies.
  - `one_work_tape` and `one_work_tape_binary` move below the witness. Their names are unchanged
    and `one_work_tape_binary`'s text is unchanged, so its external consumers are untouched.
- **Deleted**, now unreferenced: `sweep_run_to_halt`, `sweep_step`, `sweep_finish`,
  `sweep_prepare`, `sweep_init`, `sweep_init_block`, `sweep_grow_left_block`,
  `sweep_grow_right_block`, `sweepStart`, `sweepInput_read`, `sweepPos`, `sweepPos_move`,
  `tapeRow_blank`.
- **Kept:** `sweepTM`, the shared sweep layer and its two private instances (typeclass search
  uses them). `dgTM` is built on them.

Net: **−451 Lean lines**.

## Brief for the auditor

1. **Statements.** Confirm that `one_work_tape`, `one_work_tape_binary` and
   `one_work_tape_spaceUsed` are byte-identical in statement to base. `dg_all_inputs`'s header
   change is the only private statement change.
2. **Witness.** Check that `one_work_tape_witness`'s three cases are the base proof's, and that
   the time clause uses no space hypothesis.
3. **Docstrings.** Check that `one_work_tape`'s revised proof sketch is faithful to the
   demand-grown construction (policy §3).
4. **Deadness.** Check that each deleted declaration was referenced at base only from the deleted
   set or from `one_work_tape`'s old body.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below).
6. **Copy screen** (population: SingleTape): see `evidence/PAIR-DISPOSITIONS.json`.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of SingleTape's downstream closure on
  `oleans-c68cb`. REPLAY-PLACEHOLDER
- Seals, controls and sweeps: CHECKS-PLACEHOLDER
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate148-mig3-singletape-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
