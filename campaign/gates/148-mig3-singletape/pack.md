# Gate 148 · Closeout MIG-3: `one_work_tape` through the demand-grown witness (PR #337)

**Not yet clear to merge** · PR #337 is a draft. Seyoon dispatches and merges.

- Lean head: `fed2c719f935ff7f3c4875c7c680e534b4779c78`.
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

Net: **−444 Lean lines**.

**History.** The witness is a changed declaration, so the base proof's legacy reads in it became
exposed. At the first head, `8e89f6e6`, the sealed check failed at four sites:
- three bare `intro x`/`intro y` steps that unfold `ComputesFunInTimeVia`;
- one that unfolds `ComputesFunInTime`.

There were also applications of a `ComputesFunInTime` value to `x`, and the empty-alphabet case
evaluated the halting machine's step by `rfl`. The head `fed2c719` reads all of them through
`computesFunInTimeVia_iff`, `computesFunInTime_iff`, `MultiTapeTM.step_of_some`,
`Action.apply_state`/`_output` and `Cfg.init_state`/`_output`, which is also how the old
time-only `one_work_tape` proof read them. The failing seal lines are in the carrier
(`history/head1-8e89f6e6/`).

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
6. **Copy screen** (population: SingleTape): see `evidence/PAIR-DISPOSITIONS.json` and the note under Evidence.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of SingleTape's downstream closure on
  `oleans-c68cb`.
  - 328 modules replayed: 328 passed, 0 failed.
  - The 28 inherited admissions are pre-existing ones from `main` (RAMSimulation, RecordTable,
    Expanders).
  - A run at the first head also passed 328/328. An earlier attempt failed one module during a
    disk-full moment (an empty log) and was discarded.
- **Seals:** the 4 changed proofs (`dg_all_inputs`, `one_work_tape_witness`, `one_work_tape`,
  `one_work_tape_spaceUsed`) pass with every other-file definition they reach made irreducible
  (17 heads).
- **Controls:** 20 definitions' 40 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 4 roots, 0 explicit reads.
- **Lean-backed sweep:** 44 identifiers, 0 foreign definitions.
- **Lint:** no new finding. The deleted sweep blocks' missing-sketch findings are removed.
- **Copy screen:** 12 directed pairs gone and 2 new. The new ones are one unordered pair:
  `one_work_tape` and `one_work_tape_spaceUsed`, both two-line readers of the witness (obtain, then
  the anonymous constructor). This is disclosed, not copied logic. Judge whether it is acceptable.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate148-mig3-singletape-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
