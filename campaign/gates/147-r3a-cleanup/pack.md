# Gate 147 · Closeout R3a: SK-1, dead privates, two citations (PR #336)

**Not yet clear to merge** · PR #336 is a draft. Seyoon dispatches and merges.

- Lean head: `5da18960590c223ce384470e7d0d8870641f881c`.
- Base: campaign Lean `68cba664`, records `967cde57`.
- This is the first audit. The PR is independent of #334, #335 and #337.

## Scope

This is the first slice of wave R3: the families that the R3–R6 what-if seal
(`campaign/closeout/R3-R6-MEASUREMENT.md`, bundled) found with zero rule-10 exposure. It was done
under the overnight cleanup authorization of 2026-11-16. Every change is private and in Seyoon's
files. No statement changes.

- **`TuringMachine/UniversalK`, SK-1:**
  - deletes `ss_captureInitial`, whose statement is identical to `Build/InterpreterStartup`'s
    public `embedSilentCfg_initCfg`;
  - its only use, `ss_capture_run`, now cites the public lemma.
- **`TuringMachine/CodeSimulator`:**
  - deletes `canonCounterRepeat` (CC7-1), which was unreferenced (101 lines);
  - `canonStageBuffer_none` (RC-4, buffer half) keeps its name and statement and is now a
    one-line citation of `FinTM.bufferTape_eq_none_of_not_mem`.
- **`ClassNP/ExhaustiveReplay`, C1E-1:**
  - deletes the unreferenced `xr_firstArrival`; the live variant is `xr_firstArrival'`, and the
    leaf-rows note now names it;
  - `xr_bufferTape_ge` is unchanged: this file does not import `TuringMachine/BufferWords`.
- **`ClassNP/Nondeterminism`:**
  - **MIG-8:** deletes the unreferenced chain `e3_split_of_body`, `a3n_prevalidation`,
    `e3SplitStep`, `e3SplitAccept`, `e3_step_inv`, `e3_step_orbit`, `e3_find_congr`,
    `e3_find_eq`, `e3_loop_result` and `e3_loop_bound`;
  - **PL-1:** `a3n_poly_linear` keeps its statement and now cites
    `polyTimeComputable_of_linear`;
  - **Kept on purpose:**
    - the four lemmas the module's E5 note retains as audited evidence
      (`cont_poly_guess_phase`, `b2_unary_mask`, `b2_tables_coincide`,
      `certificateSplit_complete`);
    - two further unreferenced lemmas outside the ledger's MIG-8 list (`a3n_poly_fixed_eq`,
      `e3_bits_length_bound`).

Net: **−303 Lean lines**.

**Known residue.** Two historical module notes in Nondeterminism still name the deleted
`e3_split_of_body` (epoch-3A appendix) and `a3n_prevalidation` (A3 completion note).

- The first head (`944bbf9c`) edited both notes. That changed the text chunks of the public
  `ntime_expPow_subset_NEXP` and `EXP_eq_NEXP_of_P_eq_NP`, whose untouched proofs destructure
  `NTIME`/`NEXP` membership anonymously, so the sealed check failed on them (history in the
  carrier).
- Repairing them needs reader API for `NTIME`/`NEXP`, which is outside this PR. The notes are
  restored instead, at `5da18960`.
- Clean them up when those proofs are next touched (recorded in the ledger).

## Brief for the auditor

1. **Deadness.** Check that every deleted declaration was unreferenced at base, outside comments
   and outside the deleted set. The base sources are in the carrier.
2. **Citations.** Check that each kept private's statement equals, or is implied by, the cited
   public lemma.
3. **Rule 10.** The 3 changed proofs (`ss_capture_run`, `canonStageBuffer_none`,
   `a3n_poly_linear`): seals, controls and both sweeps (counts below).
4. **Copy screen** (population: the four owners): no new pair; one gone
   (`evidence/PAIR-DISPOSITIONS.json`).
5. **Records.** Check that the measurement note, the ledger and this pack agree.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the four changed
  modules, on `oleans-c68cb`: 46 modules, 46 passed.
- **Seals:** the 3 changed proofs pass with every other-file definition they reach made
  irreducible (9 heads, all three owners with a changed proof). ExhaustiveReplay has only
  deletions.
- **Controls:** 16 definitions' 32 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 3 roots, 0 explicit reads.
- **Lean-backed sweep:** 0 foreign definitions.
- **Lint:** no change.
- `history/head1-944bbf9c/` in the carrier holds the first head's failing seal lines (the
  known-residue paragraph above), and `patch/head1-to-head2.patch` the restoring diff.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate147-r3a-cleanup-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
