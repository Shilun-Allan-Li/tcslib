# The MIG-11a statement gate (PR #117): resolutions

**Gate:** PR #117, MIG-11a, the row contracts that MIG-12 composes.
- Pack: `audits/mig11a-statements-pack.md`.
- Bundle SHA-256: `84d0442fccfaea170d4428fe01d71fb16fe31ff50f615e2229a818925551b99b`
  (39 sections; folder `infra_local/gate-dispatches/33-mig11a-statements-gate/`; Lean from
  `1358ff73`, everything else from `455cb240`).

## Result

The findings are in `audits/mig11a-statements-findings.md`, verbatim. **PASS: 0 blockers,
0 majors, 2 minors, 0 notes. The gate is CLOSED (2026-10-16).**
- The auditor could not run Lean, so its elaboration and axiom results rest on the supplied
  evidence.
- It reproduced the patch blobs, the freeze, and both copy-text screens byte for byte.
- It checked the contracts by hand at the boundary instances and by a finite transition model
  (all binary words up to length 4 or 5).

The maintainer's review sub-agent verified both findings against the head `1358ff73`
(`audits/evidence/mig11a/gate/gate-review.md`). Both are true, at the auditor's severity.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `counterRowContract`'s docstring calls `fix` width-preserving and says the endpoint holds `v`, but nothing requires `\|v\| = \|w\|`. The endpoint writes `bufferTape v` only within the old word's interval. | **True; fixed in `98472df2`, docstring only.** The docstring now states what `post` writes: `bufferTape v (q - pos)` on `[pos, pos + \|w\|)`, every other cell unchanged. It also says that no width condition is assumed, and that the interval holds exactly `v` when `\|v\| = \|w\|`, as for both instances.<br>No width hypothesis is added, on the review's advice: the generic contract is exact without one, and the instances gain nothing from it. The instances' docstrings are true as they stand, because `incFixed` and `decFixed` keep the width.<br>The patch is the review's `gate/repair-docstring.patch` (SHA-256 `c6f1c51e…7842`), applied unchanged. **Checks:**<ul><li>`Contract/Counter` re-elaborated against `oleans-lm11a`, 0 errors and 0 warnings (`gate/elab-ContractCounter-docfix.out`);</li><li>no line over 100 characters;</li><li>freeze: no statement changes;</li><li>lint unchanged.</li></ul> |
| 2 | minor | The lint log does not describe the final counter module: 122 lines and 2 public, against 131 and 3. | **True.** The log was taken before `counterRowContract` was factored out, and before #116 merged; hence its 72 WARN. It is kept as is. **The corrected attestation**, re-run by the review at `1358ff73` (`gate/lint-head-1358ff73.txt`):<ul><li>**0 FAIL, 69 WARN over 79 files**, the same WARN set as the tip `f139d21a`;</li><li>`Contract/Counter`: 131 lines, 3 public, no WARN;</li><li>check 8 lists none of the six new definitions.</li></ul>The result is the same with the docstring fix (`gate/lint-repaired.txt`). `NOTES.md` and the PR body are corrected. |

## The auditor's answers to the pack's questions, carried forward

- **Design.**
  - The exits are both verdicts (a range). A singleton could not express the cut against
    premature dispatch at either flag.
  - The counter rows are indexed by `(w, v)`, which gives a total endpoint.
  - The factored constructor and the module's placement are sound.
- **Coverage for MIG-12.**
  - The four rows are the right ones, and no leaf-contract field is missing.
  - The frames of the compare and the counter rows follow from their `_post` equations and
    `Contract.frames_iff`, without unfolding.
  - Named `_frames` lemmas would be convenient but are not needed.
  - `RecordRun`'s common radius comes from the envelopes, `Contract.segment` and `Segment.mono`.
  - The counter loop's escape stays MIG-15's declared exception.
- **The row counts in `audits/evidence/mig12/DESIGN.md` include prose mentions.**
  - The proof call sites in `CfgRecord` are:
    - copy: 2 (lines 1779 and 3474);
    - compare: 1 (4804; the mention at 4551 is prose);
    - increment: 1 (2924);
    - decrement: 1 (2923).
  - The design note now says so.
- **The width lemmas (from the review).**
  - `decFixed`'s width is public in effect, through `counter_dec_spec` (`CounterLoop`).
  - `incFixed`'s is only the private `rt_incFixed_length` (`RecordTable`).
  - MIG-12 needs neither, because its arithmetic transport takes `v.length = w.length` as a
    hypothesis.
  - **Backlogged:** publish `incFixed_length` and `decFixed_length` beside their definitions,
    and have the private copies `rt_incFixed_length` and `sc_dec_success_width` cite them.

## The replay and the stack

- **The replay covers the head's Lean:**
  - #117's replay `replay-lm11a.log` ran at `b131d239`: 86 of 86, 0 failed, sorry sum 57;
  - no `.lean` file differs between `b131d239` and `1358ff73`;
  - `98472df2` changes one docstring, and its module was re-elaborated as above.
- **The stack.** #118 is stacked on `1358ff73` and does not touch `Contract/Counter`, so it
  merges cleanly after #117. Its replay snapshot `oleans-lbapi` carries the old docstring, and
  nothing downstream reads it.

**PR #117 is ready to merge (head `98472df2`), before #118.**
