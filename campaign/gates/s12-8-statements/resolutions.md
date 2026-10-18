# §12.8 statement gate — resolutions (CLOSED, round 2)

## Round 1 (2026-10-11): 0 blockers, 1 major, 7 minors, 39 notes

The findings are verbatim in `audits/s12-8-statements-findings.md`; the pack
is `audits/s12-8-statements-pack.md`. The auditor:

- found every framed row, the scan and its five identities,
  `cfgRecord_inj`, `recordValid_iff`, the two-exit seam and the transport
  true as stated, with degenerate and adversarial checks;
- confirmed the freeze from the patch;
- reproduced both screens byte for byte;
- checked the replay, probe, axiom and lint logs for internal consistency.

The major blocks the gate.

| Finding | Disposition |
|---|---|
| **1 (major)**: `exists_recordStepTM` and `exists_inputSeekTM` bound time and restore tapes, but bound no visited work cells. An admissible detour costs `Θ(n)` scratch cells at `L = Θ(log n)`, so Savitch and logspace consumers cannot use them | **Repaired.** Every record row and the input seek now bound each work head, through the verdict or exit, to `C·(size + 1)` cells of its entry position: `|pos_u − pos_0| ≤ C·(L + 1)`, `C·(\|joinFields fs\| + 1)` and `C·(\|w\| + 1)`. This is a fixed interval about the entry heads, independent of native-head travel, so repeated calls compose. The auditor asked for the step and the seek; the equality and test rows get the same clause, so that all record rows are uniform. Docstrings and sketches are updated. Round 2 re-audits the strengthened statements |
| 2 (minor): the input seek's rewind route is off by one | **Swept.** `timed_rewind` stops at position `1` within `pos + 2`, and one left move follows |
| 3 (minor): the input call's first-return proof lacks the callee's time-zero cut | **Swept.** Split on entry = exit, with `seamReleaseTM_firstReturn` in that branch |
| 4 (minor): `recordValid_iff`'s "each conjunct is a one-field fold" needs a uniformity qualification | **Swept.** Folds plus supplied width and bound templates. The validator stays deferred |
| 5 (minor): `Cfg.InWindow`'s added sentence says a record determines the configuration | **Swept.** It determines the configuration *core*, together with its separately supplied tag |
| 6 (minor): `fieldOffset`'s end formula fails at `fs = []` | **Swept.** Qualified by `fs ≠ []`, and the empty offset stated |
| 7 (minor): the declfreeze log says "4 occurrences" of the promoted name; it is 3 | **Erratum.** The count is 3, one in each of `seamComp_right`, `seamComp_firstReturn_general` and `seamComp_visited_general`. The issued log is preserved as issued |
| 8 (minor): Catalog's ledger denominator predates this layer | **Corrected.** The ledger's new §12.8 section gives 318/459 = 69.3% (strict 283/459 = 61.7%), and keeps the R1 snapshot |
| 28 (note): name the saved-input-position and clamping obligations | **Done** in the step row's sketch |
| 35 (note): the pack's input-seek nonvacuity argument needs its witness | **Corrected here.** `entry ≠ exit` follows at `x = []`, `w = []`, `p = 0` from an entry at input position `1`: the required move forces `t > 0`, and then the `u = 0` cut excludes `exit = entry`. The cut alone does not give it when `t = 0` |
| 32 (note): do not apply the transport's run or space theorem to configurations with foreign symbols on their selected tapes | Recorded as consumer guidance. Isolate the dedicated digit tapes by R1 |
| 38 (note): record the same-file similarities | **Done** in the ledger's §12.8 section |
| 39 (note): the evidence boundary | Accepted. Round 2's pack attaches the facade and `ConfigGraph.lean` |
| 41–47 (notes): recommendations on open questions 1–7 | **All adopted by the user** (2026-10-11), as recorded in `machine-library-design.md` §12.8a §9. Q6 wires the five §12.8 modules into the `TuringMachine` facade now; the nine older files absent from it are `backlog.md` FAC-1. Q7 is also recorded in §13d's G2 row |
| 9–27, 29–31, 33, 34, 36, 37, 40 (notes) | Confirmed. No action |

**Gate FAILED at round 1.** Round 2 re-audits the repaired statements, the
facade wiring, and the corrections above.

## Round 2 (2026-10-11): 0 blockers, 0 majors, 2 minors, 36 notes

The findings are verbatim in `audits/s12-8-statements-r2-findings.md`; the
pack is `audits/s12-8-statements-r2-pack.md`. This was a full re-audit. The
auditor:

- found the four strengthened contracts true (notes 3–6);
- confirmed that the head-radius clauses give `O(size + 1)` work space per
  call and compose at restored entry heads (note 7);
- re-confirmed every unchanged statement and definition (notes 10–32);
- verified the round-1 dispositions (note 9);
- confirmed the freeze by reconstruction (note 33);
- found the facade wiring and the recorded decisions accurate (notes 34–35);
- reproduced the screen byte for byte (note 38).

| Finding | Disposition |
|---|---|
| 1 (minor): the adequacy probe's record-step example concludes only `∃ t, spaceUsed ≤ …`, which `t = 0` satisfies without a verdict | **Fixed** in the evidence probe. The example now concludes `∃ t ≤ C·(L + \|x\| + 1)`, a verdict `yes` or `no` at `t`, and the space bound. It still elaborates cleanly (`audits/logs/s12-8-statements-r2-close.log`). The repaired contract itself was never affected |
| 2 (minor): `Scan.lean`'s overview says both input sweeps move the work heads in lockstep | **Swept** (comment-only). Only `inputCopyTM` moves its destination head in lockstep; `inputFoldTM` moves only the input head. The code is identical with comments stripped, and the file elaborates at 0 errors with its 4 sorries |
| 3 (note): keep the saved-position, clamping, cleanup and trajectory obligations in the step row's fill | **Carried** into the §12.8 fill brief |
| 7 (note): consumers must intercept the verdicts; the bounds say nothing after the verdict time | **Carried** into the §12.8 fill brief and S1b's statement phase |
| 8 (note): the input call is time-only, so a space-preserving call needs its own interface | **Recorded.** No current consumer needs one; it would be a new row with its own gate |
| 31, 32 (notes): mixed rich tapes need R1 isolation of the dedicated digit tapes; keep O6 | **Carried** into the fill brief, as for round-1 note 32 |
| 36 (note): the topic manifest, the full import graph and the consumer sources were not attached | **Pack practice:** attach the import graph or a topic manifest when a pack claims closure completeness |
| 4–6, 9–30, 33–35, 37, 38 (notes) | Confirmed. No action |

**Gate CLOSED. PR #28 is clear to merge.** It merges the transport of PR #16
with it.
