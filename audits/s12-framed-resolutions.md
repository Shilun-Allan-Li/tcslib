# §12.6 framed catalog contracts — statement-gate resolutions (CLOSED, round 1)

**Gate: CLOSED on round 1 (2026-10-10): PASS, 0 blockers, 0 majors, 0 minors;
eight notes.** Findings verbatim in `audits/s12-framed-findings.md`. The five
statements in `Build/Catalog.lean` (`transferTM_run_ofCfg`, `copyTM_run_ofCfg`,
`clearTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`,
`incrementTM_run_overflow_ofCfg`) are audited true as stated and sufficient for
the zone consumer. This commissions the fill batch (`briefs/s12-framed-fill.md`).

## The auditor's evidence

- Blind restatements of all five.
- Trace inductions on the transition tables, with an every-time trajectory
  table.
- 15 adversarial instantiations plus 1,524 configurations in an independent
  semantic model; all 63 of the maintainer's fixtures were reproduced.
- Mutation tests showing each delimiter premise is needed where it is claimed.
- The canonical-specialization table.
- A consumer-fitness analysis, including the counter's geometric cost:
  `Σ_{r=1}^{2^i}(2v₂(r)+2) = 2^{i+2} − 2`.

## Notes carried into the fill brief (binding guidance)

| Note | Carried as |
|---|---|
| F1–F5: no findings; prove the generalized trace once, in Catalog | The fill's central rule: one generalized trace per routine family; no parallel private traces |
| F6: hypotheses are sufficient, not minimal (the right delimiter is unread on success; clear tests only nonblankness) | Statements frozen as audited; no strengthening edits |
| F7: consumer obligations (uniform control, window location, boundary save/restore, left-side orientation, identity branch, unary-scratch restoration, first-return transport, explicit halt) | Carried to the ZF-A3 brief, not this fill |
| Canonical specialization holds for all five; "the proof dependency order may need rearrangement because the framed rows currently appear later in the file" | The fill **re-derives each canonical row from its framed form**. Moving the framed section above the canonical rows is sanctioned, statements unchanged and the move flagged |
| F8: compilation and history attestations were not replayed by the auditor | Retained as maintainer evidence: Catalog elaborates with exactly the five sorries, and the downstream replay is clean |
| Suggested kernel sanity checks (the 15 concrete cases, width preservation, the `incFixed` characterizations) | Optional permanent regressions in the fill brief |

## Fill integrated (2026-10-10)

The fill batch (`briefs/s12-framed-fill.md`) delivered **5/5** at base
`0658eb8c`. It is integrated by `git am -3` as `0aea2108`, with Codex
authorship; the agent's report is `audits/s12-framed-agent-reports/fill-REPORT.md`.

- **Freeze:** an independent declaration-level check found 44 public
  declarations before and after, with no statement or docstring changed.
  Exactly the 14 sanctioned proof bodies changed: the five framed contracts,
  the five canonical run rows and the four space rows.
- **Private declarations:** 384 before and 384 after. One was removed
  (`catalog_erase_take`), one added (`catalogTape`), and the 14 R3 traces and
  helpers were generalized in place.
- **Replay** (`audits/logs/s12-framed-fill-integration-sweep.log`): `Catalog`
  has 0 errors and 0 sorries. `Zone` (2) and `Codes2Tape` (1) keep only their
  baseline admissions, and the `TuringMachine` facade is clean.
- **Axioms** (`audits/logs/s12-framed-fill-axioms.log`): all 44 public
  declarations printed; 37 within the standard three axioms, and 7
  definitions with none. No `sorryAx`.
- **Lint:** 0 FAIL, with 4 pre-existing size warnings.
- **Census** (`audits/logs/s12-framed-fill-census-after.log`): pass 4
  reproduced, with every file unchanged (Catalog 318/428, Primitives 173,
  Loop 98, Wrappers 19, Composition 6, TimeConstructible 20).

The canonical rows now derive from the framed contracts, as the gate asked.
This unblocks ZF-A3. The fill rides the next fill-gate audit.

## Fill gate CLOSED (round 1, 2026-10-10): 0 blockers, 0 majors, 2 minors, 5 notes

Findings verbatim in `audits/s12-framed-fill-findings.md`; the pack is
`audits/s12-framed-fill-{pack,bundle}.md`. **§12.6 is complete end to end:**
statements, statement gate, fill, fill gate.

The auditor blind-restated all 15 changed or added privates and confirmed one
generalized trace per routine, with no canonical-only trace left. The binding
route, the five canonical specializations, the four space rows, and the
freeze and reordering all hold; reverse/forward patch replay reproduces both
blob IDs.

| Finding | Disposition |
|---|---|
| F1 (minor): "zero new copied declarations or proof bodies" overstates the text-level result | **Resolved in the ledger.** The fill added no additional canonical trace and no new copy family, and the binding census is unchanged. The disclosed sibling repetition is debt under 12.2c item 5, whose scope now explicitly covers the generalized traces, the framed consequence proofs, the canonical specializations and the space wrappers (plan §4d; new ledger acknowledgment row). The agent's report stays verbatim. |
| F2 (minor): 23, not 21, changed persistent pairs | **Swept.** `copytext-diff.txt` was regenerated, comparing numerator and denominator; it reproduces the auditor's 23 and +1,415 exactly. The pack carries an erratum. |
| F3–F5 (notes) | No action. |
| F6 (note): the status-tag staleness is the only kind found | The doc-only refresh stays queued until RB5 lands, since `Embed.lean` is RB5's. |
| F7 (note): keep attestations distinct | Recorded: at the requested tip `9a492650`, `Build/Catalog.lean` is blob `8d8cb704798f02af6014f8f27fa05075930c5521`. |

The auditor also suggested a single-file factoring the fill could have made:
one private consequence lemma for the three sweep contracts. It is recorded
as the first step of 12.2c item 5. The ledger's Catalog denominator is
updated to 428.
