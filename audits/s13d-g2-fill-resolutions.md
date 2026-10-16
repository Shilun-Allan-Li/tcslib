# §13d G2 fill gate: resolutions (round 1; gate CLOSED)

**Gate:** the maintainer's G2 fill (PR #108, merged as `b6e0344c`): `copyMapTM_run_ofCfg`,
`transferMapTM_run_ofCfg` and `zoneCascadeRight_home` (`audits/s13d-g2-fill-pack.md`; bundle
SHA-256 `f6044d478f76b73df94e7a08016c9b7bb5e2f1dd0ee945d26dba0f4dd5edcfc7`, 60 sections, folder 27).

**Round 1** (`audits/s13d-g2-fill-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 3 minors.**
The auditor could not run Lean and treated the elaboration, axiom and replay logs as supplied
evidence. It independently re-applied the patch, regenerated both files, re-ran both freezes and
both six-file screens, and reconciled the logs. **The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `clearTM_run_ofCfg` keeps an inline specialization of the generic `catalog_trace_clauses`: residual debt inside the acknowledged §12.6 family (plan §4d item 5), not a new family | **Fixed in PR #109:** its no-earlier-exit and head clauses are `catalog_trace_clauses` at `touched := (· = i)` over `catalog_clear_trace`. The statement is byte-identical; the endpoint proof is unchanged. The clear row's residual in item 5 is discharged by that PR. |
| 2 | minor | `NOTES.md` §3's per-file in-file subtotals: the Catalog figures aggregated both Catalog files, and Zone's final figure was 40 too high | **Corrected** (erratum in `audits/evidence/s13d/g2-fill/NOTES.md`): `Build/Catalog.lean` 105,568 → 98,150, `Build/Contract/Catalog.lean` 240 → 240, `Build/Zone.lean` 3,840 → 2,844. These are directed overlap sums, not unique copied-source sizes. No approval or disposition changes. |
| 3 | minor | The two mapped rows' sketches kept pre-fill wording (`catalog_write_take`; "the mapped copy's trace"), and `NOTES.md` §1's "moves verbatim" overstated | **Fixed:** in PR #109, both sketches describe the shared trace `catalog_transferMap_trace`, its inline prefix update, and the copy as the transfer's identity-residue consequence. In the notes (erratum), the move is qualified: statements preserved, the `_plain` blocks byte-identical, the target proofs filled and ordered by dependency. |

## Rulings (adopted)

- **Brief item 4, the re-pointed regression:** acceptable. `zoneCascadeRight_zero_eq` still
  checks the definition (both folds reduce; then the two guards), and is not circular.
- **Brief item 5, the clear row's inline clauses:** residual debt within the acknowledged family,
  at minor. Fixed as finding 1.
- **The three new-by-name pairs** (user-approved on 2026-10-15): accounting and successor claims
  verified.

## Carried

None from this gate. G4's witnesses and G5's statement phase (with the G2–G4 statement gate's
minors 1 and 2) are unaffected.
