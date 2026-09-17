# Epoch 1 (fill round) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Fill campaign" (audit rounds at epoch
boundaries). External auditor: cross-vendor LLM per decision log.

## Round 1 (`epoch1-pack.md` → `epoch1-findings.md`, audited at `d3393b35`)

**Zero statement-level blockers or majors.** Every mathematical attestation was
independently reproduced by the auditor: the statement freeze (45 pre-existing
declaration headers unchanged across the eight modified modules; 85 new
declarations, all `private`; exactly the 12 sorry removals and 3 docstring-tail
rewrites), the full 22-module elaboration (with the auditor's own strengthened
exit-code and fresh-olean conditions), and all 13 `#print axioms` footprints —
plus an environment-traversal locating each assembly theorem's exact remaining
admitted dependencies (findings table, row 12). All four delivered machines
were certified against their audited schedules (`4n+5` pairing; `3(n+1)`
palindrome; the four-state counter's `c = 5` amortization; `condTM`'s
register/rewind/dispatch design, including the confirmation that the apparent
`false` parameter in its dispatcher does not select the branch).

One **major (tooling, pre-existing — not epoch-1 content)** and one **minor
(pack erratum)**:

| Finding | Resolution |
|---|---|
| 1 major — `scripts/lean_check_tree.sh` discards Lean's exit status and checks only for `error:` text, so a compiler crash without diagnostics passes; the documented sweep's `\|\| break` also hides failure in the overall status. (Auditor demonstrated with a stub `lean` exiting 23: old gate returned 0.) | Script rewritten in the closing commit: Lean's exit status is captured and propagated; the target `.olean` is deleted up front and required to exist afterward (no stale-output satisfaction); the documented sweep recipe now runs in a subshell with `\|\| exit 1`. The auditor's exploit was reproduced against the old script (exit 0) and re-run against the new one (fails on both the status and missing-olean conditions). The full 22-module sweep was then re-run under the strengthened gate: all modules pass, zero errors, the nine expected sorry warnings. Note: epoch-1's mathematical evidence was never in doubt — the integration sweep used a freshly wiped olean tree whose 22 emitted oleans (and the facades' imports of them) certify completion, and the auditor's independent guarded run reproduced it — but the gate itself is now sound for future rounds |
| 2 minor — the pack's scope prose says "six modified modules" while naming eight (eight is correct), and `phase4-findings.md` was cited as attached but absent from the bundle (the auditor fetched it from the repository) | Acknowledged; the shipped pack is preserved as the historical artifact (phase-3 precedent). Future packs: count files programmatically and verify every promised attachment is present in the assembled bundle |

Selected note dispositions (full table in the findings file):

- **Promotions endorsed** (finding 4, 5; audit question 1): both completed-run
  characterizations go to `Finite.lean` at the epoch-2 merge — batch A's as
  `Turing.FinTM.Computes.exists_computesInTime_iff` (arbitrary alphabet,
  totality hypothesis kept), batch B's as `Turing.FinTM.computesInTime_iff`
  **generalized from `Bool` to an arbitrary `Symbol`** before sharing; both are
  kept (different roles). Batch C's suite becomes a non-vendored
  `TuringMachine/StateRenaming.lean` at the raw-model layer, *reusing the
  existing public name `Turing.Action.mapState`* (currently in `Oracle.lean`)
  rather than a parallel one, with the run-correspondence lemma explicitly
  named as initialized-run (`relabelState_runFrom_init`-style); arbitrary
  functions suffice for action/configuration mapping, an equivalence is
  genuinely required for machine relabeling (the auditor's identification
  argument), and no finiteness assumptions are added.
- **Epoch-2 constraints recorded** (finding 11): B's `leftCfg`/`rightCfg`
  suite is sound *as stated* but is not yet a buffered-composition simulator —
  the embeddings pass emissions to the real output and preserve the native
  input, whereas `exists_comp_partial`/`computesFunInTime_comp` need a buffer
  representation, virtual-input clamping invariants, and (for `comp`) explicit
  time bounds. Additionally a **source-order obligation**: the helpers sit
  *after* the two remaining composition sorries in `Composition.lean`, and
  Lean has no forward references — shared infrastructure must move above its
  use or into an earlier imported module. Both constraints fold into the
  epoch-2 brief 2A and the planned `Simulation.lean`/`StateRenaming.lean`
  split of the ~950-line `Composition.lean` (policy §1 size threshold).
- **Provenance scope** (finding 13): the auditor verified the delivered
  snapshot independently (blob hashes, diff, elaboration, axioms); the
  original delivery archives' history remains a maintainer attestation. The
  original zips are retained locally by the maintainer; attach manifests if
  independent delivery-provenance verification is ever required.

## Gate status

**CLOSED** — the statement surface is clean (zero blockers/majors); the sole
major was a verification-tooling defect, fixed and re-verified in the closing
commit. Standing state: 12 of 21 sorries proved and audited; 9 remain, all
with sketches the auditor re-confirmed implementable (findings rows in the
"Remaining declaration" table). Carried obligations, tracked in the plan:

- Epoch-2 merge pre-work: the two `Finite.lean` promotions (with the auditor's
  names and the `Symbol` generalization), the `StateRenaming.lean` module
  unifying `Action.mapState`, and the `Composition.lean` split; re-run the
  freeze comparison after the refactor (finding 3).
- Epoch-2 brief 2A must demand the buffer/virtual-input invariants and time
  bounds beyond the epoch-1 gadgets (finding 11).
- Future packs ship exact attachment inventories (finding 2) and keep
  exit/output evidence with attestations (finding 1).
