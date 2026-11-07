# MIG-1 megafill brief review

Independent internal source/brief review by Codex; no Lean, cache, build, screen, Git mutation,
commit or push was run by this reviewer. Only this review file was written. This is not the
external fill gate and does not certify the future delivery.

Reviewed brief: `campaign/fills/mig1/briefs/megafill-mig1.md`, SHA-256
`af596548bd09c26c0b0379362cbf8da0b86b34fdd0fbc999729efff66ff1a1ea`. Pinned proof base: `83ac315ed9e7089466bd16a32f3b71fbadc556d2`.
The author incorporated the two editorial findings below during this review; both corrections
were reread in the reviewed version.

**Verdict: 0 blockers, 0 majors, 0 open minors; 2 resolved minors, 4 notes.** The scope and
contracts support the proposed integrated overnight job. Finish the pending issue receipts
before describing the packet as ready to dispatch.

## Findings and dispositions

| ID | Severity | Location | Finding and evidence | Disposition |
|---|---|---|---|---|
| M1 | minor, resolved | Delivery, checkpoint archive contents | The initial wording required both complete screens in every checkpoint, potentially delaying publication of early checked source until an expensive final screen/sweep. That weakened the recovery purpose of the checkpoints. | Fixed in the reviewed brief: early archives contain completed checks and explicit NOT RUN entries; the final complete delivery requires fresh complete screens and the full sweep. Validation-incomplete work remains a partial. |
| M2 | minor, resolved | F-B work package | The initial phrase “already proved” for existing strip/split/composite specs blurred supplied proof bodies with admission-free theorems. Gate 16 round 2 decision 2 explicitly makes strip depend on F-A and the split proofs depend on F-C plus the length counter. | Fixed: existing proof bodies are admission-free only after those dependencies are filled, with actual axiom verification required before claiming completion. |
| N1 | note, issue receipt | New forwarding exports and dispatch metadata | WORKFLOW §3 requires a fresh name/statement-shape search on open PRs, prepared landings and delivery refs before a new API pack. `open-pr-overlap.json` proves only file overlaps. The author confirmed that the separate candidate search/inspection receipt is being added. Final bundle/source/records pins and published-blob verification must likewise be recorded at issue. | Complete those evidence receipts before issue; no new design approval is needed for the three already-gated exports. |
| N2 | note, issue receipt | Pre-ship / baseline screen | The brief correctly distinguishes conditional route checks from proofs of the 17 existing targets and two future map theorems. During review the author was correcting a harmless unused-tactic warning and completing the 16-file baseline screen. `preship.json` must point to the final successful source/run hashes and the completed screen receipt. | Reconcile final hashes/exit counts and bundle all named inputs. Historical failed probes remain clearly labeled. No unrun seal, replay or source proof is certified by this review. |
| N3 | note, accepted | Ownership, public surface and temporary moves | The 11-file ownership is disjoint from the paused record-table rows, F6 and Ladner; WordSize is documentation-only. Exactly 17 existing specification admissions and exactly three future forwarding exports are identified. The six canonical public removals and their consumers match the final statement-gate plan. Temporary duplication of moved arguments until F-D is the already acknowledged scheduled migration in gate 16 note N8, with disclosure and one final home required. | Accepted. No additional interface/import/debt ruling is inferred. A missing cross-file API correctly yields an explicit gap/partial instead of a new private host. |
| N4 | note, accepted | Work order, helpers and current names | The F-A → F-C → F-B → F-D order matches design §9's allowed integrated execution. This is one fill with four packages, so the single cumulative branch is coherent with the explicit cover clarification. The approved Simulation BigOperators import and Catalog→Primitives edge are correctly limited. `callTM_run` supersedes the draft install/emit names; the primitive interval theorem and Simulation's existing space-from-time lemma are reused. | Accepted. Preserve the final coefficients and machine bodies; the contract file is historical statement data, so its old landing/provenance labels must not be copied into public Lean docstrings (the bundled policy already requires this). |

## Read-only cross-checks

- Read the maintainer entry/rules/current state, repository policy/workflow, environment addendum
  v2.6, MIG-1 design/inventory, final gate 16 pack/findings/resolutions, MIG-24 triage, the brief
  and current inputs/receipts. Historical measurements are treated as historical evidence.
- Compared all **11** owned-file input hashes and bytes with Git objects at the pinned base and
  the prepared source export; all match.
- Confirmed **17** target admission records, with the three unrelated RAM admissions excluded
  from that target set and frozen by the scope.
- Independently checked list cardinality, distinctness and dependency order for **51** bootstrap,
  **394** affected-downstream and **641** full-final modules, including the approved
  Catalog→Primitives import edge. The bootstrap and final lists contain their prerequisite
  TCSlib imports; the downstream list is correctly only the affected subset.
- Recomputed the exact union of direct Mathlib imports in the full final order plus the approved
  optional BigOperators import: **239 roots**, equal to the supplied root list.
- Checked the forwarding contract against the final gate's Primitives part: it contains exactly
  `Turing.FinTM.pairMapSndTM`, `_computes` and `_spaceUsed`, with forwarding mode true,
  coefficient 22, monotone time/space premises and coefficient one on the payload space. These
  are gated future additions, not exports claimed to exist in the proof base.

No source tactic correctness or future compilation claim is made. The eventual delivery still
needs the brief's complete freeze, source/compiled censuses, axiom walks, controls, screens and
current-campaign maintainer replay.
