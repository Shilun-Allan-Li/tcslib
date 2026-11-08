# Gate 106: SG-1 deduplication, PR #215

Audit [PR #215](https://github.com/Shilun-Allan-Li/tcslib/pull/215),
`lean/dedup-sg1`, against the campaign. The immutable Lean and records commits are in the
bundle header; `evidence/current/landing/refs.json` pins the source comparison. This is a Codex
audit, selected by the user. The user dispatches the gate and merges the PR.

## Scope and purpose

The acknowledged SG-1 family is every private predicate restating `Turing.Segment` at fixed
parameters, together with its concatenation lemma. This PR removes all three known private
concatenation proofs and keeps their predicates, connected to the public API by private bridges.
The user approved importing `Build/Contract/Basic` in both Tautology and SingleTape (HANDOFF §0).

| Changed file under `TCSlib/Complexity/` | Change |
|---|---|
| `ClassNP/Tautology.lean` | `tautDualSegment_iff_segment`; delete `tautDual_segment_add`; use `Segment.trans`; use `Segment.zero` and `.one` in the two older private helpers |
| `TuringMachine/Build/CounterLoop.lean` | `counterSpan_iff_segment`; delete `counter_span_append`; three compositions use `Segment.trans`/`.mono`; four older public reads use `segment_iff` |
| `TuringMachine/Robustness/SingleTape.lean` | `dgSpan_iff_segment`; delete `dgSpan_add`; seven compositions use `Segment.trans`; older one-step and monotonicity helpers use `.one`/`.mono` |
| `SpaceComplexity/Machines/Frag.lean` | Pin the existing `halfL_run` buffer-cell step to `bufferTape_nat`; the same hunk appears in #222 |

Also changed: the Tautology blueprint removes the deleted private lemma's entry and updates its
uses. No public declaration is added or removed. All surviving statements and declaration order
are unchanged. Source counts are 287 → 287 across the four files: Tautology 5 public/88 private,
CounterLoop 59/20, SingleTape 4/96, Frag 15/0. Each deleted private is replaced by one private bridge.

The six public proof-body changes are `Turing.counterLoopTMVia_run_done`,
`Turing.counterLoopTMVia_done_witness`, `Turing.counterLoopTMVia_escape_witness`,
`Turing.RoundContract.counterLoopDone_traj`, `Turing.RoundContract.counterLoopEscape_traj`, and
`Complexity.LogProg.halfL_run`. Their statements remain frozen. The four witness/trajectory reads
were exposed by the maintainer's first seal and repaired mechanically in this PR.

## Brief for the auditor

Use the severity and debt rules in `campaign/standards/TEMPLATE.md`, `policy.md`, `workflow.md`
and the duplication ledger. Machine-checked tactic correctness is outside this gate; trusted
definitions/statements, semantic reuse, rule 10 and cumulative debt are in scope.

1. Restate the three private predicates without first reading their docstrings, then check the
   bridges against the published `Segment` equation. Tautology forbids the anchor strictly before
   the end and has a trivial head relation. CounterLoop has both exits forbidden strictly before
   the end and preserves the counter interval plus one shared body-head relation. SingleTape has
   an empty forbidden set and bounds its single work head through the endpoint.
2. Check preservation of cuts and endpoints, especially concatenation at time zero, an endpoint
   in the forbidden set, and a body relation requiring the same round/offset for every tape.
   Try at least three adversarial instantiations. A zero-length segment permits a forbidden
   start but still requires its head relation; a positive segment does not permit an earlier exit.
3. Check every changed composition and older zero/one/mono helper for a mechanical public-API
   re-point, rather than a new private composition implementation. Search inline steps and all
   closing forms as well as whole declarations.
4. Challenge the freeze, import changes, blueprint update, seals and screen classifications.
   The full consumer-file seals concern `Segment`; they do not claim to certify all older reads
   of unrelated foreign definitions. The separate Frag probe checks the exact pinned cell step.
5. Verify the ledger accounting cumulatively, including source-side members and the full nine-file
   screen population. The existing `SafeSegment` and cut-only candidates in Primitives, Catalog,
   SAT and Hardness are disclosed sibling candidates, not claimed retired by this PR. Report any
   candidate outside the approved family that needs a design or acknowledgment.

## Evidence and its limits

`evidence/current/README.md` gives the executed results and source pins. Raw evidence is retained:
`landing/` (diff and refs), `freeze/` (per-file comparisons and census), `lint/` (base/head exports),
`search/` (candidate enumeration across open PRs, prepared landings and delivery refs), `screen/`
(full populations, raw outputs, pair diff and classifications), `seal/` (whole-file probes, controls,
receipts and the initial failed attempt), `axioms/`, and `merged-tree/`.

The screen includes all four changed files and Contract/Basic, Primitives, Catalog, SAT and
CookLevin/Hardness. Its raw pair count is a candidate count, not a debt count. The ledger's standing
in-file convention counts exact copies and records near-matches without counting them. No new
debt acknowledgment is inferred by the maintainer. The replay is independently chained from the
complete Mac campaign snapshot; snapshots from other PRs are not composed.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Include a verdict line with blocker/major/minor/note counts. An empty findings table still needs
the predicate restatements and adversarial checks. The gate closes at zero blockers and zero
majors, with minors dispositioned; this pack does not authorize a merge.

**Deliver your findings as a downloadable file named `sg1-dedup-findings.md`** (the findings table
and the verdict line, no other wrapping), and also paste its content in your reply.
