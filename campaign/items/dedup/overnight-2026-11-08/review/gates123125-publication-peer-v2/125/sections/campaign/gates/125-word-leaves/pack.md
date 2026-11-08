# Gate 125: Two private word-list closure leaves

**Prepared for Codex audit. Not yet clear to merge: #245 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/245; branch `codex/ab34-word-leaves`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `b8bb1f194b86c1b0c1d56e6c3f57e1defec37e80`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and issued prompt. Frozen private preparation wording remains historical
data; this pack and STATUS.md give the current remit.

## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `433d0ce6e17ed264f0d7f650a8692d4da4744b4f` Git blob; SHA256 `5edd51e6190c39240edf2ddabeeb841ff03b8d00b31a3288cfa02cff31a393d0` | `review/source/BASE/TCSlib/Complexity/CookLevin/Hardness.lean.txt` |
| HEAD owner | `fbefdf84f456f96fdef04753ecc253f92f0661da` Git blob; SHA256 `422042d604d9bee9fb5e8c12827cb1ae046eb48a3a448bc47f38418dd7017cbc` | `review/source/HEAD/TCSlib/Complexity/CookLevin/Hardness.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `review/qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 2 roots; public/private role explicit; both sides must execute | `review/metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same 33 source files at each side; no capped listing | `review/screen-population.txt`, all complete files in `review/source/BASE` and `review/source/HEAD` |
| style-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-style-lint.txt`, `review/qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-campaign-lint.txt`, `review/qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-sizes.json`, `review/qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `review/PAYLOAD-INDEX.json` and the focused exact `review/inputs/word-full-two-scopes/` |
| New screen pairs | Completed exact33-file HEAD screen: zero new, ten BASE-only directed identities | `review/screen/pair-delta.json`, `review/screen/pair-dispositions.json`, complete raw BASE/HEAD stdout |
| Publication | Exact source/records/bundle binding is in exchange README and issued prompt | `arora-barak-ch3-4/outbox/gates/125-word-leaves-gate/` |

## Audited change

The existing private clA5_pt_tail and clA5_pt_head consume the already imported public polynomial-time tail/take1 closures. Core reduction identifies List.tail with the required drop1 function. No explicit foreign definition is unfolded and no import, machine, theorem statement or public declaration changes.

The only changed source is `TCSlib/Complexity/CookLevin/Hardness.lean`. Every original header, definition,
name/privacy and import is preserved by the source freeze, within its documented
parser bound. Review the exact complete BASE/HEAD files and selected compiled
types as independent evidence. New definitions/statements/imports/public API: none.

Selected declaration set:

- `Complexity.clA5_pt_tail`
- `Complexity.clA5_pt_head`

These named target bodies are the complete authorized source scope. No RO1, FE, FH, SAT-import or Ladner proposal is included.

The original word replay queue stopped at precheck, before an output tree or
native Lean execution, after a records-only campaign advance. See `review/replay-history/`.
It is neither a Lean failure nor a PASS; only the matching v2 RESULT can bind HEAD.

Independent literal source binding: `review/literal-source-and-scope-binding.json`
checks every retained header and all outside-selected doc/header/body text,
imports and attributes byte for byte; each exact claimed-scope chunk matches
this PR HEAD. This complements declfreeze and the selected compiled ABI.

The two private docstrings also change from two-state-transduction descriptions
to descriptions of the public tail/prefix closures. Their formal headers remain
exact; include both private prose changes in the scope.

## Evidence and its limits

- Replay: Root-owned exact 26/26 replay PASS at b8bb1f194b86c1b0c1d56e6c3f57e1defec37e80; static exit 0; whole 895 input/output; source unchanged. Bound folder: /private/tmp/ab34-nword2-replay. This is not automatic validity after other source PRs merge.
- Selected compiled ABI/AX: Fresh BASE and exact replay-bound HEAD selected metadata executed for 2 roots. See `review/selected-ABI-comparison.json`; every raw/normalized type, universe, privacy/kind, simp and AX difference is explicit. No theorem proof-value equality is inferred.
- Rule-10 scope: Fifteen ordinary foreign guards; two complete literal scopes. Thirty positive and thirty expected-negative identities (30 pairs). This packet includes only the thirty word-leaf pairs from the older shared extras validation.
- Source/QA freeze: `review/qa/source-freeze.json`, exact complete BASE/HEAD owner and
  full 33-file source population under `review/source/`, plus declaration-freeze stdout.
- Lint/size comparison: style-lint.txt: BASE/HEAD delta; inspect both complete outputs; campaign-lint.txt: BASE/HEAD delta; inspect both complete outputs; sizes.json: BASE/HEAD delta; inspect both complete outputs. Existing BASE findings are not new HEAD findings;
  inspect both raw stdout files rather than treating nonzero historical output as
  a clean-tree certificate. No new lint execution is claimed by this helper.
- Default simp argument: imports and source attributes are unchanged; the executed
  BASE/HEAD selected root simp flags are exact. This is
  not a whole-environment simp-set or generated-auxiliary equality certificate.
- Screen: root-owned complete33-file BASE and exact HEAD screens both exit0.
  Directed pairs2107→2097; zero new, ten BASE-only, all ten explicitly
  dispositioned in `review/screen/pair-dispositions.json`. Filtered extraction2433→2431
  counts only bodies at least60 normalized characters, not source declarations.
  No screen was launched by this helper; no global absence/retirement inferred.

`review/PAYLOAD-INDEX.json` enumerates all exact copied frozen evidence inputs and hashes.
`review/replay/` contains the actual matching RESULT/request, all module logs, complete
object/source maps and every compiled replay module source as `.lean.txt`;
`compiled-source-index.json` gives the uncapped list, Git blobs and hashes.
These committed bytes independently match the actual replay input SHA map.
This extra context does not enlarge the named 33-file screen population.
Frozen source/native/seal/control reports are data, not authority to close a gate.
Some historical full-owner candidate checks included another proposed proof-only
family in the same file: only matching literal target scope evidence is used
here; actual PR-head replay supplies current full-owner validation. Preserve the relevant failed preparations and original raw logs.

## Canonical closures and exact source paths

| Selected private contract | Existing public closure | Canonical source |
|---|---|---|
| `Complexity.clA5_pt_tail : PolyTimeComputable List.tail` | `Complexity.polyTimeComputable_tail : PolyTimeComputable (fun w => w.drop 1)` | `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean:143` |
| `Complexity.clA5_pt_head : PolyTimeComputable (fun w => w.take 1)` | `Complexity.polyTimeComputable_take1` | `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean:295` |

The tail adapter proves the two list functions equal by cases on the list. It
unfolds no foreign TCSlib definition. Both public closures were already visible
through the existing imports. All33 complete source files are under `review/source/`
at both revisions. Unchanged SAT counterparts remain in that named context;
this PR does not change them or authorize their pending import proposal.

## Exact QA baseline comparison

Style findings are the same after the eighteen-line source shift and the
size8686→8668 update. Campaign lint changes only Hardness size8685→8667 in
one existing WARN and its INFO row; public5/private539 are unchanged. Full
raw outputs and uncapped diffs are in `review/qa/`; these inherited findings remain.

## Auditor checks

1. Verify the source pin, complete changed owner, exact authorized proof/prose scope and
   unchanged literal headers/imports/definitions. Restate the preserved selected
   contracts and explain why the published equations have the exact orientation,
   side conditions and instantiations required by each replacement.
2. Inspect every explicit simp/rw/unfold argument, including inline steps; a
   sealed definition can still be explicitly unfolded. Verify full claimed scope
   placement, ordinary guards, projection/abbreviation exclusions, default simp
   removals, and every positive/negative control identity. The scope is exactly the two complete private closure declarations;
   imported theorem proof values remain citation boundaries.
3. Check selected full types/universes/privacy/kind/simp/AX against BASE. Review
   any raw type or generated proof-auxiliary differences individually; no blanket
   raw ABI or proof-value equality is assumed. Confirm the exact replay HEAD and
   module count (26 expected), static result, source freeze and whole-tree
   provenance; do not compose snapshots or infer post-other-PR validity.
4. Compare complete BASE/HEAD lint and screen stdout on the identical named
   population. Disposition every new pair when supplied; candidate enumeration
   plus inspection is not exhaustive semantic absence. No global debt retirement
   follows from a short reader proof or a local screen.
5. Preserve the seven accepted SG1 structural kinds, FE-LIVE/FH1/BLIVE separation,
   the 54-name affected union (not 54 copies), bounded class-image residual and
   prior nine inherited Primitives AX closures. Do not convert inherited closure
   axioms into new direct admissions or imply permission for new imports/interfaces.
   Mathematical sorries and other family choices remain outside these edits.

The standards are supplied in full under `review/standards/`: `policy.md`,
`workflow.md`, audit `TEMPLATE.md`, maintainer controls and the duplication ledger. Report a new unapproved copy at
major; accounting inside the exact acknowledged kind remains minor. Neither a
local retirement nor this gate closes unrelated debt. Root owns final adoption,
gate status and current merged-tree replay.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`,
with blocker/major/minor/note per TEMPLATE. Give a verdict and counts; an empty
table needs the scoped reasoning supporting it. Identify any unresolved evidence
or source gap explicitly. Do not push, change source, dispatch another auditor or
declare merge clearance.

**Deliver your findings as a downloadable file named `gate125-word-leaves-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in
your reply.

## Independent provenance and current context

The actual26-module exact-head replay has0 failures and static0 mismatches/0
inherited admissions. Both895 input/output maps and the unchanged MAC8 input are supplied.
Independent public input anchors are the three files under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
The replay input895 hashes equal that adoption, not merely a self-reported count.
Actual static helper and diagnostic helper/context are in reproduction-tools/.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. Retire only the stated
proof implementations after external audit closure and Seyoon’s merge; no global absence,
all-owned-type equality or new debt exception follows.

Exact screen/lint/freeze/comparison helpers and toolchain/package context are in `reproduction-tools/`. The copied screen source matches the recorded execution SHA. Other context files are current reproduction inputs, not a newly invented historical byte attestation.
