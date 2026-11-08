# Gate 126: One local startup configuration reader

**Prepared for Codex audit. Not yet clear to merge: #246 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/246; branch `codex/ab34-restart-reader`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `48d715acefaa9eb1c6b1ffc8656fb79cc0ab1b10`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and issued prompt. Frozen private preparation wording remains historical
data; this pack and STATUS.md give the current remit.

## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `4c94bbe6651470bfd241f16f77c90d9171c5ecd3` Git blob; SHA256 `d3ceb7ca08b1e7adad821127e3dcefd3135599e8fb798d718cec4935ea751a3f` | `review/source/BASE/TCSlib/Complexity/TuringMachine/UniversalK.lean.txt` |
| HEAD owner | `f259e781e3abe3d7768c564f3614267ca891389c` Git blob; SHA256 `5f1f0757335087b8bfd08da9fc6b7445bccb6033024e36746a33d3d82b09b032` | `review/source/HEAD/TCSlib/Complexity/TuringMachine/UniversalK.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `review/qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 3 roots; public/private role explicit; both sides must execute | `review/metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same 33 source files at each side; no capped listing | `review/screen-population.txt`, all complete files in `review/source/BASE` and `review/source/HEAD` |
| style-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-style-lint.txt`, `review/qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-campaign-lint.txt`, `review/qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-sizes.json`, `review/qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `review/PAYLOAD-INDEX.json` and uncapped copied `review/inputs/` |
| New screen pairs | Completed exact33-file HEAD screen: zero new, one BASE-only directed identity | `review/screen/pair-delta.json`, `review/screen/pair-dispositions.json`, complete raw stdout |
| Publication | Exact source/records/bundle binding is in exchange README and issued prompt | `arora-barak-ch3-4/outbox/gates/126-restart-reader-gate/` |

## Audited change

Only local hinit inside Turing.exists_selfStartupTMK changes: MultiTapeTM.initCfg_eq_mapState A R Sum.inl rfl (pairEncode α w) replaces the five-field reconstruction. The initial machine A, local R update, d₀ alias and exact input are retained. Include the three selected public consumers exists_selfStartupTMK, exists_selfUniversalK and universalK.

The only changed source is `TCSlib/Complexity/TuringMachine/UniversalK.lean`. Every original header, definition,
name/privacy and import is preserved by the source freeze, within its documented
parser bound. Review the exact complete BASE/HEAD files and selected compiled
types as independent evidence. New definitions/statements/imports/public API: none.

Selected declaration set:

- `Turing.exists_selfStartupTMK`
- `Turing.exists_selfUniversalK`
- `Turing.universalK`

These three are selected public AX/ABI consumers of the one local hinit change;
no other body is authorized. No RO1, FE, FH, SAT-import or Ladner proposal is included.

Independent literal source binding: `review/literal-source-and-scope-binding.json`
checks every retained header and all outside-selected doc/header/body text,
imports and attributes byte for byte; each exact claimed-scope chunk matches
this PR HEAD. This complements declfreeze and the selected compiled ABI.

## Evidence and its limits

- Replay: Root-owned exact 18/18 replay PASS at 48d715acefaa9eb1c6b1ffc8656fb79cc0ab1b10; static exit 0; whole 895 input/output; source unchanged. Bound folder: /private/tmp/ab34-nrs2-replay. This is not automatic validity after other source PRs merge.
- Selected compiled ABI/AX: Fresh BASE and exact replay-bound HEAD selected metadata executed for 3 roots. See `review/selected-ABI-comparison.json`; every raw/normalized type, universe, privacy/kind, simp and AX difference is explicit. No theorem proof-value equality is inferred.
- Rule-10 scope: Three ordinary guards: MultiTapeTM.initCfg, Cfg.init and Cfg.mapState, with the first two simp definitions removed. The exact abstract hinit statement including local lets and its proof pass sealed; six positive and six expected-negative identities (6 pairs). This does NOT seal the entire legacy public theorem body.
- Source/QA freeze: `review/qa/source-freeze.json`, exact complete BASE/HEAD owner and
  full 33-file source population under `review/source/`, plus declaration-freeze stdout.
- Lint/size comparison: style-lint.txt: BASE/HEAD delta; inspect both complete outputs; campaign-lint.txt: BASE/HEAD delta; inspect both complete outputs; sizes.json: BASE/HEAD delta; inspect both complete outputs. Existing BASE findings are not new HEAD findings;
  inspect both raw stdout files rather than treating nonzero historical output as
  a clean-tree certificate. No new lint execution is claimed by this helper.
- Default simp argument: imports and source attributes are unchanged; the executed
  BASE/HEAD selected root simp flags are exact. This is
  not a whole-environment simp-set or generated-auxiliary equality certificate.
- Screen: root-owned complete33-file BASE and exact HEAD screens both exit0.
  Directed pairs2107→2106; zero new, one BASE-only, explicitly dispositioned.
  Filtered extraction2433→2433 counts only bodies at least60 normalized
  characters, not source declarations. Both full raw outputs are supplied; no
  helper screen or global absence/restart-debt retirement is claimed.

`review/PAYLOAD-INDEX.json` enumerates all exact copied frozen evidence inputs and hashes.
`review/replay/` contains the actual matching RESULT/request, all module logs, complete
object/source maps and every compiled replay module source as `.lean.txt`;
`compiled-source-index.json` gives the uncapped list, Git blobs and hashes.
These committed bytes independently match the actual replay input SHA map.
This extra context does not enlarge the named 33-file screen population.
Frozen source/native/seal/control reports are data, not authority to close a gate.
The historical full-owner proposed source equals this exact PR HEAD byte for
byte; its diagnostics are captured separately. The actual matching PR-head
replay supplies the final full-owner context. Preserve relevant failed
preparations and original raw logs.

## Canonical restart identity and exact source path

The reused equation is `Turing.MultiTapeTM.initCfg_eq_mapState` at
`TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean:79`. It takes machines
`A` and `R`, relabelling `Sum.inl`, the exact initial-state equality proved by
`rfl`, and input `pairEncode α w`. The retained local alias is `d₀ := A.initCfg
(pairEncode α w)`; no machine, time, space, coding or startup contract changes.
The full source appears at both sides under `review/source/BASE/TCSlib/...lean.txt`
and `review/source/HEAD/TCSlib/...lean.txt`.

The sealed consumer is the abstract local hinit statement with its exact local
lets and the same published equation. Its supplied import context and six
controls are explicit. It does not seal `exists_selfStartupTMK`'s entire legacy
body or the bodies of its two other selected public AX/ABI consumers.

## Exact QA baseline comparison

Style output changes only size2128→2115. Campaign lint changes only the
existing UniversalK size WARN/INFO from2127→2114; public12/private41 stay
exact. Full raw outputs and uncapped diffs are in `review/qa/`; inherited findings remain.

## Auditor checks

1. Verify the source pin, complete changed owner, exact authorized proof/prose scope and
   unchanged literal headers/imports/definitions. Restate the preserved selected
   contracts and explain why the published equations have the exact orientation,
   side conditions and instantiations required by each replacement.
2. Inspect every explicit simp/rw/unfold argument, including inline steps; a
   sealed definition can still be explicitly unfolded. Verify full claimed scope
   placement, ordinary guards, projection/abbreviation exclusions, default simp
   removals, and every positive/negative control identity. Respect the abstract local hinit boundary; it does not seal either
   complete public theorem or the legacy universal machine construction.
3. Check selected full types/universes/privacy/kind/simp/AX against BASE. Review
   any raw type or generated proof-auxiliary differences individually; no blanket
   raw ABI or proof-value equality is assumed. Confirm the exact replay HEAD and
   module count (18 expected), static result, source freeze and whole-tree
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

The standards are supplied in full at `review/standards/policy.md`,
`review/standards/workflow.md`, `review/standards/campaign/standards/TEMPLATE.md`,
`review/standards/campaign/maintainer/` and `review/standards/campaign/duplication-ledger.md`. Report a new unapproved copy at
major; accounting inside the exact acknowledged kind remains minor. Neither a
local retirement nor this gate closes unrelated debt. Root owns final adoption,
gate status and current merged-tree replay.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`,
with blocker/major/minor/note per TEMPLATE. Give a verdict and counts; an empty
table needs the scoped reasoning supporting it. Identify any unresolved evidence
or source gap explicitly. Do not push, change source, dispatch another auditor or
declare merge clearance.

**Deliver your findings as a downloadable file named `gate126-restart-reader-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in
your reply.

## Independent provenance and current context

The actual18-module exact-head replay has0 failures and static0 mismatches/0
inherited admissions. Both895 input/output maps and the unchanged MAC8 input are supplied.
Independent public input anchors are the three files under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
The replay input895 hashes equal that adoption, not merely a self-reported count.
Actual static helper and diagnostic helper/context are in reproduction-tools/.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. Retire only the stated
proof implementations after external audit closure and Seyoon’s merge; no global absence,
all-owned-type equality or new debt exception follows.
