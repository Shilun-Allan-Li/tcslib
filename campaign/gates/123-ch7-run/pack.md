# Gate123 — reuse five public run laws

**Prepared for Codex audit. Not yet clear to merge: #243 — external audit open.**
Seyoon alone dispatches, rules on design/debt and merges. No audit is dispatched by this packet.

PR: https://github.com/Shilun-Allan-Li/tcslib/pull/243; branch `codex/ab34-ch7-run-reuse`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8. Audited HEAD `7c4b1a3e15b800cc4a98624f71a3b27458a41340`.
The exact records/exchange pins, bundle SHA256 and section count are supplied by the
published exchange README and the issued prompt. The source/evidence below is immutable
at that records pin. Frozen private drafts retain their earlier preparation wording as data;
this pack and STATUS.md give the current remit.

## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `3ac162843c4363e2c31082efa4b66408fd184ce8` Git blob; SHA256 `1a7d25619fb88b51d012e48fb66b758ce08c199e7d3aad219c25f18a7e741b4d` | `review/source/BASE/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| HEAD owner | `188fdc7b1776e0141bcbf29bc088d06628ec6539` Git blob; SHA256 `b9014e1a466ec3a57207f01decce39f75d41dec30f522cc0ca3c4ba53c3f3cbd` | `review/source/HEAD/TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `review/qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 5 roots; public/private role explicit; both successful sides executed | `review/metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same 33 source files at each side; no capped listing | `review/screen-population.txt`, all complete files in `review/source/BASE` and `review/source/HEAD` |
| style-lint.txt | Byte-identical BASE/HEAD outputs | `review/qa/BASE-style-lint.txt`, `review/qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-campaign-lint.txt`, `review/qa/HEAD-campaign-lint.txt` |
| sizes.json | Explicit BASE/HEAD delta; retain both full outputs | `review/qa/BASE-sizes.json`, `review/qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `review/PAYLOAD-INDEX.json` and uncapped copied `review/inputs/` |
| Copy screen | Actual33-file BASE2107→HEAD2105 directed pairs;0 new;2 BASE-only rows dispositioned | `review/screen/pair-delta.json`, `review/screen/pair-dispositions.json` |
| Publication | Source/records/bundle binding is in exchange README and issued prompt | `arora-barak-ch3-4/outbox/gates/123-ch7-run-gate/` |

## Audited change

The five unchanged public Bool-facing run-law statements now consume MultiTapeTM.step_output_prepend, runFrom_output_prepend, output_prefix, runFrom_of_halt and runFrom_state_ne_none_of_le. Review endpoint direction, the time-zero specialization and live-prefix inequality. Loop companion implementations were removed by an earlier merged cleanup; no claim is made about global run infrastructure or pending RO1.

The only changed source is `TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean`. Every original header, definition,
name/privacy and import is preserved by the source freeze, within its documented
parser bound. Review the exact complete BASE/HEAD files and selected compiled
types as independent evidence. New definitions/statements/imports/public API: none.

Selected declaration set:

- `Turing.step_output_prefix`
- `Turing.runFrom_output_prefix`
- `Turing.runFrom_output_extends`
- `Turing.runFrom_of_halted`
- `Turing.state_isSome_of_runFrom`

These named target bodies are the complete authorized source scope. No other family source proposal is included. The unchanged context sources and
ledger do not grant a new interface/import/home or debt ruling.

Independent literal source binding: `review/literal-source-and-scope-binding.json`
checks every retained header and all outside-selected doc/header/body text,
imports and attributes byte for byte; each exact claimed-scope chunk matches
this PR HEAD. This complements declfreeze and the selected compiled ABI.

The packet is complete for available source, replay, ABI/AX, full-five opacity,
controls, lint and screen evidence. Publication bindings are supplied by the exchange README and issued prompt.
No final records/exchange/bundle SHA or external dispatch is inferred.

## Evidence and its limits

- Replay: Root-owned exact 80/80 replay PASS at 7c4b1a3e15b800cc4a98624f71a3b27458a41340; static exit 0; whole 895 input/output; source unchanged. Bound folder: /private/tmp/ab34-nchr1-replay. This is not automatic validity after other source PRs merge.
- Selected compiled ABI/AX: Fresh BASE and exact replay-bound HEAD selected metadata executed for 5 roots. See `review/selected-ABI-comparison.json`; every raw/normalized type, universe, privacy/kind, simp and AX difference is explicit. No theorem proof-value equality is inferred.
- Rule-10 scope: Six ordinary foreign definitions; complete five literal doc/header/body scopes in the original import context. Action.apply default simp unfolding removed in both variants. Twelve fresh positive and twelve expected-negative identities (12 pairs). The unpinned first fixture is quarantined and is NOT evidence.
- Source/QA freeze: `review/qa/source-freeze.json`, exact complete BASE/HEAD owner and
  full 33-file source population under `review/source/`, plus declaration-freeze stdout.
- Lint/size comparison: style-lint.txt: BASE/HEAD bytes identical; campaign-lint.txt: the sole delta is the informational owner line count 326→295; all other stdout is exact. sizes.json confirms 326→295. See qa/lint-comparison.json. Existing BASE findings are not new HEAD findings;
  inspect both raw stdout files rather than treating nonzero historical output as
  a clean-tree certificate. No new lint execution is claimed by this helper.
- Default simp argument: imports and source attributes are unchanged; once both
  native runs exist, selected root simp flags are compared explicitly. This is
  not a whole-environment simp-set or generated-auxiliary equality certificate.
- Screen: the exact root-owned 33-file BASE/HEAD screens both completed with exit 0.
  Directed pair identities: 2,107 → 2,105, zero new, two BASE-only. Every new-pair
  row is dispositioned (the set is empty); see `review/screen/pair-delta.json` and
  `review/screen/pair-dispositions.json`. The tool extraction count 2,433 → 2,430 is not
  a Lean-interface count; source headers remain exact. No semantic absence or
  global debt retirement follows. No screen was launched by this helper.

`review/PAYLOAD-INDEX.json` enumerates all exact copied frozen evidence inputs and hashes.
`review/replay/` contains the actual matching RESULT/request, all module logs, complete
object/source maps and every compiled replay module source as `.lean.txt`;
`compiled-source-index.json` gives the uncapped list, Git blobs and hashes.
These committed bytes independently match the actual replay input SHA map.
This extra context does not enlarge the named 33-file screen population.
Frozen source/native/seal/control reports are data, not authority to close a gate.
The historical full-owner native receipt includes only these five replacement
proofs plus appended AX diagnostics; its proposed owner bytes equal this exact
HEAD. The pinned v2 seal contains all five complete literal doc/header/body chunks
that match HEAD. The unpinned first CH7 fixture is quarantined, not validation.
Preserve its raw files and the old shell preparation failure; neither is a PASS.

## Canonical public equations and source paths

| Preserved Bool-facing name | Existing generic equation | Canonical TCSlib source (HEAD equals BASE) |
|---|---|---|
| Turing.step_output_prefix | Turing.MultiTapeTM.step_output_prepend | TCSlib/Complexity/TuringMachine/Finite.lean:167 |
| Turing.runFrom_output_prefix | Turing.MultiTapeTM.runFrom_output_prepend | TCSlib/Complexity/TuringMachine/Finite.lean:189 |
| Turing.runFrom_output_extends | Turing.MultiTapeTM.output_prefix, specialized from time zero, plus runFrom_zero | TCSlib/Complexity/TuringMachine/Finite.lean:129 and TCSlib/Complexity/TuringMachine/Deterministic.lean:210 |
| Turing.runFrom_of_halted | Turing.MultiTapeTM.runFrom_of_halt | TCSlib/Complexity/TuringMachine/Deterministic.lean:262 |
| Turing.state_isSome_of_runFrom | Turing.MultiTapeTM.runFrom_state_ne_none_of_le | TCSlib/Complexity/TuringMachine/Finite.lean:201 |

The full files at both revisions are under `source/BASE/TCSlib/...lean.txt` and
`source/HEAD/TCSlib/...lean.txt`. All 33 screen-population files appear completely
at both sides. The separate full replay context is in `review/replay/compiled-source/`.
This preserves the five existing public names and headers as thin readers;
it introduces no new wrapper/API and does not settle another run-law/debt family.

## Auditor checks

1. Verify the source pin, complete changed owner, body-only authorization and
   unchanged literal headers/imports/definitions. Restate the preserved selected
   contracts and explain why the published equations have the exact orientation,
   side conditions and instantiations required by each replacement.
2. Inspect every explicit simp/rw/unfold argument, including inline steps; a
   sealed definition can still be explicitly unfolded. Verify full claimed scope
   placement, ordinary guards, projection/abbreviation exclusions, default simp
   removals, and every positive/negative control identity. The positive scope is these five complete declarations; imported theorem
   values are not traversed, and projection/abbreviation exclusions stay explicit.
3. Check selected full types/universes/privacy/kind/simp/AX against BASE. Review
   any raw type or generated proof-auxiliary differences individually; no blanket
   raw ABI or proof-value equality is assumed. Confirm the exact replay HEAD and
   module count (80 expected), static result, source freeze and whole-tree
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

The standards are supplied in full: policy.md, workflow.md, audit TEMPLATE,
maintainer controls and the duplication ledger. Report a new unapproved copy at
major; accounting inside the exact acknowledged kind remains minor. Neither a
local retirement nor this gate closes unrelated debt. Root owns final adoption,
gate status and current merged-tree replay.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`,
with blocker/major/minor/note per TEMPLATE. Give a verdict and counts; an empty
table needs the scoped reasoning supporting it. Identify any unresolved evidence
or source gap explicitly. Do not push, change source, dispatch another auditor or
declare merge clearance.

**Deliver your findings as a downloadable file named `gate123-ch7-run-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in
your reply.

## Current-campaign validity and scoped retirement

The campaign has no Lean change after MAC8/9b5; intervening commits are records only.
The actual80-module replay at the audited head has0 failures, static0 mismatches/31
inherited admissions,895 whole input/output objects, and unchanged original MAC8.
Every input hash equals the published MAC8 adoption. No snapshot is composed.
Later source merges require the standing current-tree check; no prospective unmerged
proof branch or unapproved RO1/SAT/Ladner proposal is assumed landed.

This retires the five CH7-D2 reproof implementations only after audit closure and Seyoon’s
merge; the existing Bool-facing statements remain compatibility forwards. The old Loop
companions were removed earlier. Structural embedding/host debt and other kinds retain
their recorded owner/window; this packet grants no new exception. Test t=0, halted starts,
nonempty output/prefix, zero tapes, and j=0/j=t at a live endpoint. Restate the arbitrary
configuration convention rather than silently specializing to initialized runs.

Independent input provenance is supplied in `campaign/status/2026-11-08-mig1-merge/receipt.json`, `object-hashes.json` and `Lean-tree.json` there. The895 recorded replay input hashes equal that published anchor. Actual static helper and diagnostic helper/context are in `reproduction-tools/`; the replay leanelab-o helper is self-contained. These sources are included for verification, without a new elaboration claim.

Exact screen/lint/freeze/comparison helpers and toolchain/package context are in `reproduction-tools/`. The copied screen source matches the recorded execution SHA. Other context files are current reproduction inputs, not a newly invented historical byte attestation.
