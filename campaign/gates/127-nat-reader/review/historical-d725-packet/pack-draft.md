# Gate 127: One private Nat.bit equation reader — PRIVATE DRAFT

**PREPARING PUBLICATION BINDING. Not ready to dispatch. Not yet clear to merge: #247.**
Seyoon alone dispatches, rules on API/import/home/debt choices and merges. Root
must bind final records/exchange/bundle publication pins before dispatch.
The actual exact replay and completed screen evidence are supplied here. The user selected Codex for all morning
audits; no external dispatch has occurred here.

Source PR: https://github.com/Shilun-Allan-Li/tcslib/pull/247; branch `codex/ab34-canonoffset-bit-reader`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8. HEAD `d725e9fa76c81623e95c350250853bec511ddc3c`.
Records captured for this draft: `a65af49cbd8e720f267b6a16b6b4812d31be0904`.
Final records commit, exchange path/ref, bundle section count/SHA and actual
dispatch remain ROOT-TO-BIND; this private draft is not a published audit bundle.

## Exact source and evidence table

| Input | Binding | Evidence |
|---|---|---|
| BASE owner | `123a5538616a3456ac3bcc2c7c4b67abdc3f4eea` Git blob; SHA256 `57e7dc52dedf3d146499ad5694270d1c6fee7255cad74338d4174c5cce3e1a73` | `source/BASE/TCSlib/Complexity/TuringMachine/CodeSimulator.lean.txt` |
| HEAD owner | `cf207e1467eb90836f13c784fbffba8fd509bf67` Git blob; SHA256 `33c27b4177ce01aa941fec28b0e3bb095fc51a03d90359671c7ae801b6f8793c` | `source/HEAD/TCSlib/Complexity/TuringMachine/CodeSimulator.lean.txt` |
| Header/import/privacy freeze | Unchanged within the declfreeze parser scope; compiled selected ABI separate | `qa/source-freeze.json` and complete declfreeze stdout |
| Selected metadata | 1 roots; public/private role explicit; both sides must execute | `metadata/` full raw logs/requests and selected JSON |
| Full screen population | Same 33 source files at each side; no capped listing | `screen-population.txt`, all complete files in `source/BASE` and `source/HEAD` |
| style-lint.txt | Byte-identical BASE/HEAD outputs | `qa/BASE-style-lint.txt`, `qa/HEAD-style-lint.txt` |
| campaign-lint.txt | Byte-identical BASE/HEAD outputs | `qa/BASE-campaign-lint.txt`, `qa/HEAD-campaign-lint.txt` |
| sizes.json | Byte-identical BASE/HEAD outputs | `qa/BASE-sizes.json`, `qa/HEAD-sizes.json` |
| Frozen native/seal/control inputs | Literal source scope must match this HEAD; historical receipts keep their actual source pins | `PAYLOAD-INDEX.json` and uncapped copied `inputs/` |
| New screen pairs | Completed exact33-file HEAD screen: zero new, zero BASE-only directed identities | `screen/pair-delta.json`, `screen/pair-dispositions.json`, complete raw stdout |
| Publication | PREPARING; records/exchange/bundle binding and dispatch are root-owned | ROOT-TO-BIND |

## Audited change

Only the address-value line of Turing.MachineFormat.canonOffset_spec changes from simp [Nat.bit] to simp only [Nat.bit_val, Bool.toNat_true], retaining omega. Its binary-length clause already cites the shared length_bits_le_self; do not claim a new length-bound migration or delete the stronger combined private statement.

The only changed source is `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`. Every original header, definition,
name/privacy and import is preserved by the source freeze, within its documented
parser bound. Review the exact complete BASE/HEAD files and selected compiled
types as independent evidence. New definitions/statements/imports/public API: none.

Selected declaration set:

- `Turing.MachineFormat.canonOffset_spec`

These named target bodies are the complete authorized source scope. No RO1, FE, FH, SAT-import or Ladner proposal is included.

Independent literal source binding: `literal-source-and-scope-binding.json`
checks every retained header and all outside-selected doc/header/body text,
imports and attributes byte for byte; each exact claimed-scope chunk matches
this PR HEAD. This complements declfreeze and the selected compiled ABI.

## Evidence and its limits

- Replay: Root-owned exact 23/23 replay PASS at d725e9fa76c81623e95c350250853bec511ddc3c; static exit 0; whole 895 input/output; source unchanged. Bound folder: /private/tmp/ab34-nnat2-replay. This is not automatic validity after other source PRs merge.
- Selected compiled ABI/AX: Fresh BASE and exact replay-bound HEAD selected metadata executed for 1 roots. See selected-ABI-comparison.json; every raw/normalized type, universe, privacy/kind, simp and AX difference is explicit. No theorem proof-value equality is inferred.
- Rule-10 scope: Focused Nat.bit Mathlib-reader consumer guard; two positive and two expected-negative identities (2 pairs). This is not a whole-canonizer rule-10 certificate. Include the exact Mathlib equation source and binding evidence.
- Source/QA freeze: `qa/source-freeze.json`, exact complete BASE/HEAD owner and
  full 33-file source population under `source/`, plus declaration-freeze stdout.
- Lint/size comparison: style-lint.txt: BASE/HEAD bytes identical; campaign-lint.txt: BASE/HEAD bytes identical; sizes.json: BASE/HEAD bytes identical. Existing BASE findings are not new HEAD findings;
  inspect both raw stdout files rather than treating nonzero historical output as
  a clean-tree certificate. No new lint execution is claimed by this helper.
- Default simp argument: imports and source attributes are unchanged; the executed
  BASE/HEAD selected root simp flags are exact. This is
  not a whole-environment simp-set or generated-auxiliary equality certificate.
- Screen: root-owned complete33-file BASE and exact HEAD screens both exit0.
  Directed pairs2107→2107; zero new/zero BASE-only directed identities.
  Filtered extraction2433→2433 counts bodies at least60 normalized characters,
  not source declarations. Full raw output retains persistent ratios/order.
  No helper screen, global absence or legacy-canonizer retirement is claimed.

`PAYLOAD-INDEX.json` enumerates all exact copied frozen evidence inputs and hashes.
`replay/` contains the actual matching RESULT/request, all module logs, complete
object/source maps and every compiled replay module source as `.lean.txt`;
`compiled-source-index.json` gives the uncapped list, Git blobs and hashes.
These committed bytes independently match the actual replay input SHA map.
This extra context does not enlarge the named 33-file screen population.
Frozen source/native/seal/control reports are data, not authority to close a gate.
The historical full-owner proposed source equals this exact PR HEAD byte for
byte; its diagnostics are captured separately. The actual matching PR-head
replay supplies the final full-owner context. Preserve relevant failed
preparations and original raw logs.

## Canonical Mathlib equation and exact source path

The reused equation is `Nat.bit_val` at `Mathlib/Data/Nat/BinaryRec.lean:93`:
`Nat.bit b n = 2 * n + b.toNat`. The complete7295-byte source capture and exact
package/source binding are `inputs/nat-reader/Mathlib-BinaryRec.lean.txt` and
`inputs/nat-reader/Mathlib-source-binding.json`, pinned to mathlib commit
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. `Bool.toNat_true` supplies the final
Boolean value and `omega` handles arithmetic. No Mathlib/TCSlib source changes.

Only the first arithmetic branch's explicit unfolding of `Nat.bit` is replaced.
The private name is `Turing.MachineFormat.canonOffset_spec`; its whole formal
header is retained. The independent focused sealed equation consumer and two
paired controls test this Mathlib reader only. The rest of this legacy proof,
including its explicit own canonizer equations, is not claimed to be sealed.

## Exact QA baseline comparison

All three BASE/HEAD QA outputs are byte identical. The full raw stdout
and hashes remain in `qa/`; equality does not erase inherited findings.

## Auditor checks

1. Verify the source pin, complete changed owner, exact authorized proof/prose scope and
   unchanged literal headers/imports/definitions. Restate the preserved selected
   contracts and explain why the published equations have the exact orientation,
   side conditions and instantiations required by each replacement.
2. Inspect every explicit simp/rw/unfold argument, including inline steps; a
   sealed definition can still be explicitly unfolded. Verify full claimed scope
   placement, ordinary guards, projection/abbreviation exclusions, default simp
   removals, and every positive/negative control identity. Respect the focused Nat.bit consumer boundary; it does not seal the
   complete canonOffset_spec proof or the legacy canonizer.
3. Check selected full types/universes/privacy/kind/simp/AX against BASE. Review
   any raw type or generated proof-auxiliary differences individually; no blanket
   raw ABI or proof-value equality is assumed. Confirm the exact replay HEAD and
   module count (23 expected), static result, source freeze and whole-tree
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

The standards are supplied in full at `standards/policy.md`,
`standards/workflow.md`, `standards/campaign/standards/TEMPLATE.md`,
`standards/campaign/maintainer/` and `standards/campaign/duplication-ledger.md`. Report a new unapproved copy at
major; accounting inside the exact acknowledged kind remains minor. Neither a
local retirement nor this gate closes unrelated debt. Root owns final adoption,
gate status and current merged-tree replay.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`,
with blocker/major/minor/note per TEMPLATE. Give a verdict and counts; an empty
table needs the scoped reasoning supporting it. Identify any unresolved evidence
or source gap explicitly. Do not push, change source, dispatch another auditor or
declare merge clearance.

**Deliver your findings as a downloadable file named `gate127-nat-reader-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in
your reply.
