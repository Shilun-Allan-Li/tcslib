# hash-sign — final

**Theorem proved and required verification complete.**
`TCSlib.Cryptography.Authentication.hashAndSign_oneTimeSecure` proves PS10
Theorem 144.1 with its frozen statement unchanged. Final checked coverage is
169 modules with zero errors; admissions change only from 22 to 21 by removing
the target. Its axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.
All twenty final A/B seals, both parent-facade baseline seals and all eleven
final control pairs pass. The complete raw evidence accompanies the source and
four-patch series; packaging verifies both manifests and the ZIP contents.

- Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
- Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
- Final source: `2e9d455a003c83d33b89149c83a6ab0610a63a4f`.
- Local-only branch: `fill/hash-sign`.
- Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## Proof and source changes

The proof follows the issued route. A common logged transcript fixes independent
signature-key, hash-index, adversary and signing tapes. The one-query sampling
law draws the possible signing tape before the run without changing its law.
T1 supplies the collision finder, which remembers the queried message and emits
it followed by the final message. Source freshness supplies distinctness;
`hdom` supplies domain membership. `exists_collisionGame_bound` bounds the
averaged equal-hash/fresh-message event by its actual CRH collision probability.

T2 supplies the original-scheme forger with `perCall = 1`, `finCall = 0`.
`exists_forwardGame` gives an exact original forgery-game/common-transcript
equality: acceptance and freshness of the final hash among forwarded queries.
The union bound and `Negligible.add` finish the theorem. The proof covers empty
logs, zero widths, malformed/noncanonical words and signatures, timeout outputs,
`m′ = m` and `hlen` casts. With no query the collision handler retains its zero
initial state; the forwarding forger covers that branch, so no collision success
is asserted for that default.

The main title/status and `## Contents` now describe a proved theorem. The sketch
records the shared transcript and tapes; its no-query description matches the
implementation. The final fourth patch makes two collision proofs use explicit
published padding/split readers and synchronizes that prose. It changes neither
the theorem statement nor any original declaration other than the target proof.

All paths below are relative to the repository. `HS/` denotes
`TCSlib/Cryptography/Authentication/Signatures/HashAndSign/`.

| Changed file | Lines | Purpose |
|---|---:|---|
| `TCSlib/Cryptography/Authentication.lean` | 60 | Eight specifically authorized helper imports. |
| `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean` | 639 | Source/common-game readers, case split and final proof. |
| `HS/CodecReaders.lean` | 104 | Codec extensionality and split/concatenation readers. |
| `HS/CollisionGame.lean` | 171 | Averaged collision-game bound. |
| `HS/CollisionHandler.lean` | 450 | T1 construction, tape coupling and collision soundness. |
| `HS/FixedGame.lean` | 168 | Common transcript, fixed/fresh signers and success event. |
| `HS/ForwardGame.lean` | 384 | T2 transcript/log/output coupling and exact game equality. |
| `HS/ForwardHandler.lean` | 337 | T2 construction and typed call/finalization/width readers. |
| `HS/OneQuery.lean` | 63 | Zero/one-query normal forms. |
| `HS/OneQuerySampling.lean` | 63 | Drawing one possible answer tape before the run. |

Every file is below 1,000 lines. The full inventory,
`evidence/logs/final-source-declarations.json`, records 110 explicit additions
(26 definitions, 84 theorems) and 15 generated `simps` readers: 125 source-level
names. Its explicit list agrees with the touched-declaration census. The six
new main-file theorems are `hsHashList_eq_hashWord`, `expect_hashAndSign_sign`,
`hashAndSign_accepts_iff`, `runAt_hsGen_split`, `hashAndSign_forge_eq_common` and
`hashAndSign_success_cases`. The existing target is a changed proof, not a new
name. The final collector separately covers all 176 stored constants, including
auxiliaries: 50 in the main file, 126 in helpers, zero in the parent facade.

## Scope and reuse disclosures

`evidence/logs/source-scope.json` confirms the unchanged target header and all
other original declarations. No new admission or global simp attribute is
introduced. `Lamport.lean` and `Games/Efficiency.lean` are untouched, and the
target proof does not depend on Lamport's parallel proof. No foreign reader
remains missing.

The sole expanded ownership is the exact eight-import parent-facade patch.
After reviewing it and the eight corresponding lint failures, the user answered
“Authorize the eight imports”; `evidence/inputs/session-overrides.md` records
this exception. It authorizes no other parent-facade change.

Promotion requests:

- `MachineCodec.ext_of_fields` → `Games/Machines.lean`.
- `SignatureScheme.forgerCodec_eq_bitCodec` → `Authentication/Signatures/Defs.lean`.
- `splitBits_append`, `splitBits_pad_concat` → `Authentication/Encoding.lean`.
- `eq_pure_of_cost_zero`, `one_query_cases` → `Games/OracleComp.lean`.
- `expect_simulate_sample_once` → `Games/Hopping.lean`.
- `origFixedSign`, `OriginalSuccess`, `forgeGame_eq_fixed` → a signature-game helper module.

Search records are `evidence/logs/generic-searches.log`, `one-query-search.log`,
`split-bits-search.log` and `evidence/rule10/codec-searches.json`. Public sampling,
coin/seed, codec and take/drop facts are imported rather than copied.

overlap: `TCSlib/Cryptography/Games/Forwarding.lean` `fwdRun` and
`polyTimeComputable_fwdRun`. The specialized hashing round follows the same
two-round pattern, rederived from published input/call readers. No private
lemma was copied.

overlap: `TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean`
`polyTimeComputable_hsHashList`. The reduction hash pads to `S.msgLen` instead
of `H.rangeLen`; its wrapper uses public evaluator/padding combinators. A helper
importing the main file would create a cycle. These variants are disclosed for
maintainer review.

## Environment and checks

The isolated checkout `/private/tmp/hash-sign-fill/repo` uses disk-backed APFS.
The preflight records macOS substitutes for unavailable Linux `nproc`, cgroups,
`/proc` and GNU `df`: 12 CPUs; physical memory 19,327,352,832 bytes; non-file use
11,676,270,592; headroom 7,651,082,240; disk free 271,874,621,440. Both floors pass.

The user overrode the original single-Lean rule: unlimited checks for twenty
minutes from about 05:42 UTC, then at most three concurrent Lean jobs. Later
coordination clarified the host-wide cap and reserved capacity for `dl-crh`
and Lamport. The launcher counts both bare `lean` and full executable paths and
was tightened to one worker slot while other projects were active. Unrelated
jobs were not interrupted. All hash-sign native checks had closed before the
final Lamport coordination note; subsequent work uses only file/Git operations. Checks remain one module per `scripts/lean_check_tree.sh`
invocation in this checkout's tree; Python runs as `python3 -I`.

All seven pack hashes and 150 pinned source hashes pass. The same narrowed 82
Mathlib roots suffice. Cache retrieval exits 0, unpacking 2,339 files without
failed downloads; no archives were downloaded because the tool's hash-checked
store already held them. Its pre-session 32,667 files total 1,595,387,830 bytes,
origin unknown. Present package pins all match; absent documentation packages
are recorded as absent. There are no empty oleans and the root-import probe
passes. No project `lake build` or unfiltered cache command was run.

The extended order contains the issued 150 modules, eleven existing T1/T2/bridge
prerequisites and eight helpers. The full sweep at `8e4234934` passed; after the
two reader repairs, ordered indices 164–168 passed again. All 164 prefix sources
are byte-identical, and every selected row's SHA matches the final source.
`evidence/logs/final-sweep-results.jsonl` and `sweep-summary.json` establish
169/169 exit-zero, error-free final coverage. This accurately records reused
prefix checks and fresh tail checks.

`admission-delta.json` reports only the target removed (22 → 21). The target's
printed axioms are the expected three. The latest
`evidence/rule10/final-r2/axioms-summary.json` audits all 176 constants: all new
constants use only those axioms; the unchanged
`exists_oneTimeSecure_of_crh_owf` alone retains `sorryAx` through Lamport as at
base. Style lint (`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography
--check8b`) reports 216 inherited FAIL at both base and final, zero new/removed
FAIL. Its exit 1 reflects inherited failures; the required comparison passes.

## Rule 10 results and provenance

Seals cover each owner's full TCSlib import closure. A excludes `PolyExpr.eval`
as notation; B seals it. Counts come from `evidence/rule10/final-r2/seal-A/manifest.json` and its B counterpart.

| Owner | A requests / result | B requests / result |
|---|---:|---:|
| `Authentication` | 2220 / pass | 2221 / pass |
| `HashAndSign` | 2112 / pass | 2113 / pass |
| `CodecReaders` | 789 / pass | 790 / pass |
| `CollisionGame` | 2058 / pass | 2059 / pass |
| `CollisionHandler` | 2050 / pass | 2051 / pass |
| `FixedGame` | 2045 / pass | 2046 / pass |
| `ForwardGame` | 2051 / pass | 2052 / pass |
| `ForwardHandler` | 2039 / pass | 2040 / pass |
| `OneQuery` | 617 / pass | 618 / pass |
| `OneQuerySampling` | 634 / pass | 635 / pass |

All twenty final A/B checks have zero failing declarations and complete native-guard
coverage; `evidence/rule10/final-r2/seal-matrix.json` records every check and source hash. Raw results,
request records and guard audits are retained under `evidence/rule10/` in
`final/`, `final-2250/` and `final-r2/`, with source hashes identifying byte-identical checks carried
forward.

The original main-file base seals pass A/B with 1,546/1,547 requests; seven
baseline paired controls pass. The added import-only parent facade has zero
stored constants. Its separately reconstructed baseline plans have 2,035/2,036
requests: both pass with complete native guards. This reconstruction uses exact base source/import
graph and preserved native metadata, but loads current compiled owned
dependencies. It is **not an authentic old Lean environment** and checks no
changed proof at base;
`evidence/rule10/base-facade-2250/catalog-reconstruction.json` records
that limitation.

The source-seal ledger records exactly three historical diagnostics, all with
passing resolutions on the latest bytes: `exists_forwardMachine` had a foreign
output-width elaboration dependency; `ofFn_collisionReply` and
`collisionHandler_collision` needed explicit published padding/split readers.
See `evidence/rule10/source-seal-failure-ledger.json` for original source hashes,
raw diagnostics, declarations and resolving guard audits. No failing declaration
is omitted or relabeled as an environment failure.

Earlier 1,000-request batches and the controlled 2,250-request workflow are both
retained. The switch changes batching only: request coverage, native-name
identity guards, instance masking and EOF verification are unchanged. A check
counts as a pass only with its complete installation/mask/EOF audit, not merely
an error-free proof log. Hash-addressed tool versions, pilot records, manifests,
requests and raw `results.jsonl` establish the executed workflow.

The completed explicit scan reviews 406 items: 361 public theorem uses (including
20 method/open aliases verified against native theorem names), six own-definition
uses and 39 local proof/let bindings; zero foreign-definition uses remain.
`evidence/rule10/final-r2/explicit-final.json`, its `explicit-review.json` and native probe logs
preserve this classification and the scanner's alias-resolution limitation.
All twenty-two final controls with minimal imports pass their expectations:
eleven unsealed probes pass; each of eleven sealed negatives fails exactly once
at its planned declaration; every published-reader positive passes. Independent
audits verify native identity, installation, instance masks and EOF for every
sealed control. See `evidence/rule10/final-r2/control-audit-summary.json`.

## Reproduction and delivery

The four complete format-patches are based on
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, in this order:
`6bb523434a3a49abf8410a73f6eccf1db6cddca1`,
`15f43fd73b9f466263312403896953ca0ece0017`,
`8e4234934690fe4e3e00e46965112998e1d09a31`,
`2e9d455a003c83d33b89149c83a6ab0610a63a4f`.
Applying them reproduces exact tree `20aa8ef6247e3f0f7e58a6c4e096873219c9017c`;
`evidence/logs/patch-reproduction.json` passes. `src/` follows full repository
paths and matches the committed files.

Checkpoint 1 was pushed at exchange commit
`07d53012fdbe748fe2cfa7ae3dc04d166396dba0`; checkpoint 2 at
`053edd270ba3b2bd082ca2edcffb25c3cc2b3857`, only under
`inbox/fills/hash-sign/`. Both followed pull-with-rebase; no force-push occurred.
The user's direct push authorization supersedes the older generic README's
Codex chat-only rule. The proof branch remains local; other delivery paths are
untouched. `evidence/logs/exchange-deliveries.json` records provenance.

`evidence/logs/final-verification.json` independently checks the twenty seal
cells and their raw-log/request hashes, all seventy-four indexed Rule-10 logs,
controls, baseline checks, axioms, explicit scan, scope, admission delta, lint
and patch reproduction. Every check passes.

The final packager includes every evidence file, including original/superseded
sources, requests, manifests, raw logs, `results.jsonl`, probes and all used tool
versions. The native stack diagnostic is retained losslessly compressed.
`evidence/SHA256SUMS` covers exactly the evidence files except itself;
`PAYLOAD-SHA256SUMS` covers all other payload files. The packager verifies both
path sets and hashes, exact committed `src/` bytes, ZIP integrity and its sole
`hash-sign/` root. The assigned-path mirror verifies byte equality with that
snapshot before the final commit and pull-with-rebase/push.

The final exchange revision and fallback ZIP checksum accompany the chat
delivery. Only `inbox/fills/hash-sign/` is written on the exchange. Campaign
landing remains a maintainer PR for Seyoon's approval.
