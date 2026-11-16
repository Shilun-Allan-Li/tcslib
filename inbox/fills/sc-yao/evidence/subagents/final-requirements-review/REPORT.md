# Final requirements review

This is an independent read-only audit of the lead's source and saved evidence. No Lean,
compilation, package/cache command, proof edit or commit was performed. Report files were
written only in the existing sc-yao-c worktree; the lead's worktree was read-only.
`AUDIT.json` contains the exact hashes and per-case records.

## Result

No additional proof, reader, export or host-contract gap was found. The lead's known final
checks and delivery work still need authoritative completion evidence; this review is not
an assertion that the entire goal is complete.

Two literal report/packaging requirements were identified and communicated to the lead:

1. The brief asks for the header script under `evidence/headers/` and the name-clash script
   under `evidence/clash/`. They originally existed only under `evidence/tools/`. The lead
   has installed exact copies at the requested locations (and the explicit-definition
   scan under `evidence/unfold/`). I independently verified all three copies are SHA256
   equal to their canonical tools. This gap is resolved.
2. The scope-request rule asks for each question and answer verbatim both in its evidence
   record and in `REPORT.md`'s scope section. The CP4 report only referenced the four records.
   The final report must include the actual blocks. The lead has agreed; the optional
   `scope-request-verbatim.md` fragment preserves the recorded questions and answers.

The final report should also retain the fuller efficiency hypothesis/reader mapping from
CP2, rather than the shortened CP4 paragraph. Its simulator premise map and Gate27 map
already have concrete declaration/reader detail in the a13 and b-final fragments. This is
report completion, not an additional source proof obligation.

## Independently verified evidence

| Requirement | Authoritative evidence and verification |
|---|---|
| Issued packages | Rehashed every entry of both `/private/tmp/sc-yao-issued/outbox/fills/{sc-yao,codex-host-2026-11-15}/SHA256SUMS`; every file matches. Historical raw verification outputs remain `evidence/logs/pack-sc-yao.log` and `pack-host.log`. |
| SY3 necessity controls | All24 rows in `evidence/probe-runs/checkpoint1-frozen-readers/results.jsonl` tagged with a reader:8 unsealed direct passes,8 sealed negatives each exactly1error,8 sealed reader passes. Independently hashed both current probe and retained source snapshot against each row; independently recounted both `error:` and `error(...)` forms in every raw log. All match. |
| Base whole-file seals | All12 requests in `evidence/seals/frozen/base/manifest.json` have exact immutable record/source/log under `checkpoint1-frozen-readers/immutable-rows`. Source and raw-log hashes match each record. Removing the declared instrumentation lines restores the exact issue-base bytes via `git show 6ce4658d:<file>`. Independent raw error recount agrees: DAG0 in4variants; Uniform4 ineach4variants; YaoA0, YaoB15. |
| Base target and consumer axioms | `evidence/probes/BaseAxioms.lean`, its exact retained source, `evidence/logs/base-axioms/results.jsonl` and raw log print all4target/consumer axiom sets and transitive admitted roots. Runner row is exit0/errors0/generic0 and source SHA matches. |
| Frozen source/header boundary | `evidence/headers/final-exact/results.json` has0unexpected differences, same76Yao declarations including4private; exact restoration after masking approved spans/insertions. Controls record exactly1header change and1region violation. Current71-source inventory hashes match the source bytes. |
| Export reachability | Root `TCSlib.lean:69` imports SecureComputation; its facade imports Yao; Yao imports exactly the HybridProof hub after the existing imports. Hub imports exactly all67children once. All helper direct TCSlib imports lie in the193approved-module order or helper set, without the forbidden in-flight imports. |
| Declaration signatures | CP4 payload has764new explicit source headers in `evidence/interfaces/source-signatures.md`; source headers intentionally retain section context. `AllAxioms.lean` enumerates every stored constant by defining module, including private/generated constants, and prints full elaborated types. The final rerun and final payload export are still lead-owned pending work. |
| Scope approvals | The four `evidence/scope-request/*.md` records contain the exact approved imports, questions, verbatim answers and rationale. No additional frozen scope is inferred by this audit. |
| Generic decoder host | `DescriptionDecoder.decodeDescription_host` at source224 existentially fixes one `M,A,c`; that same `M` satisfies Clean correctness/time and the forall-time work-head envelope. It also states canonical correctness for every circuit/output word. Public, generic, built from H14 clean_install/envelope. |
| Generic evaluation host | `RunWithHost.exists_machine` at source174 is generic in encoded gates, value family, leaf algorithm and polynomial bounds. One `M,A,d` satisfies Clean for the actual encoded runWith function and the all-time work-head envelope. Public; no private host copy. |
| Host draft registry rows | `evidence/reports/common-contract-disclosures.md` has4-column rows for decoder and evaluator with host, status/provenance and named consumers, matching `machine-library-design.md`§14's4-column format. Promotion/registry review is explicitly requested; no frozen registry edit. |
| Overlap and reuse | Common disclosures include the exact SY5 assignmentFold relative, whole-coordinate versus sc-garble marginal comparison, OTAnswerWords/sc-compose lengths, decoder/CookLevin finite pairing, GI strategy/history relatives, source/public probability/list reuse and technical extraction provenance. b5/v6/v7 and c fragments add nearest paths/names and searches. This review checked coverage of the issued comparison families, not a fresh theorem-equivalence search over all764declarations. |
| Final static evidence | Latest final lint has92FAIL/102WARN with only approved Yao size added; circuit counts0/79 with reader text improvements. Name scan reports764names/0unexpected clashes across all4required pins. Explicit-definition scan now includes both target bodies:8970files,2023references,17candidates; final resolution must say final (old resolution still had CP4 label when audited). |

## Base consumer closure to preserve in final report

The baseline raw log is `evidence/logs/base-axioms/evidence__probes__BaseAxioms.log`.
It reports:

* `yaoHybrid_polyTime`: itself only.
* `yaoHybrid_simulators`: itself only.
* `yaoHybrid_hbcSecure`: the two target admissions.
* `yaoProtocol_hbcSecure`: the two Yao targets, `otProtocol_polyTime`,
  `otProtocol_simulators`, and `HybridProtocol.hbcSecure_compose`.

The final trace must replace the two Yao target admissions with exactly frozen
`yaoSeed_good_whp` and `sliceMultiMessageSecure_of_prfOut`, with no helper admission.
The final real-protocol consumer is expected additionally to retain the two OT admissions
and the composition admission, attributed to those other units. These expectations are not
substitutes for reading the final trace.

## Root-owned completion items

At task assignment the remaining items were3Uniform variants after the pause, final
per-error B attribution,272roothelperseals, final261-module sweep and32→30admission diff,
final all-stored trace, final explicit-definition resolution, final report and seventh
proof commit, complete unsigned patch/hash reproduction, exact manifests, scoped rebased
non-force final push and sc-yao-rooted ZIP. The lead subsequently reported the3Uniform
variants complete with the same4baseline errors each, and the full sweep active. This
review deliberately does not certify those changing live jobs or future artifacts.

Before final freeze, copy all new read-only review reports into root evidence, refresh the
sc-yao-tagged shared-slot log, preserve raw interrupted versions and zip-part entry hashes,
and check that all source hashes correspond to the final committed tip. The final REPORT
must replace CP4 statuses/counts and prototype-only qualifications with actual final-source
results while preserving the historical prototype failures/repair evidence.
