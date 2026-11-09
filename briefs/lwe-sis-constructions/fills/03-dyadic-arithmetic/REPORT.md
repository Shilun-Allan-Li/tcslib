# Dyadic scalar proof-fill report

All twelve audited obligations are filled at
`ec72ed773a690c17ac253707350935cc9e0acb34`, against statement freeze
`dbacd91218c19f0df106d316ce4ff0e22b869e66`. The eighteen source declarations,
definitions, signatures, complete equation readers, namespaces, attributes and
imports are unchanged. Exactly twelve theorem bodies change; all 101 other
frozen paths match. Only the module overview changes among comments; sketches
remain aligned without repair.

The proofs cover canonical writers, exact raw-input widths, residue-ring
readings and all three polynomial-time contracts. Subtraction explicitly reads
the modulus word, normalizes the right operand and proves the non-underflow
bound before casting natural subtraction. FP proofs compose the existing public
contracts and identify the complete functions through their owner equations.
No helper declaration, host or copied proved infrastructure is added.

| Verification | Result |
|---|---|
| Fresh serial dependency sweep | 94 modules, 251.162 seconds, zero errors |
| Owned / inherited admission warnings | 0 / 17 |
| Fresh axiom probe | 41.336 seconds, zero errors |
| Owned constants | 302; only standard axioms, no `sorryAx` |
| Earlier constants | 284 retain exact identity and axiom sets |
| Statement-era identities | All 302 preserve module, kind and visibility |
| New compiler auxiliaries | Zero |
| Backing public contracts | Sixteen, all only standard axioms |
| Source freeze | Twelve changed proof bodies, no surface drift |
| Scoped style | 0 FAIL / 2 unchanged WARN over twenty files |
| Development | Three passing runs with exact source snapshots |

Checks use the own pinned packages, a separate own development clone and a
newly empty final object tree. Statement-stage objects remain intact. No new
cache fetch, package/pin/export/shared API change, whole-root build, other
checkout edit, push or merge is performed by this fill. Resource/physical
provenance limits remain explicit. Root ran serially; two internal researchers
were read-only and ran no native/cache work. No PID was killed.

PR #239 remains the delivery path into `cryptography/lwe-sis-constructions`.
Its earlier Encoding facade overlap stays in the separate statement export
commit; the proof fill adds none. The issued statement pack/bundle/evidence and
all seven earlier findings reports remain unchanged. This new proof review
needs a fresh Codex/Claude selection and user dispatch.

Source validation/ingestion/approved matching, relevant landing checks and later
sampler/schedule/matrix/primitive bridges remain open. The twelve scalar
admissions are discharged locally; their separate external proof gate is open.

**Not yet clear to merge — proof review, source-policy work, applicable landing
checks and user approval remain.**
