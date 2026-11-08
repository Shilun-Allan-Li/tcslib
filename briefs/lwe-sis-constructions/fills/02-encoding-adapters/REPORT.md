# Encoding-adapter proof-fill report

All fourteen audited obligations are proved at
`b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`, against statement freeze
`6eec97be8f54d9990340900a5595dab32fb477f5`. The twenty source declarations,
three definitions, all signatures, complete equation proofs, attributes,
namespaces and imports are unchanged. All 100 other frozen paths match.

The proofs cover endian conversion, low-bit width normalization, exact lengths,
preservation, both round-trip formulations and all three polynomial-time routes.
They compose existing public machines and read foreign constructions through
published equations. The only sketch changes correct a lemma owner and describe
reuse of the reverse writer; the module overview now states proved results.
No handwritten helper, private host or copied proved infrastructure is added.

| Verification | Result |
|---|---|
| Fresh serial dependency sweep | 93 modules, 194.383 seconds, zero errors |
| Owned / inherited admission warnings | 0 / 17 |
| Fresh axiom probe | 29.042 seconds, zero errors |
| Owned constants | 284; all only standard axioms, no `sorryAx` |
| Earlier constants | 263 retain exact identity and axiom sets |
| Statement-era constant identities | All 283 preserve module, kind and visibility |
| New compiler constants | One arithmetic proof auxiliary, fully inventoried |
| Consumed machine contracts | Nine, all only standard axioms |
| Source freeze | Exactly fourteen changed theorem bodies; no surface drift |
| Scoped style | 0 FAIL / 2 unchanged WARN over 19 files |
| Development records | Nine runs with source snapshots; two failures retained |

The added compiler theorem is
`TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_length._proof_1_1`.
The length proof emits it with `propext` and `Quot.sound`; it is not a source API.
Development run 00 required explicit simplification of the true conditional;
run 07 required explicit reading of the encoded pair's projections. Neither
repair changed a statement. The final sweep is separate from development logs.

Checks use this chat's own pinned packages and a newly empty final object tree.
No cache fetch, package edit, whole-root build, shared API change, export edit,
other checkout edit, push or merge is performed by this proof fill. Global
process listing was unavailable; the resource receipt discloses that limit and
the user's extra coordination slots. Root ran serially; internal researchers
were read-only and ran no native/cache work. No PID was killed.

PR #238 remains the delivery path into `cryptography/lwe-sis-constructions`.
Its earlier single Encoding facade overlap remains in the separate statement
export commit; this fill changes only the owned module. Proof review is a new
job requiring a fresh Codex/Claude choice and user dispatch. The issued statement
pack/bundle remains unchanged. All five earlier findings reports are preserved.

Source validation/ingestion/approved matching and relevant landing checks remain
open. The source-validation handoff only prepares exact inputs; it selects or
dispatches no job. These adapters do not complete any primitive-security theorem.

**Not yet clear to merge — the proof gate, source-policy work, applicable landing
checks and user approval remain.**
