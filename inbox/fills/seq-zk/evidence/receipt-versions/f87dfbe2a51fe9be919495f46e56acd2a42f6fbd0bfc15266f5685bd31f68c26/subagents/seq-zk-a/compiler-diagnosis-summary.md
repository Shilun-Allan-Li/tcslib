# Closed own compiler-debugging ledger for checkpoint 2

This snapshot is complete through NormalizedStep attempt07. No own Lean process is active at
the snapshot boundary. Every listed interruption was separately authorized by the lead under
Seyoon’s best-judgment exception after verifying the exact own child chain. These were
diagnosed proof-elaboration investigations, never elapsed-time timeouts or E-RES reports.
No other process or slot was interrupted/edited/removed.

## StatisticalRecursion

Attempt01: own Lean3000 under wrapper2984, active CPU/Meta.isDefEq work, headroom6.113GiB.
The lead authorized SIGINT after exact source/sample/chain preservation; checker exit130,
783.64s, maxRSS3,811,213,312 bytes. A fully typed sampler/domain rewrite then passed attempt02
with 0 diagnostics in2.45s, maxRSS2,121,269,248 bytes. Source139lines, maxwidth94, SHA256
fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
The raw source, exact rewrite patch, authorization, process/resource records and sample are
all delivered. The native sample is losslessly packed in part001 with verified raw SHA.

## NormalizedStep closed attempts

All seven attempts below were interrupted by exact lead authorization and exited Lean130;
none is claimed checked. The mathematical/API read-only review found no known domain flaw.

| Attempt | Wall seconds | Max RSS bytes | Closed diagnosis | Authorization |
|---|---:|---:|---|---|
| 01 | 287.41 | 4226859008 | Sparse stack showed Simpa/whnf; assigning it to a particular hproduct line was tentative, not source-localized. | normalized-step-interruption-authorization.md |
| 02 | 334.22 | 4356784128 | Sparse stack showed Exact/isDefEq; no exact source line established. | normalized-step-interruption-02-authorization.md |
| 03 | 313.03 | 3860791296 | Ordinary trace markers absent in checker stdout; stage not localized. | normalized-step-interruption-03-authorization.md |
| 04 | 338.13 | 3989684224 | dbg_trace markers also absent in checker stdout; this was not evidence that proof had not begun. | normalized-step-interruption-04-authorization.md |
| 05 | 112.09 | 3356131328 | Direct-file IO markers proved module/signature/proof/fixed-point stages done; last marker test.begin brackets the hrawT declaration (type AND value). Earlier dot-reader-only attribution was overstated. | normalized-step-interruption-05-authorization.md |
| 06 | 735.60 | 5710823424 | Fully explicit statClose_iff reader still stopped within that declaration; type versus value remained unresolved. Authorized opaque-law fallback. | normalized-step-interruption-06-authorization.md |
| 07 | 342.75 | 5554405376 | Opaque generic helper independently passed; fixed and pointwise stages completed. Final explicit concrete generic-law instantiation remained pending. Authorized opacity/instance correction after lead cache. | normalized-step-interruption-07-authorization.md |

The live markers first isolate the whole hrawT declaration, not its annotated type versus
its value. Earlier guesses assigning that whole stage specifically to the dot-reader were
tentative and are explicitly corrected here. Attempt06’s explicit reader did not resolve it.
Attempt07 instead used seq-zk-c’s checked opaque generic law, but its concrete instantiation
still required further elaboration work. No target or helper statement has been weakened.

## Preservation and resource evidence

Eight own compiler-debugging interruptions are recorded here: StatisticalRecursion01 plus
NormalizedStep01–07. Other workers’ events are outside this sub-agent ledger; the lead has
their separate records. All own wrappers flushed checker output and released normally.
Resource readings stayed above the 4GiB floor; latest attempt07 headroom6.105GiB.

Native samples were created for StatisticalRecursion01 and NormalizedStep01–04; each is
delivered losslessly in numbered ZIP parts001–005, with raw SHA256, exact entry list and
verified decompression. Uncompressed originals are retained outside the payload under
/private/tmp/seq-zk-a-diagnostics/. Attempts05–07 were localized with direct-file markers;
no native samples were created for them, so none is omitted.

Exact marked source snapshots, each raw check log, preserved live marker logs, authorization
records, exact process-chain records, resource logs, and checker-stdout snapshots are included.
Checked prerequisite sources are retained in source-snapshots/ under their module paths.
StatisticalPostprocess belongs to seq-zk-c; its source hash/provenance and own dependency
check are included. No active check/marker is being copied at this snapshot boundary.

Future diagnostic changes and checks will use new attempt/file names. This closed ledger and
the files named by checkpoint2-closed-files.tsv are frozen until the lead confirms copying.
