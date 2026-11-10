# Exact-target landing verification for draft #250

Gate 15 passed the seven efficiency proofs and two asymptotic SIS
collision-resistance proofs. The independent review reproduced all 144
campaign module logs and both probes. F01 corrects the axiom description
to the removal of `sorryAx` alone.
[Audit disposition](../../../../audits/lwe-sis-counted-loop-consumer-proofs-resolutions.md)

| Pin | Revision |
|---|---|
| Target `cryptography/lwe-sis-constructions` | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Checked Lean source and root | `8b3187bdaf0c634c086313a727a7210dca14bfeb` |
| Checked source records head | `ecbef871d2f7b878eb71b118b95fd24d5bbcde7c` |
| Exact-target preview tree | `9b0e3b5c6e6b373d17fc596df5173dc8201aa548` |

The preview preserves the Gate 15 library, root exports, H16 registry,
Lean toolchain and Lake pins. All 25 added Lean paths are reachable from
`TCSlib.lean`. The whole-library closure includes 1,089 modules
including that root. The 34 existing unexported Lean paths are outside
the root closure.

| Check | Result |
|---|---|
| Whole-library elaboration | All 1,089 modules produced fresh objects with zero errors in 4452.863 s of summed module time. |
| Admission diagnostics | Zero campaign-owned admissions. The whole library has 198 inherited admission warnings across 47 modules, including the 17 from the Gate 15 closure. Every affected file is byte-identical to the exact target. |
| Package bootstrap | Lean 4.25.0. Reused 2,513 reachable pinned package objects, restored 1,093 from local cache archives, and checked 31 PFR dependencies from the pinned source. |
| Dataset hygiene | Strict validation passed with zero hard failures. |
| Blueprint | Strict output matches the target byte for byte, including 857 inherited orphan labels. The check passes with those orphans allowed. |

The isolated object tree began without project objects. The first retry
supplied missing package companion files. The inherited
`Complexity/ClassP/BinaryArith/DetMod` timed out at 300 s and passed
with a longer limit in 735.923 s. All 45 modules
in its project closure are byte-identical to the exact target. While it
retried, the remaining independent modules ran serially in the same
object tree. The nine dependent modules finished afterward, ending with
`TCSlib.lean`.
The diagnostic log is preserved as a gzip archive. The landing receipt
records its decompressed SHA-256.
[Landing receipt](landing-checks.json) · [Module receipts](evidence/whole-library-checks.json) · [Checksums](evidence/SHA256SUMS)

The approved source integration covers 35 PW10 attributions and 49 Pei16
and Wu24 attributions. Three prior foundation attributions carry forward.
[PW10 approval](pw10-source-approval.json) · [Pei16 and Wu24 approval](pei16-wu24-source-approval.json)

The final publication check compares the live GitHub merge preview with
the verified library and source records on this draft. The user performs
the merge.
