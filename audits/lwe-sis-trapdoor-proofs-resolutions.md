# Gate 12 audit disposition

The audit is **HOLD on policy**, with zero blockers, one major, one minor,
and four continuing notes. All 40 fills pass the mathematical and axiom
checks. The auditor replayed both 144-module closures and reproduced the 308
axiom prints, 609-constant inventory, and all 220 elaborated type fingerprints.
The [verbatim findings](lwe-sis-trapdoor-proofs-findings.md) and
[intake record](../briefs/lwe-sis-constructions/fills/07-sis-trapdoor/intake-r1/intake.json)
preserve the audited pins and evidence.

| ID | Status | Disposition |
|---|---|---|
| F01 | Owner approval pending | `Lossy.error_sum_bound` duplicates `Regev.subsetError_bound`. The [proposed diff](../briefs/lwe-sis-constructions/fills/07-sis-trapdoor/intake-r1/proposed-binary-error-sum.patch) moves the existing Regev proof to `LWE.binaryErrorSum_bound` in `LWE.Basic` and uses it from both existing theorem signatures. This adds one theorem to a shared owner module. The isolated proposal passed the affected module checks and the axiom probe. The library source awaits approval and the repair awaits re-audit. |
| F02 | Repaired, pending re-audit | Commit `d3bb52db5aaf249a35e83506371a3c86e76cb69a` extends the PW10 references through pp. 37 and 39 respectively and points the concealer overview to the finite column hybrids in `Lossy.Experiments`. Both affected modules passed and the comment-stripped Lean source matches the audited source. |
| N01 | Open | The 18 owned admissions comprise nine counted-loop consumers, seven gadget and positional-reader obligations, and two anti-cyclic rank obligations. Carry the owner and host coordination forward. `Cyclotomic.Roots` is outside the current scoped cache. The 17 inherited admission warnings are tracked separately. |
| N02 | Open | The auditor independently verified the exact PW10 PDF and the seven consumed page hashes. Complete scoped ingestion and approved matching for the passages used. |
| N03 | Open | Efficient samplers and schedules, asymptotic and game bridges, other-branch inversion, strong one-time signatures, and CCA2 are separate obligations. SIS hardness remains an independent assumption. |
| N04 | Reader prerequisite merged | #255 is merged. The preview against central tip `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` preserves the #250 Lean tree, root, and pins. Repeat the exact-target and six export checks at landing. |

**Not yet clear to merge.** F01 requires owner approval and re-audit. The 18
owned admissions, scoped source review, and landing checks remain open.
