# Gate 08 round 2 — external Codex findings

**Verdict: PASS. Open findings: 0 blockers, 0 majors, 0 minors.** The round-1 major and three minors are fixed; both notes have adequate dispositions. Gate 08 closes for the pinned revision below. No false statement, changed retained mathematical statement, or repair regression was found within this follow-up's scope.

This is a scoped audit of S1 and the rejection-loop **statement**. `polyTimeComputable_rejectBlocksL` still contains the authorized `sorry` assigned to the later external S2 fill. This verdict does not certify a completed proof of that host or dispatch S2.

## Audited revisions and integrity

| Item | Exact revision |
|---|---|
| PR | [#227](https://github.com/Shilun-Allan-Li/tcslib/pull/227) |
| Audited Lean head | `84f35910912bd3d1cd520beea9469e0ed45ce504` |
| Checked base | `bee51909a5c581bd61e954d6e1d86c708b4bc804` |
| Records snapshot | `11daf06237ab298fbe8dfdc27b382bd7bd741c08` |
| Exchange snapshot | `b4218c3d0194f083e7bc17a70419c48c8afbfafb` |
| Original S1 head | `c6affb3a92535d3f1de2e0a52c205a84c0cff551` |
| Original base | `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47` |

Read the exchange README, gate README, `pack-r2.md`, verbatim round-1 findings, resolutions, full root host registry, and round-2 report and underlying evidence. All three entries in `SHA256SUMS` pass. The bundle SHA-256 is:

`2e6b018933b65074cb41ca48d1986293b3b9cebffe5c766dfbaf8df4bed8b33e`

I independently reconstructed the complete bundle from all **153 revision-qualified manifest entries and their Git blobs**, including the format's newline normalization. It matches exactly. The archived round-1 findings also match their recorded SHA-256, `e6b5c1d9427897c3521092523775276c1c7806cd5e30f0e14bf52bba3d9e28a2`.

## Finding table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| — | — | Audited repair and records | No new or unresolved in-scope finding. | Independent comparisons and supplied Lean evidence are distinguished below. | None required for this gate. |

## Disposition of every round-1 issue

Paths below are repository-relative at the pinned revisions. Line numbers refer to the audited head, except the root registry, which refers to the records snapshot.

| Issue | Disposition | Evidence |
|---|---|---|
| **G08-01 — major** | **Fixed.** | The actual `machine-library-design.md` §14 registry contains H15 at line 3092. I checked the complete registry, rather than relying on `H15-registry-extract.md`. The row names the full public contract and `Candidates/Concrete.lean` home; statement-only, gate-pending status; external S2 proof assignment; dl-a, dl-c, rsa and rabin consumers; repetition-host/H14 dependency; polynomial-time output and payload-length guarantees; and absence of a separately exposed machine head envelope at this string-function layer. It explicitly says the proof is `sorry` and the registration does not dispatch the fill. The base and repaired Lean head carry the same registry entry. |
| **G08-02 — minor** | **Fixed.** | `Candidates/Concrete.lean:595` now promises a nonempty success word whose tail represents the value. The public theorem at line 633 still constrains only emptiness, the tail's value and its length. The original constant `[false]` counterexample remains consistent with the revised prose: with an always-true test, empty parameter/width/block/coin words and one trial, the sampled value is zero, the output is nonempty, and its empty tail has length zero. The sketch may choose `true :: trial word` for its witness without making that head bit an API guarantee. No theorem clause or proof code changed. |
| **G08-03 — minor** | **Fixed.** | `Candidates/Arithmetic.lean:195` now says “the last `W` bits.” The statement and proof of `natToList_zero_append_drop` at line 203 are unchanged. Dropping the original suffix length from a word of length `W + b.length` leaves exactly `W` bits, as its proof establishes. |
| **G08-04 — minor** | **Fixed.** | Inspected the repaired scanner and reproduced all seven lexical regression cases. Recounted every `TCSlib/` Lean source at all four pins: **506 → 507** at the original base/head and **510 → 511** at the checked base/repair head. Each comparison changes only `Candidates/Concrete.lean`, by one `sorry`. The baseline increase of four is entirely in `Games/Efficiency.lean`, introduced by #195. The old 507 → 508 figures are now identified as historical textual counts. These are lexical results, not elaboration results. |
| **G08-N1 — note** | **Recorded.** | The G6/G7/G10 public counterparts remain disclosed staged debt under Q2(A). The design's §5.4 and cleanup part 2 items A/N preserve the composition/congruence re-points, size-bound counterparts and restriction family. Item N explicitly requires retaining the old restriction statement's empty-codomain case when using the new theorem's `Nonempty O` interface. The follow-up pack qualifies its claim to **undisclosed** copies. No newly undisclosed counterpart was found in the repair. This does not certify that the deferred cleanup has been performed. |
| **G08-N2 — note** | **Fixed, with the separate tooling limit recorded.** | In the collector committed through #227, `cc.type.getUsedConstants` is outside the own-module condition; definition-value traversal remains restricted to the audited module. The saved expanded collector source agrees with this repair. Parsing the fresh collection output and comparing the old/new per-module lists yields 90 distinct names, no dropped pair, and exactly the DiscreteLog/`TCSlib.Cryptography.bitsToNat` and RSA/`TCSlib.Cryptography.Candidates.primeStr` additions. The stored-constant collector still does not independently cover every anonymous command; the import-closure supplement and controls address that gap for this pinned review. The general implementation debt remains open. |

## Repair merge and preserved statements

The raw commit objects confirm that the repair head follows merge `1fc275cdb658f4af75e5d7701d13de1c9510141a`, whose parents are the original S1 head and the checked base. The checked base's parent is the user's #195 merge, `922fc00cda9ecb3ac0ca8a54fbf2fbe8f50848f4`.

I independently compared all **1,070 library Lean files**, including the facade, with the base/S1 union. Every file is byte-identical to its expected source except the two documented docstring edits; those two files have identical comment-stripped code. The collector is a separate metaprogram change. Thus the repair introduces no additional mathematical proof or statement edit.

Reproducing the supplied source-header comparison against the checked base gives **25 ADDED, 2 REMOVED, 0 CHANGED**, with the same rows as the staged TSV. This is a source-header comparison; it does not independently establish equality of all elaborated ambient universe parameters. The original statement audit remains separate evidence. I found no reason to reopen its statement conclusions in this scoped follow-up.

## Evidence reproduced and evidence inspected

**Reproduced here:** checksums and all manifest/blob comparisons; merge/source preservation; lexical regressions and both census pairs; source-header delta; source import closures; candidate-list additions and reconciliation; control/probe source comparisons; diagnostic-to-declaration classifications; all 17 supplemental base/head code comparisons and hashes; and the historical inventory lookup.

**Lean execution was not repeated here.** This audit environment has no installed `lean`/`lake` toolchain. I inspected and reconciled the pinned maintainer logs, drivers, exact probe sources and summaries instead. I did not run `lake build`, fetch an unfiltered cache, or count a failed setup attempt as a proof check.

The supplied evidence supports the following qualified conclusions:

- **Replay:** all 437 source fingerprints match the audited head; the recorded order covers the TCSlib prerequisites before their users. All 437 module logs end with return code zero and contain no error or failure diagnostics. The checking script deletes the destination object before each check and requires a fresh nonempty object. Thus the logs support the reported 437/437 fresh-object replay; I did not inspect those native objects locally. The narrowed cache and pinned Mathlib records are consistent with the stated setup.
- **Aggregate axioms:** independently parsed and compared all **364 records** with the original S1 output, including multiplicities. They comprise 361 distinct names because three names are printed twice. The axiom sets are unchanged, including the same four `sorryAx` records. Separately, all **146 touched-declaration records** contain only the permitted standard axioms, with `sorryAx` additionally present only for the authorized host.
- **Expanded seals:** all 15 saved probes are exact audited source copies plus their seal insertion. Their logs reconcile to ten passing files and six untouched failing declarations across five files, with zero touched failures. All 14 control examples pass unsealed and fail at their proof sites when sealed. The original base controls remain historical evidence and were not freshly rerun in round 2.
- **Conservative supplement:** reconciled the collection output, all 15 candidate arrays, exact-name seal templates and final logs: **13,056 pairs = 12,966 active seals + 90 already irreducible pairs**. The final logs have no seal-command errors. They contain 20 proof diagnostics in the 17 declarations listed below, with zero touched failures. Both anonymous-only control pairs pass unsealed and fail sealed at the anonymous example; the broader pair uses the exact complete RSA seal.
- **Limits and excluded attempts:** the seals retain the documented exclusions for instances, reducible nonmatchers, `PolyExpr.eval` and `glNeed`; this is not an unrestricted audit of core/Mathlib unfolding. Earlier driver/attribute/name-resolution failures are excluded from successful evidence. The copied-tree hash inventory and three rebuild logs support the recorded probe setup, but are not locally regenerated object evidence. Style lint still exits 1 for the six approved fill-owned size findings; it is not a clean lint pass.

## Independent check of the 17 supplemental failures

For each final diagnostic, I located its enclosing declaration in the saved probe, verified it is outside the seal command and outside the touched list, removed the seal insertion to recover the audited source, and compared the declaration's code with the checked base. Comments and following namespace/section commands were excluded from the block comparison. All 17 code blocks and their hashes agree with the pinned preservation record.

| Module under `TCSlib/` | Untouched failing declaration | Base line → head line |
|---|---|---|
| `Complexity/Randomized/Build/IterateFind` | `polyTimeComputable_find` | 308 → 331 |
| `Complexity/Randomized/Closure` | `pairFstD_combineAdvice` | 184 → 202 |
| `Complexity/Randomized/Closure` | `pairSndD_combineAdvice` | 192 → 210 |
| `Cryptography/Asymptotic/PublicKeyLemmas` | `blockEncFun_flatten` | 196 → 197 |
| `Cryptography/Asymptotic/PublicKeyLemmas` | `distAdv_tuple_le_mul` | 576 → 577 |
| `Cryptography/Asymptotic/PublicKeyLemmas` | `exists_hybridBound` | 650 → 651 |
| `Cryptography/Asymptotic/PublicKeyLemmas` | `tdpPredictor_runAtL` | 764 → 765 |
| `Cryptography/Asymptotic/PublicKeyLemmas` | `uprob_tdpPredictor` | 803 → 804 |
| `Cryptography/Asymptotic/Sampling` | `pushesUniform_of_card_fiber` | 271 → 284 |
| `Cryptography/Candidates/Concrete` | `primesPairEquiv_apply_val` | 335 → 340 |
| `Cryptography/Candidates/DiscreteLog` | `ExpGroupGen.FullLength.exists_fullLengthExcept` | 440 → 440 |
| `Cryptography/Candidates/RSA` | `rsaTrapdoor_oneWay` | 2319 → 2221 |
| `Cryptography/Candidates/Rabin` | `rabinCollection_index` | 1408 → 1341 |
| `Cryptography/Candidates/Rabin` | `rabinBlumTrapdoor_index` | 3202 → 3067 |
| `Cryptography/HardcoreBit/Basic` | `uexp_mono` | 81 → 83 |
| `Cryptography/NumberTheory/Primality` | `bitsToNat_eq_listToNat` | 671 → 673 |
| `Cryptography/NumberTheory/Primality` | `exists_samplePrime_nuppt` | 899 → 921 |

This establishes **source preservation**, not reproduction of the broad base-seal behavior. I accept the classification as unchanged source debt for this gate, without claiming a fresh base kernel comparison. Fifteen rows match the historical 764-row inventory. The remaining two—`polyTimeComputable_find` and `exists_samplePrime_nuppt`—are explicitly recorded for reconciliation at the cleanup issue base. That disposition neither repairs those proofs nor dispatches cleanup. The narrower six-failure/base-control evidence is distinct from this broader supplement.

No GitHub push, campaign-branch change, host proof fill or S2 dispatch was performed.

**Clear to merge — Gate 08 closes for PR #227 at `84f35910912bd3d1cd520beea9469e0ed45ce504`, with the authorized S2 proof and recorded cleanup/tooling debt preserved.**
