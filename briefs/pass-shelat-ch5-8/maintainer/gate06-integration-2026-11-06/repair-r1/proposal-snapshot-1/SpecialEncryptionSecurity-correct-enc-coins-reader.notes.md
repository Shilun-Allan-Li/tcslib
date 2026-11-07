# SpecialEncryptionSecurity: second coin-length proof only

**UNAPPLIED; native elaboration and sealing pending.** Context comes from exact frozen commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16` via read-only `git show`. No Lean/cache, Git mutation, app or library edit was used.
Working-copy changes made independently by root are outside this proposal.

Valid V3 ordinal33 probe139 maps to pinned source89: the existing local `hr` proof in
`specialScheme.correct` ends in `rfl`, which reads the foreign constructor machine's coin
length. This patch changes only that one existing block to rewrite through public
`List.length_ofFn`, `NUPPT.coinLen_eq`, `NUPPT.coins_ofPolyTimeUniform` and `PolyExpr.eval_var`.
No definition is named in the rewrite list, and no new owner reader is needed.

The patch uses one unchanged forward context line (`have hp`) so it does not require the
adjacent old `hk` line. Static in-memory application verified the requested order:
first `SpecialEncryptionSecurity-correct-gen-coins-reader.patch`, then this `hr` patch.
The earlier `hk` patch retains the original `hr` as context, so apply the two in that order;
reverse-order context compatibility is not claimed. Both patches remain based on the
frozen file, with the new patch applying at the expected shifted location after `hk`.

The typed `hGE n rg re` issue at source91 remains for the next invocation; this repair does
not turn opaque coin function types into `Fin n → Bool` definitionally. The six downstream
`specialScheme G` application errors still need replay after the correctness proof has been
repaired. All headers, hypotheses, algorithms/security games and substantive admissions
remain byte-for-byte unchanged. No new `by` block, helper declaration or admission is added.

Static checks validated the manifest fingerprint/line map, unchanged bytes outside `hr`,
unchanged `by`/admission counts, the single-hunk counts, and chronological in-memory
composition with the `hk` proposal. No native success is claimed; root retains serial checking.

| Artifact | SHA-256 |
|---|---|
| Pinned source | `5e94e5d6139117ba39e5ad129dba737c91db52b9d80f16cc207499d300d03052` |
| `hr`-only proposed source | `d4c663ea6dcf42b2bd816769e7ae8586a7f832893f3d4a973ca53b605daa7bc6` |
| Combined `hk` + `hr` proposed source | `280b02cc2951226de9b7b9d872b2f039913b4f3b984e5ba5d1fca55c5aa8eea7` |
| New `hr` patch | `c2bb891d9ce89f485f17206ed48f82a0581c997cad56fa3eb083821f9bc9e859` |
| Earlier `hk` patch | `4d432c16a773f770b2027e97d66a7beef12d28f43b0c5cbca7a0bf4cf605044a` |
| Original valid-seal log | `8d66b2f5d9f584f1479ad78cc1b7ffa6a7e8f5adfbe336b1a18772f1fb74c3fe` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_033_TCSlib_Cryptography_SecureComputation_SpecialEncryptionSecurity_HarnessV3.log`.
