# SpecialEncryptionSecurity: all observed roots and one generator-length repair

**UNAPPLIED; native elaboration and sealing pending.** All source and owner-reader context
was read with `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>` exactly. No library edit, Lean/cache command,
Git mutation or app was used. Root may independently change the working copy; these patches
and fingerprints remain pinned to the frozen base.

The completed survey summary's actual attempt path identifies **ordinal33**, not32:
ordinal32 is `SpecialEncryption`; ordinal33 is `SpecialEncryptionSecurity`.
The valid INSTALL and EOF markers verify all 1,636 names (1,617 active, 19 already
irreducible). The nine diagnostics map as follows.

| Probe line | Pinned source | Site | Cause and next route |
|---|---|---|---|
| 138 | 88 | `specialScheme.correct`, local `hk` | `rfl` reads opaque constructor-machine coin length. This invocation replaces this one existing proof block with public readers. |
| 139 | 89 | Same, local `hr` | Same issue for the encryptor; a separate proof-block repair can use the identical public coin-length route. |
| 141 | 91 | Same, local `hp` | `hGE n rg re` expects tapes of type `Fin n → Bool`, but `rg` and `re` retain their machines' opaque `Coins n` types. Length equalities alone do not make these types definitionally equal. A later repair must cast each tape along the public coin-length equality and transport `List.ofFn` via `List.ofFn_congr` before applying `hGE`. |
| 156 | 106 | `specialScheme_multiMessageSecure` header | `specialScheme G` is reported as expecting a list function rather than `G`; this is an application of the failed construction, not a new security-proof obligation established by this diagnostic. |
| 189 | 139 | `specialScheme_wrongKey` header, first scheme occurrence | Same application error. |
| 190 | 140 | Two scheme occurrences | Same application error, twice. |
| 191 | 141 | Scheme decryption-coin occurrence | Same application error. |
| 192 | 142 | Scheme decryption occurrence | Same application error. |

The last six diagnostics have the same failed `specialScheme G` head application. **Inference
from source and error recovery:** `G` and `hGE` occur only in the failed correctness field,
so recovery replacing that proof can drop those section parameters from the provisional
construction. Once all three correctness-field blockers are fixed, replay must confirm that
these six disappear. Do not rewrite the theorem headers or add wrappers/premises to satisfy
the recovered, invalid construction signature. Their security admissions remain untouched.

There is no bitwise scheme construction in this module. No missing bitwise field reader is
needed for these observed roots. The scheme already publishes generated non-simp `gen`,
`enc` and `dec` readers at its owner definition. The needed machine and evaluation readers
also already exist:

* `NUPPT.coinLen_eq` at pinned `Complexity/Randomized/PPT.lean:163`;
* `NUPPT.coins_ofPolyTimeUniform` at that owner line393;
* `PolyExpr.eval_var` at pinned `Complexity/Randomized/PolyExpr.lean:114`;
* `List.ofFn_congr` for the future same-word tape transport.

This first proposal changes **only the existing local `hk` proof block** at source88:
rewrite `List.length_ofFn`, `NUPPT.coinLen_eq`, `NUPPT.coins_ofPolyTimeUniform`, and
`PolyExpr.eval_var`. No foreign definition is named in the rewrite list, and no owner
addition is necessary. The sibling `hr` and `hp` blocks are deliberately preserved for
separate invocations, so this is a partial repair and does not claim to eliminate all nine
diagnostics. No new tactic block, helper definition, hypothesis or admission is added.
All headers, data algorithms, security games and existing substantive security admissions
are byte-for-byte preserved; all source outside the one local proof is unchanged.

Static validation checked the pinned source against the completed manifest, summary/log
binding, all nine line mappings, verified seal markers, one-hunk application in memory,
and unchanged public headers and `by`/admission counts. Root retains application and serial
native checking. Remaining native diagnostics are expected until the subsequent two
correctness-proof repairs are prepared/applied.

| Artifact | SHA-256 |
|---|---|
| Pinned source | `5e94e5d6139117ba39e5ad129dba737c91db52b9d80f16cc207499d300d03052` |
| Proposed source | `047a9a896d413244dd8d0ee7c2af2aaf7a511e234e710e6c8a2c30c0fb26e481` |
| Proposal patch | `4d432c16a773f770b2027e97d66a7beef12d28f43b0c5cbca7a0bf4cf605044a` |
| Pinned `PPT.lean` reader owner | `1766685ee73e2221d7cdecffe8a8cafedc43dc46af2d1b06da8c750973a453f4` |
| Pinned `PolyExpr.lean` reader owner | `69b3f23c2eddbaa479c1ea23c3cee9960cc30553bb846be1a4a9d408bae69903` |
| Actual attempt log | `8d66b2f5d9f584f1479ad78cc1b7ffa6a7e8f5adfbe336b1a18772f1fb74c3fe` |
| Survey summary | `672085e62d50fa3e4f710de667e2a135fee52fc5e9164556a4526a6dc4a7cbfd` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Actual log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_033_TCSlib_Cryptography_SecureComputation_SpecialEncryptionSecurity_HarnessV3.log`.
