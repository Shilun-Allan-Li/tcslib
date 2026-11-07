# SpecialEncryptionSecurity: typed evaluator tapes, one existing proof block

**UNAPPLIED; native elaboration and sealing pending.** Proposal source is exact frozen commit
`e9d64158461bfe24ddc88ab885bc4017899b4c16`, obtained with read-only `git show`. No library edit, Lean/cache command,
Git mutation or app was used. Root's independent working-copy changes are not altered here.

Valid V3 ordinal33 probe141 maps to pinned source91, the existing local `hp` block in
`specialScheme.correct`. Its `hGE n rg re` application fails because `rg` and `re` have
constructor-machine coin types whose lengths remain opaque, while `hGE` requires arguments
of type `Fin n → Bool`. The prior `hk` and `hr` proposals establish the corresponding word
length equalities through public machine coin readers.

This third proposal changes **only that existing `hp` proof block**. It derives each tape's
index equality from `(List.length_ofFn (f := tape)).symm.trans hlen`, then rewrites its word
using public `List.ofFn_congr`. That theorem explicitly casts a function of type
`Fin m → Bool` to `fun i : Fin n => tape (Fin.cast h.symm i)` and proves equality of the
`List.ofFn` words. After both rewrites, `hGE` applies to actual `Fin n → Bool` arguments;
`List.length_ofFn` supplies the output length. No foreign body `rfl` or definitional coin
conversion is used. No new owner reader is required.

The casts preserve the two input words exactly. The generator/encryption algorithms, their
coins, the original evaluator specification `hGE`, public theorem headers, all security
games, premises and substantive admissions remain unchanged. The local `hrg` and `hre`
are proof terms, not helper definitions, and no new `by` block is introduced.

Static chronological composition succeeded in memory:

1. `SpecialEncryptionSecurity-correct-gen-coins-reader.patch`;
2. `SpecialEncryptionSecurity-correct-enc-coins-reader.patch`;
3. this typed-tape patch.

The new hunk uses one context line on each side, both outside the preceding `hk`/`hr`
changes. All three original correctness-proof diagnostics have proposed public-interface
repairs. The six downstream `specialScheme G` diagnostics were inferred to cascade from
failed construction elaboration; their outcome must await root's native replay. No passing
seal or disappearance of those diagnostics is claimed here.

Checks validated the pinned manifest fingerprint, source/probe map, exact public List lemma
signatures, single-hunk application, chronological composition and unchanged `by`/admission
counts. Only ignored proposal artifacts were written.

| Artifact | SHA-256 |
|---|---|
| Pinned source | `5e94e5d6139117ba39e5ad129dba737c91db52b9d80f16cc207499d300d03052` |
| Typed-tape-only proposed source | `107755a764dc1b3e733e9a5ed5fd6520637ca4ff3b3af918bbe6b4a4ef3d7a2e` |
| Earlier `hk` + `hr` proposed source | `280b02cc2951226de9b7b9d872b2f039913b4f3b984e5ba5d1fca55c5aa8eea7` |
| Combined three-repair source | `da9e654ece151cd62e6945612d7e29689c9056bd1d6b8f177d0d0c8b5f3824ed` |
| New typed-tape patch | `c6101eea03a6f5452120ed6b82c259abef1f819fa91812f50dc73aeef8e87626` |
| Earlier `hk` patch | `4d432c16a773f770b2027e97d66a7beef12d28f43b0c5cbca7a0bf4cf605044a` |
| Earlier `hr` patch | `c2bb891d9ce89f485f17206ed48f82a0581c997cad56fa3eb083821f9bc9e859` |
| Pinned Core `List/OfFn.lean` | `6cd7e9519ca430a49bf18c05943874ea338d361e0c390d7f7fb92658ada56785` |
| Mathlib `List/OfFn.lean` | `44af0461f05ce0e57d6906cbe82398aaab953d998e5ec2011e1a25a7ca5c8731` |
| Original valid-seal log | `8d66b2f5d9f584f1479ad78cc1b7ffa6a7e8f5adfbe336b1a18772f1fb74c3fe` |
| V3 manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_033_TCSlib_Cryptography_SecureComputation_SpecialEncryptionSecurity_HarnessV3.log`.
