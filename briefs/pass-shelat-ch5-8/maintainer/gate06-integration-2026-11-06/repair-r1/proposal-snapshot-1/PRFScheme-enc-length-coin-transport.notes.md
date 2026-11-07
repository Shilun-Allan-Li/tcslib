# PRFScheme generator-tape repair: owner interfaces and one consumer proof

**UNAPPLIED; native elaboration and whole-file sealing pending.** Frozen Gate06 library:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. The complete current library byte digest matches
the original Rule-10 manifest snapshot; no Git query was used. No library edit, Lean/cache
command, Git command, or app was used in this invocation.

## Scope and interfaces

- `MultiMessage-prfScheme-machine-readers.patch` adds only public `prfScheme_gen` and
  `prfScheme_enc` equations immediately beside their existing definition. Both proofs are
  owner-local terms `:= rfl`; all existing owner bytes and algorithms are unchanged.
- `PRFScheme-enc-length-coin-transport.patch` changes only the existing `prfFixedScheme.enc_length`
  tactic block. No nested/new tactic block, helper declaration, definition/data-field change,
  assumption, public-header change or admission is introduced in that consumer.
- The prior `PRFScheme-not-cca2-predicate-readers.patch` is unchanged and composes with this
  consumer patch in either order in memory. Existing admitted security claims remain admitted.

The original ordinal-14 diagnostic at probe **1880:89**, frozen source **61**, arises when the
proof substitutes an explicit generator constructor while `rg` still has the foreign
`(prfScheme ...).gen.Coins n` type. The old proof also applies `hFE` directly to tapes whose
`coinLen` is no longer reducible, and uses an implicit coin-length `rfl` later in the same block.

The repair first rewrites generator/encryptor fields, including binder types, through the new
owner public equations. A local term-valued `hlen` chains `NUPPT.coinLen_eq`,
`NUPPT.coins_ofPolyTimeUniform` and `PolyExpr.eval_var` to expose the length of either machine's
coin tape. `Fin.cast` transports the key and nonce to `Fin n → Bool`; `List.ofFn_congr` proves
that both transported tapes retain their exact words. Public `runAt_coinKey` and `runAt_prfEnc`
then read the algorithms, and `hFE` applies to these correctly typed tapes. Public list-length
and polynomial-evaluation equations give `2*n + 2 + n = 3*n + 2`.

There is no foreign-body `rfl` in the consumer and no foreign definition in an unfolding list.
No new import is needed. The new owner readers resolve the missing data-field interface at
its home, rather than copying foreign constructor bodies into the consumer. MultiMessage is
an additional touched module and must be included in root's post-repair collector/replay.
The required machine identities are published; no new machine abbreviation is necessary.

## Native-check limits

These proposals were inspected and applied only in memory. No Lean syntax/elaboration or
sealed result is claimed. Root should apply the owner-reader patch before checking the consumer,
then check both modules and regenerate affected seal/collector evidence. The one existing
consumer proof is the only logically changed tactic block in this invocation. Owner additions
have term proofs only. Existing public headers and data fields are preserved.

## Fingerprints

| Artifact | SHA-256 |
|---|---|
| Frozen `MultiMessage.lean` | `3ed16c59e1b352fb631b13e1c6d4526f414c4b473a493de3ba57ed5671ce6b96` |
| Proposed `MultiMessage.lean` | `efbb0e64f68e4e9dfa7973f0ee1df2a8580b877df6253398ffcd3720f858ddcf` |
| Owner-reader patch | `8e58b3ab478459a3d0ed731c2cfcf38546099578fa15eb628ef8c5b16faa3ba1` |
| Frozen `PRFScheme.lean` | `27e85230b94478b31362ed71d385f53f48f2d56695aa75683f8416b131308927` |
| Proposed `PRFScheme.lean`, this proof repair alone | `c571b1945cdcdc635c566a566e90a4ecd50f0d0899e8f482e1ee238850bd09a8` |
| Consumer proof patch | `4405173abcba7a95e4cd204c76cfc21e23c44835549f8018a66844b6e39e5354` |
| Prior non-CCA2 proposal, unchanged | `4813e8c4ab9ba334d095a35dd2c4be326761c2c2c1a121768f7f6bf9114847ab` |
| PRFScheme after both consumer proposals | `2bc8530480e0cc22c7ca87ff6e0e6d6e3a93aea83a1081dedaa246cf176a878e` |
| Public machine-reader home `PPT.lean` | `1766685ee73e2221d7cdecffe8a8cafedc43dc46af2d1b06da8c750973a453f4` |

Static checks verified one-hunk application of each new patch, exact preservation of all
existing owner bytes, all consumer bytes outside `enc_length`, admission counts, and composition
with the prior security-predicate proposal. Library source files remain at their frozen hashes.
