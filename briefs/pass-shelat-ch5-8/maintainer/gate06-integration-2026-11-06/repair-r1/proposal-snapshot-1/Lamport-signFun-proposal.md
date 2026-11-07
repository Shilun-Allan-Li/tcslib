# Lamport signer: one-proof public-reader proposal

**Unapplied and unchecked.** Frozen source head:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Patch: `Lamport-signFun-public-readers.patch`. Apply it **after** the previously proposed
`Lamport-genFun-public-readers.patch`. The generator patch was composed only in memory to
produce this patch's base; neither patch was applied to the library.

## Selected diagnostic and repair

Completed survey 009 maps probe `1728:81` to frozen-source `311:81`, the theorem
`polyTimeComputable_lamportSignFun`; its final conversion is at frozen line 320. The
polynomial-time witness builds nested pairs beneath `blockEncFun` and `decListFun`, while
the target wraps the same fields in foreign `blockState`. The unsealed conversion relies
on reducing that definition.

This invocation changes **only that existing proof block**, replacing its final `convert`
with pointwise transport through public `PolyTimeComputable.congr` and simplification by:

- owner-local `lamportSignFun_eq`;
- public foreign reader `blockState_eq` (`Asymptotic/BlockEncryptor.lean:80`);
- Core theorem `Function.comp_apply`.

The tuple flattener `decListFun`, block encryptor `blockEncFun`, raw-input projections and
other foreign ordinary definitions remain opaque and identically applied on both sides.
No helper-header or coin transport change is needed for this selected function proof.
Headers, algorithms, premises, imports, admissions and tactic-block count are unchanged.

## Fingerprints and static verification

| Version | SHA-256 |
|---|---|
| Frozen library file | `91dcee4158e54b53372ea573067d8bb08576f73f2b4c08af2889c80d0eebd391` |
| In-memory base after generator proposal | `00c992722bf74791be20bd6d6caf35e322c346be27d7f65c97ad3b81b33bc7b7` |
| In-memory result after generator + signer proposals | `8812be18ab448ff11d1c4f8a8ed0ba995831618780580d724a665f9a437ae09b` |

Both patches apply in memory with exact context. Relative to the in-memory base, every byte
outside the signer proof is unchanged. The actual library still has the frozen fingerprint.
No Lean/cache, Git command, app or native seal check was run. The proposed term is unchecked.

The verifier's unresolved `decide` conversion and correctness proof's `coinLen` reduction
remain flagged in `Lamport-one-proof-proposal.md`. No further proof block was written here.
The source snapshot and the completed four-diagnostic survey are unchanged.

**Not yet clear to merge — proposals remain unapplied/unchecked; other Lamport diagnostics and root verification remain.**
