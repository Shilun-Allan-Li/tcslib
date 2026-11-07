# PublicKey ofPadded.enc_length: one caller-block proposal

**Unapplied, unchecked proposal.** Explicit source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

The two earlier PublicKey patches were composed **only in memory**, in this order:

1. `PublicKey-runAt_padEnc-coins-transport.patch`
2. `PublicKey-ofPadded-correct-coins-transport.patch`

This separate third patch changes one line in the existing `FixedLengthPKScheme.ofPadded.enc_length` proof (frozen source 268–271, composed-source 272–275):

```lean
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))
```

After the repaired run contract rewrites the padded activation, its ciphertext is the original encryptor's activation on the coin input

`NUPPT.coinsCongr (padEnc_coins enc L) n re : enc.Coins n`,

where `re : (padEnc enc L).Coins n`. The original `hL` assumption instantiated with that argument gives exactly `2 * ciphertext.length + 2 ≤ L.eval n`. Existing `length_padCt` then proves the required padded length. The public coin equivalence preserves the exact coin string, so there is no change to the sampler or length premise.

No header, premise, algorithm, data field, admission, other proof block or definition body outside this proof changes. The prior `ofPadded.correct` proposal is retained byte-for-byte in the in-memory composition. This invocation adds no tactic block; it changes only the final application in one existing block. The rewrite item is an existing owner-local theorem, and the public coin equivalence is applied without unfolding any foreign definition.

## Fingerprints and static checks

| Stage | SHA-256 of PublicKey source |
|---|---|
| Frozen library | `8bc99296a28985a783285c42db1bc0e27787538e78d3c909bbff594dc0ef9717` |
| After run-contract proposal in memory | `915d1fea150487befcac3c2d9c169b025c352f93b48d5e9dc1bbf203fd36d18a` |
| After run-contract and correct proposals in memory | `91a8769181a222b915de43429e51f27813e403225bc75da96f491821fad4f564` |
| After all three proposals in memory | `8bae0ef1abea902f1c99bd0979932d48b1b8169ff4281b19bef8cdf30a863dc9` |

Patch SHA-256: `c89c07f4238068843e9812987f9b03160e778cc5a129aa73473bd184a05561ae`.

Both prior patch contexts matched strictly. Their composed source matched the previously recorded fingerprint. The old four-line `enc_length` block matched exactly once, and splitting before/after around that block confirms every other byte is unchanged. The `:= by` count is unchanged. The complete prior `correct` block was separately checked unchanged. The live PublicKey source and HEAD retained their frozen values.

Root should apply/check the three proposals in order after the freeze is released, then rerun the native module, collector/axiom checks and whole-file seal with installed-status verification. These proposals are intended to remove the observed typed-coin header failure and make both direct callers use the same public transport; they do not constitute a native pass claim.

No Lean/cache, apps, Git writes or library edits occurred. Only the requested ignored patch and notes were saved.

**Not yet clear to merge — all three PublicKey proposals remain unapplied and require native replay/seal.**
