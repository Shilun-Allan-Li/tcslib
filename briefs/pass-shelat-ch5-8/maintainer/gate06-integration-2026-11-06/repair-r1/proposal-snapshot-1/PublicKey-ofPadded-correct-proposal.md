# PublicKey ofPadded.correct: one caller-block proposal

**Unapplied, unchecked proposal.** Source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

This patch is based on `PublicKey-runAt_padEnc-coins-transport.patch`, composed **only in memory** over the frozen source. The library remains unchanged.

## Exact scope

Only the existing `FixedLengthPKScheme.ofPadded.correct` field proof is changed (frozen source 264–267, composed-source 268–271). Its final application now supplies the original correctness assumption with the encryptor coin input exposed by the repaired run contract:

```lean
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
```

No header, hypothesis, algorithm, data field, admission, definition body outside this proof or other proof block changes. The `enc_length` proof is byte-identical and explicitly remains pending for a separate invocation.

## Why this is the required caller transport

In the wrapper's correctness field, `re` belongs to `(padEnc enc L).Coins n`. The existing public equality

`padEnc_coins enc L : (padEnc enc L).coins = enc.coins`

identifies the two coin polynomials. Its public equivalence `NUPPT.coinsCongr (padEnc_coins enc L) n` maps this `re` into `enc.Coins n`, preserving the exact coin list through `NUPPT.coinsCongr_ofFn`.

The preceding repaired `runAt_padEnc` rewrite already produces the original encryptor's run on precisely that transported coin argument. `padDecFun_padCt` removes padding. The remaining goal is therefore exactly the original `correct` assumption instantiated with the same `n`, `m`, `rg` and transported `re`. No new logical premise is needed.

This block applies the public equivalence without unfolding its body. The two rewrite items are existing owner-local theorems; no explicit foreign ordinary/Core/Mathlib definition is added to a tactic list.

## Static fingerprints and checks

| Stage | SHA-256 of PublicKey source |
|---|---|
| Frozen library | `8bc99296a28985a783285c42db1bc0e27787538e78d3c909bbff594dc0ef9717` |
| Prior run-contract proposal in memory | `915d1fea150487befcac3c2d9c169b025c352f93b48d5e9dc1bbf203fd36d18a` |
| Prior proposal plus this caller repair in memory | `91a8769181a222b915de43429e51f27813e403225bc75da96f491821fad4f564` |

Patch SHA-256: `637181610c6bf4996d0270787aebe3f4ca55de5985e5006dbcd218fee0a48318`.

The prior patch's old context matched exactly and its composed source matched its recorded fingerprint. This field's old four-line block matched once. Before/after splitting around that block confirms every other byte is unchanged. No `:= by` block was added, and the complete `enc_length` block was separately checked unchanged. The live PublicKey source retained its frozen fingerprint.

## Native confirmation and remaining work

Root should check this caller after the run-contract proposal, then repair `ofPadded.enc_length` in its own later invocation and perform the native module/seal checks. The full module is not claimed repaired by this patch alone. No Lean/cache, apps, Git writes or library edits occurred; only ignored proposal artifacts were saved.

**Not yet clear to merge — this caller proposal and the preceding contract remain unchecked; enc_length is deliberately untouched.**
