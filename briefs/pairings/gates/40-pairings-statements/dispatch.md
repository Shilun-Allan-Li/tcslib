# Dispatch · Gate 40

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/870bed6ca6d79f43599ab2972f74834137672b2a/outbox/gates/40-pairings-statements-gate)
is staged on the exchange (local commit on branch `stage/gate40-exchange`, for the maintainer to verify and push).
Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 40 (pairing campaign statements) in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 870bed6ca6d79f43599ab2972f74834137672b2a.
   Read outbox/gates/40-pairings-statements-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #331 at Lean head 110c2f9db810d243693b9a5e8976a5ad205f1bab,
   with campaign records 356321accdd29b9ec73391b1c7b211b7d4cabf0f, using the pack.
   This is a statement audit of the pairing campaign (PairingCryptographyPlan.md,
   rulings Q1-Q13 and the location ruling). Check the fidelity of the
   definitions to [Jou00] and [BB04] (ePrint numbering) under the rulings,
   using the source excerpts in the pack: the bilinear bundle and generator,
   BDH and DBDH, the IBE interface and the selective-ID game (Init oracle,
   bottom for forbidden queries, l-bit identities, two-experiment advantage),
   BB1 and the simulator. Check that every target T1-T4 is true and
   sufficient, that T2-T4 imply bb1_sidSecure with no hidden hypothesis, and
   audit as proofs the results already proved: Joux correctness and key
   indistinguishability, jouxGame_eq_dbdhGame, BB1 correctness and the
   derivation of bb1_sidSecure from T2-T4. Also check Rule 10, readers and
   seals (the canonical seals cover 3 of the 12 modules; rate the round-1
   hand-list seals for the rest), docstrings, source tags and sketches
   against the papers' numbering and the disclosed deviations, the fill-unit
   split (bb1-sim and bb1-machine own disjoint files), duplication against
   the DDH, El Gamal and Games layers, and policy (modularity, sizes,
   facades). The add/add conflict with #333 in the shared AdvancedEncryption
   facade and the rebuilds listed under Merge interaction are merge
   conditions the maintainer runs, not audit items.
3. Return gate40-pairings-statements-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `356321ac`, then this dispatch commit) and the exchange commit `870bed6c` (on the exchange tip
`da8f8f66`) must be pushed first.

**Ready to dispatch**
