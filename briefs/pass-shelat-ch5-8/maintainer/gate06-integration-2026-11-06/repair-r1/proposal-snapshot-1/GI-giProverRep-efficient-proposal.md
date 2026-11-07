# GI repeated prover: one efficiency-proof public-reader repair

**Unapplied, unchecked proposal.** Explicit Gate06 worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen input source: exact `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>` only; mutable library bytes were not used.

## Composition and exact scope

First compose `GI-gniVerifierRep-efficient-public-readers.patch` in memory. Both its owner-reader and earlier EfficiencyRep consumer hunks were checked strictly; its saved bytes remain unchanged (SHA-256 `6252fce6b336b07f58834da02137a3c59505c51c55a714d376a4afa81ecc524f`).

This new patch contains **additional hunks**, not a replacement of that prior proposal:

- Two owner-local **term** readers beside `GI.giProverRep` in Proofs.
- One existing consumer proof-block repair in `EfficiencyRepGI.giProverRep_efficient`, plus the matching name in its existing sketch.

No new tactic block, simp attribute, algorithm, data field, premise, admission, helper definition or host is introduced. The complete original prover definition and consumer theorem header are literal matches. Other existing proof blocks are untouched.

## Valid frozen seal error

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_040_TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_EfficiencyRepGI_HarnessV3.log`.

The selected error is **source120:2 → probe170:2**, log line **972**, inside the theorem beginning at source109. The valid marker verifies 968 active/requested names.

The old `show` expects an `if hist.length % 2 = 0` expression, while the target retains sealed foreign `giProverRep.next x z r hist`. The owner strategy is frozen Proofs:215–222. Its specialized next-even/next-odd lemmas live in later SoundnessRepGI and cannot supply an import route here; no general next/coins readers exist at the frozen source.

Log SHA-256: `4694ca76d8b5f164d00b8d070618416577e8ed2799c53a42cba909f2e312fc93`.

## Owner term interfaces and the one consumer step

Add `GI.giProverRep_coins` with the existing polynomial `.mul .var (.normal 1 2)`, and `GI.giProverRep_next` with the full total next-message formula. Both proofs are owner-local `rfl` terms.

The next equation spells the owner-local `instanceVertexCount` and `instanceG₀` via `Nat.sqrt (pairFstD x).length` and `decGraphAt`. Other operations remain public constants. Its block width and index remain `(x.length + 1)^2` and `hist.length / 2`. At an even count it sends the relabelled first graph; at an odd count it returns the sampled permutation, multiplied by the inverse decoded witness exactly when the last challenge bit is true. The equation covers every input word/history/tape without a well-formedness premise.

The consumer changes only the failed conversion:

`show (if hist.length % 2 = 0 then _ else _) = _`

becomes

`rw [giProverRep_next]`.

The polynomial-time sampling/graph/reply witness, half-count and parity normalization, public `sampleStr_eq` / `relabelAt_replicate` / `mulInvStr_encPerm` equations, and both final branches remain otherwise unchanged. The owner equation exposes the local graph/count aliases needed by those branches so the repair does not simply move the same forbidden read to a subsequent reflexive leaf.

No foreign definition is explicitly unfolded by the added consumer step. The new reader terms reduce only definitions owned by Proofs; no new logical tactic block is created.

## Fingerprints and static validation

| Item | SHA-256 |
|---|---|
| Frozen Proofs | `353569e786eae6f1aeb04358ad992cb4c4e6602fd9bbc37a8757fb92bf2b8bcf` |
| Proofs after earlier GNI proposal, in memory | `08b9c3a1e960cb5682e05b1af57cac9f0afb3edcb8f6eb8beb72ea7c8b800a42` |
| Proofs after both proposals, in memory | `934202753018670ccb0919a08e8e2ab8e03b4e6173b65b8f5f85de60314b4008` |
| Frozen EfficiencyRepGI | `65f9e7e23fb8b14dfea12e3612ad53acae5e81ee8847404ad85b1f4118b08d4a` |
| EfficiencyRepGI after this proposal, in memory | `cbe9ef3898bb7555c8e91a973f1f64d33d144304f47d857781e0e0f75652559a` |

New patch SHA-256: `fc4dffddcd8ca9c4f9628ccee6e41ccf91b7accfc022c7bb4141322dd198243e`.

All prior and current insertion/replacement contexts matched exactly once. The earlier GNI reader declarations were checked retained literally. The prover's full raw definition and consumer header through `:=` are unchanged; both files' `:= by` counts remain unchanged. The added reader text contains no `by`, admission or simp attribute.

## Required replay and remaining scope

Check Proofs with both sets of owner readers before replaying Efficiency, EfficiencyRep and EfficiencyRepGI and the other affected downstream closure. Imported old objects cannot provide these new names. Root should then re-run the native consumer/seal, collected-read/axiom checks and explicit-list scan.

The remaining three observed EfficiencyRepGI diagnostics (two in `gi_verdict_iff`, one in `giVerifierRep_efficient`) are untouched inherited-source observations, not repaired or declared passing here. The other four genuinely changed soundness next-message proofs and `attemptAt_poly` remain later invocations.

The previous GNI patch and finished full-survey review files were not modified. No Lean/cache, apps, Git mutations, library edits or received-program execution occurred. Only separate ignored proposal artifacts were saved.

**Not yet clear to merge — both owner-reader proposals and this one consumer repair require root's serial native replay/seal.**
