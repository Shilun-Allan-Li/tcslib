# Repeated GNI verifier next-message cases: two term-only repairs

**Unapplied, unchecked proposal.** Explicit Gate06 worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
All original source is from exact `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>`, not live worktree bytes.

## Ordering and scope

Compose the existing proposals in this order, **in memory only**:

1. `GI-gniVerifierRep-efficient-public-readers.patch` — SHA-256 `6252fce6b336b07f58834da02137a3c59505c51c55a714d376a4afa81ecc524f`.
2. `GI-giProverRep-efficient-public-readers.patch` — SHA-256 `fc4dffddcd8ca9c4f9628ccee6e41ccf91b7accfc022c7bb4141322dd198243e`.
3. This separate `GI-gniVerifierRep-next-terms.patch`.

The earlier patches are not overwritten. This third patch adds one owner-local term branch reader in Proofs and replaces **both** existing SoundnessRep next-case proofs by equality terms. It writes **zero tactic blocks** and removes the two old blocks. Consumer headers/premises and all algorithm definitions/data/admissions are preserved.

## Valid frozen diagnostics

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_042_TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_SoundnessRep_HarnessV3.log`.

| Declaration | Frozen source error | Probe error | Log line |
|---|---:|---:|---:|
| `gniVerifierRep_next_lt` | 152:2 | 202:2 | 978 |
| `gniVerifierRep_next_ge` | 173:2 | 223:2 | 985 |

Both old `show` steps try to turn the foreign strategy's opaque `next` application into its implementation conditional. The field reader from proposal 1 supplies that equation publicly.

Log SHA-256: `a6f6c7623be3bbc015746cbf58ed7c585db3d9a66720806d814a6128b247ce7a`.

## One owner term bridge, no algorithm change

Add beside the existing GNI field readers in `GraphIsomorphism/Proofs.lean`:

```lean
theorem gniVerifierRep_next_run (x z r : List Bool) (hist : List (List Bool))
    (h : hist.length < x.length) :
    gniVerifierRep.next x z r hist =
      gniVerifier.next x z (coinBlock (1 + (x.length + 1) ^ 2) hist.length r) [] :=
  (gniVerifierRep_next x z r hist).trans (if_pos h)
```

This is a next-message branch contract: before the replies are exhausted, the repeated verifier sends exactly the single verifier's first message on the current tape block. Its only case premise is the existing branch condition. Inside the owner, the single verifier and the local graph/count aliases may reduce; the two strategy algorithms are untouched. Foreign graph/sampling/coin operations remain identical symbolic applications.

No new helper definition, host, data transformation, simp attribute, reducibility override or admission is introduced.

## Both consumer proofs are terms

For `gniVerifierRep_next_lt`, use the branch bridge on the encoded instance, followed by existing public `GI.gniVerifier_next_nil` (frozen Proofs:460–473) on that same coin block. The existing single-message equation already gives the graph pair and vertex count at `n`. Reusing that public contract removes the need to unfold `encInstance`, `instanceVertexCount`, `instanceG₀/G₁` or to recreate their decoding/count-transport proof in a consumer.

For `gniVerifierRep_next_ge`, use

`(gniVerifierRep_next x z r hist).trans (if_neg (not_lt.2 h))`.

Its else branch is literally the original verdict statement. No precondition or case is removed. The old `<` proof sketch is refreshed to describe the public single-run route; no other declaration changes.

There are no explicit consumer tactic lists or foreign-body conversions in these new term proofs. The owner bridge uses only an owned field contract and the standard `if_pos` theorem.

## Fingerprints and static checks

| Source / stage | SHA-256 |
|---|---|
| Frozen Proofs | `353569e786eae6f1aeb04358ad992cb4c4e6602fd9bbc37a8757fb92bf2b8bcf` |
| Proofs after first two proposals in memory | `934202753018670ccb0919a08e8e2ab8e03b4e6173b65b8f5f85de60314b4008` |
| Proofs after this proposal in memory | `25eca9f3304390f3296f3fbc139209d182118dbfcb78ebce61f942a2b6eeb3de` |
| Frozen SoundnessRep | `8b42199908b4e9e04363cc616a7e77283e18d3e6301b0ef7adca849afe6c87a6` |
| Proposed SoundnessRep in memory | `76744c63341aa7d92b4525e39a15cab776f4950c6d96c80207f7975b52a5ca6e` |

Patch SHA-256: `d572d42f26fd3e321eb5ec3e645729fab31d213c8e9513ba59770069e1304da0`.

Both prior patches composed with strict context checks, and their resulting Proofs fingerprint matched the recorded value. Both consumer headers were compared literally through `:=`. The original repeated-verifier definition remains literally present. The new reader and replacement proof text contain no tactic-block introducer; SoundnessRep's `:= by` count decreases by exactly two, and Proofs' count is unchanged.

## Native checks and remaining scope

Root must check/replay Proofs with all three proposal stages before checking SoundnessRep and the affected downstream closure, then collect reads/axioms and rerun the valid seal and explicit-list scan. Reusing `gniVerifier_next_nil` means reading its published statement, not copying or unfolding its proof.

The other eight original SoundnessRep diagnostics remain untouched source-inherited observations, not passes. The two genuinely changed GI prover next-message cases and `attemptAt_poly` remain later work.

Previous proposal/review files were not modified. No Lean/cache, apps, source edits, Git mutations or received-program execution occurred. Only separate ignored patch/notes artifacts were saved.

**Not yet clear to merge — the branch bridge and both term repairs are unapplied/unchecked and require root's serial native replay/seal.**
