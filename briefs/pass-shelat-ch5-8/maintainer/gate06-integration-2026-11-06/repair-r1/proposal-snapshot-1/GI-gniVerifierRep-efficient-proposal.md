# GI repeated GNI verifier: one efficiency-proof reader repair

**Unapplied, unchecked proposal.** Explicit Gate06 worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
All source input was read through exact `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>`; mutable worktree source bytes were not used.

This invocation changes **one existing proof declaration**, `GI.gniVerifierRep_efficient` in EfficiencyRep, and adds two owner-local **term** field readers beside `GI.gniVerifierRep` in Proofs. No new tactic block, definition, algorithm, hypothesis, admission, simp attribute or host is introduced. The existing efficiency header and the entire original strategy definition are literal matches.

## Valid seal evidence

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_039_TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_EfficiencyRep_HarnessV3.log`.

The selected source diagnostic is **EfficiencyRep source609:2 → probe659:2**, log line **1028**, inside the existing theorem starting at source595. Its `show` attempts to read the foreign owner definition `GI.gniVerifierRep` to make the left side an `if`. Under the valid seal the target remains

`gniVerifierRep.next x z r hist = <the polynomial-time layout function>`,

so that implicit conversion fails. The owner definition is at frozen Proofs:162–172. No general next/coins readers for this shadow strategy exist at the frozen source; the specialized SoundnessRep next lemmas are later dependents and are not an import route for EfficiencyRep.

This is one of the seven genuinely changed GI declarations from the full-survey review. Its source identity does not earn an inherited exemption. The seven other observed EfficiencyRep diagnostics belong to different declarations and remain outside this repair.

Log SHA-256: `354ac046a20615b66260ea1119e6e6bf31989cf39831966d42cbd55df1694e83`.

## Two complete owner term readers

Add beside the unchanged strategy in `GraphIsomorphism/Proofs.lean`:

- `GI.gniVerifierRep_coins`: the existing polynomial `.mul .var (.add (.const 1) (.normal 1 2))`, proved by owner-local `rfl`.
- `GI.gniVerifierRep_next`: the total next-message equation, for all input words, auxiliary words, tapes and histories, proved by owner-local `rfl`.

The next equation exposes the owner-local `instanceVertexCount` and `instanceG₀/G₁` calls as their `Nat.sqrt (pairFstD x).length` / `decGraphAt` formulas. This prevents the consumer's subsequent reflexive comparison from depending on a second sealed owner helper. The count is unchanged for every word, including malformed encodings. All foreign operations remain the same public constants: `coinBlock`, `encGraph`, `permGraph`, `samplePerm`, list operations and the graph decoder symbol. Their bodies are not explicitly unfolded.

The coin-block width is still `1 + (x.length + 1)^2`. Before `hist.length < x.length` the verifier selects/relabels the graph using that block; afterwards it returns the original well-formedness-and-challenge-comparison decision. There are no new preconditions or shortened cases. The unused auxiliary argument remains an explicit arbitrary argument in the total reader.

## One existing consumer block

In `EfficiencyRep.gniVerifierRep_efficient`, replace only the failed proof step

`show (if hist.length < x.length then _ else _) = _`

with

`rw [gniVerifierRep_next]`.

The existing runtime witness, selection/sampling/scan construction, layout normalization, both branches and `gni_verdict_iff` application remain otherwise unchanged. The existing sketch gains the name of the reading equation. Existing `sampleStr_eq`, `relabelAt_replicate`, layout equations and `decPerm_encPerm` continue to read the other functions through public interfaces.

No foreign ordinary definition is added to an explicit tactic list. The added field readers are term `rfl` proofs owned by the file containing the definition; they do not create another logical tactic block.

## Fingerprints and static checks

| Source file | Frozen SHA-256 | Proposed SHA-256 |
|---|---|---|
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean` | `353569e786eae6f1aeb04358ad992cb4c4e6602fd9bbc37a8757fb92bf2b8bcf` | `08b9c3a1e960cb5682e05b1af57cac9f0afb3edcb8f6eb8beb72ea7c8b800a42` |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | `21d08b837c0ab801e6e6d74ece11a5b58c1f91584454bb35d57fee37cf225ddb` | `c2a2302cf0b1db753c7c30a01fe3237f8a5b35c14709500618009cc2936b085f` |

Patch SHA-256: `6252fce6b336b07f58834da02137a3c59505c51c55a714d376a4afa81ecc524f`.

Insertion/replacement anchors matched exactly once. The owner strategy's complete raw definition was checked literally preserved; the consumer theorem header was compared literally through `:=`. Both source files retain their existing `:= by` counts, and the added reader text contains no `by`, admission or simp attribute.

## Replay requirement and limits

Root must check the new owner terms in Proofs first, then replay Efficiency and the affected downstream import closure before checking the consumer or its seal. An old Proofs object cannot supply these new reader names. Recollect the changed consumer/readers and rerun the valid whole-file seal, explicit-list scan and axiom checks; do not infer a pass for the seven unrelated EfficiencyRep failures from this targeted repair.

The other six genuinely changed GI proofs remain for later invocations. The finished full-survey classification files were not modified. No Lean/cache, apps, Git mutations, source edits or received-program execution occurred; only ignored proposal artifacts were saved.

**Not yet clear to merge — the owner readers and one consumer repair are unapplied/unchecked and require root's serial replay/seal.**
