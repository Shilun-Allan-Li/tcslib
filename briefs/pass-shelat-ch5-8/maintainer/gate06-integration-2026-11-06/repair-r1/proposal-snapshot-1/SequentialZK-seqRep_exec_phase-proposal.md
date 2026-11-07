# SequentialZK seqRep_exec_phase: zero-case public-reader proposal

**Unapplied, unchecked proposal.** Explicit source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

The existing comment-only `SequentialZK-doc-abort-premise.patch` was composed strictly **in memory only**, so this proof patch is based on that documented source. Its existing source-fidelity edits are not duplicated in this patch. Neither patch was applied to the library.

## Observed failures

Completed log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs/G06Seal_016_TCSlib_Cryptography_Composability_SequentialZK.log`.

The valid installed-status marker records 853 requested/active/verified names, none already irreducible. Its two source errors are both in the same existing theorem, `Protocol.seqRep_exec_phase`:

| Case | Frozen source | Probe | Goal after dropping the earlier phases |
|---|---:|---:|---|
| `zero.left` | 305:8 | 1212:8 | `[] = (exec π.P π.V vF x y z sP sV 0).1` |
| `zero.right` | 309:8 | 1216:8 | `[] = (exec π.P π.V vF x y z sP sV 0).2` |

The two old `rfl` leaves reduce foreign `exec` at zero. Their failure does not require changing the protocol construction or any premise.

## Exact two term replacements within one declaration

Replace the first `rfl` by:

`exact (congrArg Prod.fst (exec_zero π.P π.V vF x y z sP sV)).symm`

Replace the second `rfl` by:

`exact (congrArg Prod.snd (exec_zero π.P π.V vF x y z sP sV)).symm`

The public reader already exists in `ZeroKnowledge/Interaction.lean:255–257`:

`exec_zero P V vFirst x zP zV rP rV : exec P V vFirst x zP zV rP rV 0 = ([], [])`.

Projecting this equation gives each execution history equal to `[]`; symmetry gives the required orientation. The projection of the literal pair is ordinary constructor computation. No foreign `exec` body or generated matcher is read, and no explicit unfold/rewrite list is added. No new owner reader, public API, helper definition, simp attribute or admission is needed.

Only `seqRep_exec_phase`'s single existing declaration proof changes. Its header, hypotheses, local bindings, phase arithmetic, list-length bounds, induction structure, successor case, protocol definitions and every other declaration remain unchanged relative to the composed base. Both replacement leaves are proof terms; no new `by` block is introduced.

## Fingerprints and static checks

| Item | SHA-256 |
|---|---|
| Frozen SequentialZK source | `323bbcbd042abeabdc408e2a64a808b8e3ffb9cfd20601093f2ab3d9e3391062` |
| Existing comment-only patch | `71754da3f546cd37b3392edf019f6e316cb110d9d5f8071a0d4ed33508530b81` |
| Comment patch composed in memory (proof patch base) | `ff83de2b5ae739f2dc712950974705ccd1bbfade18628ccaed40eac569c0fa1d` |
| Comment and this proof patch composed in memory | `f7c9a99f7cc657e83205e7f37063ac232fb3fecd6ce61f422829845e2d8a7a72` |
| This unapplied proof patch | `3cf5f9cf0b0f8cade6ea2d2e87d468eaa4667acdd6810343b42981b4c587ef64` |
| Completed original seal log | `61de8218db1b6a86604600c725fdb7c84f5822fcdf169f37c93d141392a9b129` |
| Recorded original seal probe | `03341ee31774ed7d8127cccb25e594ffcaddce240d79618522cb43da0cd0f54f` |

Both comment-patch hunks matched their frozen contexts strictly. The entire old zero-case segment matched exactly once; replacing it and splitting before/after confirms that every other byte is preserved. The number of `:= by` blocks is unchanged. The manifest line map explicitly confirms source 305→probe 1212 and source 309→probe 1216. The live source retained the frozen fingerprint and HEAD.

## Native confirmation and limits

Root should check the composed source through the authorized serial process, then rerun the whole-file seal with installed-status verification and inspect the changed theorem's collected reads, axioms and explicit-list scan. The two observed zero-case diagnostics should be removed by the public equation; this static proposal does not claim native or full-module success.

No Lean/cache, apps, Git mutations or library edits occurred. Only the requested ignored patch and notes were saved.

**Not yet clear to merge — the proof proposal is unapplied and requires native replay/seal.**
