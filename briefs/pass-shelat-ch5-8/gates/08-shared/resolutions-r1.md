# Gate 08 (S1 / #227): round 1 resolutions

**HOLD: 0 blockers, 1 major, 3 minors returned.** The gate remains open pending the selected
Codex follow-up audit; the maintainer's repairs are not an auditor's closing verdict.

- Findings were delivered as a local untracked inbox file announced by the user, then filed
  verbatim in `findings/gate08-shared-findings.md`, SHA-256
  `e6b5c1d9427897c3521092523775276c1c7806cd5e30f0e14bf52bba3d9e28a2`.
- Audited head: `c6affb3a92535d3f1de2e0a52c205a84c0cff551`, base
  `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`; frozen evidence records
  `1c623a6c88ecfc6d5e9ae1063c743b0327fcc0ca`.
- The user has merged #195. The #227 repair worktree incorporates that campaign base, and the
  original S1 library source is preserved apart from the two planned docstring edits. The
  referenced-constant type traversal is a separate Lean metaprogram change in the PR.
- The user selected **Codex** for round 2: return `gate08-shared-r2-findings.md` in chat;
  no GitHub push. S2's worker selection is separate and must be asked before preparing that fill.

| Finding | Resolution and evidence |
|---|---|
| G08-01, major | **Confirmed; records repair made, re-audit pending.** H15 is now registered in `machine-library-design.md` §14. The row names the public contract/home, says statement only / gate 08 pending / external S2 proof, names dl-a, dl-c, rsa and rabin consumers, records the repetition-host/H14 dependency, states the polynomial-time and tail-length guarantees, and explicitly exposes no separate machine head-envelope clause at this string layer. The proof remains `sorry`; registration is not a proof or a fill dispatch. |
| G08-02, minor | **Confirmed; docstring repair in #227's worktree.** Success is a nonempty word whose tail represents the accepted value and has the stated bound. The public conclusion does not prescribe a `true` head. The proof sketch may still choose a `true` marker for one witness. No marker hypothesis/conclusion is added and the theorem statement is unchanged. |
| G08-03, minor | **Confirmed; docstring repair in #227's worktree.** `natToList_zero_append_drop` says “the last `W` bits.” Its equation, statement and proof remain unchanged. |
| G08-04, minor | **Fixed in records.** The census excludes string literals, nested comments and quoted identifiers and passes seven lexical regression cases. On the original pinned base/head, the totals are **506 → 507**. On the base after #195 and the repair head, they are **510 → 511**; #195 contributes the four authorized deferred efficiency proofs, and S1 still contributes exactly one host `sorry`. Full revision pairs appear in the census files. The old 507 → 508 files are labelled historical textual counts. |
| G08-N1, note | **Accepted staged disposition preserved.** Design G6/G7/G10 and clean-up part 2 A/N already disclose the public composition/congruence/size/restriction counterparts under Q2 (A). The round-2 pack must say no *undisclosed* public copy, rather than claim no counterpart exists. The cleanup brief also preserves the old nonempty-index restriction theorem's extra empty-codomain case when using the new generic `Nonempty O` theorem. |
| G08-N2, note | **Confirmed; collector code repair is in the PR.** Referenced-constant type traversal has been moved outside the own-module condition. Foreign definition bodies are still not traversed by this collector; that is not its claimed scope. The auditor reports the stronger traversal adds the DiscreteLog/`bitsToNat` and RSA/`primeStr` pairs, with no newly hidden touched failure. Fresh expanded collection/seal/control results are being prepared under `evidence-r2/`; they must be read as actual measured output, not assumed from that report. The gate-04 anonymous-command qualification remains in force. |

The two library edits are comment-only. The repair merge's complete library source agrees with
the base/S1 source union, with comment-stripped equality for those two files; see
`evidence-r2/merge-source-preservation.log`. The collector is changed only through the existing
PR. The maintainer does not push its `.lean` change directly to the campaign branch.

Current checks are in progress in a fresh, dedicated olean tree. No failed launch or missing
prerequisite is counted as a Lean proof check. Do not infer that the replay is complete until
its summary records completion. The round-2 pack will pin the checked PR head and records.

**Not yet clear to merge — round-1 repairs must pass the Codex follow-up audit.**
