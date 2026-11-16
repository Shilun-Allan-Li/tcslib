# Dispatch · Gate 42 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/0ddfda335430e259091127a3f62f8b5ea75f2f45/outbox/gates/42-sc-yao-gate-r2)
is staged on the exchange. The commit is local and signed, and is not pushed yet; the maintainer pushes it. Seyoon
dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 42 (sc-yao, Yao's
garbled-circuit protocol in the OT-hybrid model), round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 0ddfda335430e259091127a3f62f8b5ea75f2f45.
   Read outbox/gates/42-sc-yao-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/42-sc-yao-gate/ at exchange
   747b61e7d95d44461639c5884aed33aa4908fc00; the round-1 findings are
   findings/gate42-sc-yao-findings.md in the round-2 folder.
2. Re-audit draft PR #341 at Lean head 355a0288d56290e8c984228cbc1824187029e456,
   with campaign records 2da7e0f3cd65ec93ed71813b7828c3b66ba18942, using the pack.
   Round 1 was HOLD at e9b03c437aca251846430ff23b40ee5ff3d3347a (0 blockers,
   1 major, 2 minors, no mathematical gap). The head adds three landing edits
   on that commit. Say whether each round-1 finding is closed:
   - G42-01 (major), by LE-reuse-2 26f0b77b: RunWithHost.acc_poly is now
     derived from the public Complexity.StateLoop.MajLoop.acc_poly. Check
     that the new body reads MajLoop.acc only through the published readers
     acc_eq and MajLoop.acc_eq, unfolding neither definition; that the edit is
     proof-only, with no import change and the statement unchanged; and that
     the docstring discloses the reuse. The committed body is not round 1's
     simpa candidate (pack § 1).
   - G42-02 (minor), by LE-refs 3e99eb80: the full [AB09] and [BMR90] entries.
     Are they correct, and is the edit comment-only?
   - G42-03 (minor), by LE-steps 355a0288: step comments in the six proofs.
     Are they accurate against the proofs and their sketches?
   LE-refs and LE-steps must be comment-only: each file equal after
   stripping comments, and removing the inserted lines restoring the
   parent byte for byte. Yao.lean's frozen regions must still hold: only
   the six approved regions and LE-title's title line differ from the tip,
   and the file has 1195 lines, within the 1,200 cap.
   Check the integration evidence and its binding to the head (pack § 6):
   - M = the records tip f22e0f67 merged with e9b03c43, and M' = f22e0f67
     merged with 355a0288; their trees are reproducible with git merge-tree;
   - the builds and state checks;
   - the axioms, with yaoProtocol_hbcSecure now standard;
   - admissions 229 -> 227;
   - the seals: Yao.lean at M, and RunWithHost in all four variants at M'.
     The comment-only files were not re-sealed at M'. Say whether that
     evidence suffices or a re-run is necessary.
   Say whether the round-1 confirmations still hold (pack § 7), and
   whether anything new is undisclosed (§ 8 and the known slips). The earlier
   rulings stand: SY-F01 to SY-F05, and ledger rows DL-49 (with the d6fe1ddd
   wording), DL-51 and DL-52. Integration with the other open PRs (#331,
   #338, #339) is a maintainer merge condition, not an audit item.
3. Return gate42-sc-yao-r2-findings.md as Markdown in this chat. If you need
   multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records:** the pin `2da7e0f3` is the records tip. This gate directory's round-2 files are written but not
  committed; the maintainer commits them. They are `pack-r2.md`, `pr-r2.diff.txt`, `pr.diff-r2.txt`,
  `source-head-r2.json`, `sources-r2.zip`, `verification-r2.zip`, `pr-description-r2.md`, `SHA256SUMS-r2` and this
  file. The exchange copies equal them byte for byte.
- **Exchange:** the commit is `0ddfda335430e259091127a3f62f8b5ea75f2f45`, on the exchange tip
  `309071c6efc7a98cf0e832c7ff0c8973127d3701`, which was fetched at staging. The tip is not the expected `7031cef6`:
  one external checkpoint commit landed after it.
  - The local branch is `stage/gate42r2-exchange`, in the sparse worktree `wt-exch-g42r2`.
  - The commit adds 16 files under `outbox/gates/42-sc-yao-gate-r2/` and nothing else, and is SSH-signed.
  - It is **not pushed**.
- #341's description already names the head `355a0288`, so no PR update is needed before dispatch.

The exchange commit `0ddfda33` (on `309071c6`, after the T4 worker's checkpoint 1) and the records (pin `2da7e0f3`, then this staging commit) are pushed.

**Ready to dispatch** once the records files are committed and both the records and the exchange commit are pushed.
