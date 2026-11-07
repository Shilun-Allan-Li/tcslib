# #195 at 9ac1c426: re-merge on the landed base

The newest base is merged into `wip/g04r6` and all checks pass again: 26/26 seal with no entries, no scan hits, replays clean. Nothing is pushed.

**New head:** `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`.

## Merges since f4b2c95d
1. `8fd2a633a30357489478e8474b13f6ea62f001cc` merges a3cca8ab0c456088132501a57eb751bccdf98ef5 (#210 merged; its Lean sources equal eb99dd7b, which I verified).
   - The expected Experiments.lean conflict did not happen; git merged it cleanly.
   - The result keeps the base's new formula docstrings on `invProb_def`, `predProb_def`, `acceptProb_def` and `distAdv_def`, and #195's proofs in that file (`statDist_eq`, `uexp_def`).
2. `9ac1c426` merges the branch head 7018d13e243df4d8b54b99444c34c934199755f5. Its latest commit touching `TCSlib/` is 8dcdc8a56382289b5739e13fd18c4d5bd9b67c47 (fill landings #224–#226); the commits after it are records. The merge was clean, and none of the landed files is among the 26.

## Diff stat
`git diff --stat 7018d13e..HEAD | tail -1`:
`26 files changed, 2723 insertions(+), 287 deletions(-)`
- That is 25 of #195's Lean files plus `TCSlib.lean` (one added import of `TCSlib.Cryptography.Games.Bridges`).
- `Foundations/Probability.lean` no longer differs from the base.

Against 8dcdc8a5 itself the count is 52 files (3727+/287−). The 26 extra files are the base's own later records commits (briefs/…, `PassShelatChapter5-8Plan.md`), which my merge of 7018d13e includes. 7018d13e is therefore the base the PR will be compared with.

## Re-run at 9ac1c426
- **Replay:**
  - First pass (`r10/replay.log`): the 108 modules of the closure changed since f4b2c95d, including all 23 landed Candidates/ThreeColoring modules and `audits/pass-shelat/Checks`. All rc=0, no errors.
  - Second pass (`r10/replay-extra.log`): the 23 remaining modules downstream of the 26 files anywhere in the repository (`tools/downstream.py`), including `audits/garg-ch1-3/Checks`. All rc=0, no errors.
  - The root facade `TCSlib` was not replayed.
  - **Post-audit correction:** the audited implementation set has four explicit deferred `sorry` proofs in Games/Efficiency: `exists_handlerMachine`, `exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, and `exists_toOracleAdversary_of_bitCodec`. The replay also has Universal (1) and UniversalPadding (1), outside that implementation set; Candidates and Checks have 0. See `../evidence-r5-review/ERRATUM.md` for file-set and axiom-print scopes.
- **Seal:**
  - Derivation from an empty seed: `unseal.json` = `{}`.
  - Head seal: 26/26 PASS with no entries. Plain seal: 26/26 PASS.
  - #210's sweep rows tagged 195: all 16 pass the head seal, and the control fails at each.
- **$BASE control:** 10 PASS, 16 FAIL, the same files as before.
- **Scan:** 0 / 0 / 0 at the head.
- **Union check:** 5/5 PASS.
- **`exclusions.md`:** no entries.
- **Axioms:** 198 public theorems in the 8 files changed since 40553944, all within propext, Classical.choice and Quot.sound; no sorryAx, 0 errors.
- **Lint:**
  - style_lint: 0 findings in each of the 8 changed files and over all 26.
  - check8b: 0 FAIL in Asymptotic, Pseudorandom/Functions, Foundations and Games.
  - ZeroKnowledge still has the same 9 facade-import FAIL rows, all outside the 26.
  - No file is over 1000 lines.
- **Classifier:** SAME 279, ADDED 210, CHANGED 152, INDUCED 4, unchanged.
- **Statement diff against f4b2c95d** (`r10/stmtdiff-vs-f4b2c95d.txt`): docstrings only. These are the 4 Experiments `_def` docstrings; there are no statement changes, additions or removals.

## Process note
I stopped my superseded replay (recorded PID 5311) once you sent the new base. Its command-substitution child (PID 9444, compiling Checks into my own olean tree) was left to finish on its own. I let it exit rather than kill it, then started the new replay. No other processes were touched, and all recorded PIDs have exited.

Evidence is in `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g04r6/` (`r10/` for this round, `at-f4b2c95d/` for the previous head's copies). The diff stat is in `r10/diffstat-vs-base.txt`; it was taken against 8dcdc8a5, the 52-file version above.
