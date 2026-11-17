# 160-ram-readers-r2-gate

The second Codex audit for draft PR #370 (gate 160) on the RAM work branch. Round 1 returned HOLD (one major, one minor). This round checks the corrected tier 3 brief and dependency inventory, the repaired docstrings, and four new readers for the vendored run calculus (`Programs/WordRAM/Steps.lean`) that tier 0 needs. Replay 280/280, seals and controls pass, no sweep flag.
Read pack-r2.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate160-ram-readers-r2-bundle.md` | the bundle to attach: 28 sections (one per file, in `BUNDLE-FILES.txt` order), 8688925 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `e9a79683a6d498345d051a20c07dba250023dba10674a3850593af444808bf15`
- **Built by** `mkbundle-mixed.py`: the Lean files from `25040f435bba85ad563d5c1f1ceb42744aefc3eb`, everything else from the
  campaign commit `f827aaec99c5b141bbaac15891617c15c532171d`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `28 segments, 0 problems`.
- **Export:** only the 28 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate160-ram-readers-r2-findings.md` as an attachment in chat; committed as `campaign/gates/160-ram-readers/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
