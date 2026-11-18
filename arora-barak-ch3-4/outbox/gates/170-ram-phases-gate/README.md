# 170-ram-phases-gate

The Codex audit for draft PR #386 (gate 170) on the RAM work branch: tier 2 job D, the phase interfaces exists_phase (modulo the 12 row statements of jobs A, B, C) and exists_verdictPhase (no admission), in 25 new Sim/Phase* modules (public in the internal namespace WordRAM.Sim), with three pure readers. Replay 268/268, seals pass, no sweep flag, 93 new copy pairs classified; the PhaseBlock/PhaseBranch duplication is raised for your judgment.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate170-ram-phases-bundle.md` | the bundle to attach: 56 sections (one per file, in `BUNDLE-FILES.txt` order), 7331350 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `bcd907a368255777c7482d639fbcc0662941dd0f229f2ea5eb3db5e6506e3b84`
- **Built by** `mkbundle-mixed.py`: the Lean files from `09546b899d451b693e80588bd625e6b476eb930b`, everything else from the
  campaign commit `e61728742b566bdffe3a711099ecbe052ead7901`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `56 segments, 0 problems`.
- **Export:** only the 56 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate170-ram-phases-findings.md` as an attachment in chat; committed as `campaign/gates/170-ram-phases/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
