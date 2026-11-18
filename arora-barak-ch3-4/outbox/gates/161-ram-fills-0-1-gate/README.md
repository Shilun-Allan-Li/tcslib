# 161-ram-fills-0-1-gate

The Codex audit for draft PR #371 (gate 161) on the RAM work branch, stacked on #370: two Codex fills that prove 21 admissions, tier 0 (the 18 of `Programs/WordRAM/Extended.lean`, the run calculus) and tier 1 (the 3 of `RAMSimulation/WordSize.lean`), plus one maintainer repair at intake. Replay 7/7, seals and controls pass, no sweep flag, 9 copy pairs dispositioned.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate161-ram-fills-0-1-bundle.md` | the bundle to attach: 26 sections (one per file, in `BUNDLE-FILES.txt` order), 1289597 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `7b8bb38e8b61960256d8d69cac63fdc7a99e08d3ecc4b1e9e078fff886b88626`
- **Built by** `mkbundle-mixed.py`: the Lean files from `24aa40503e183a6de58b67dc4d3f7aea08d670b5`, everything else from the
  campaign commit `41a85193893049662cc11961931ea3b004823846`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `26 segments, 0 problems`.
- **Export:** only the 26 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate161-ram-fills-0-1-findings.md` as an attachment in chat; committed as `campaign/gates/161-ram-fills-0-1/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
