# 163-ram-fill-classes-gate

The Codex audit for draft PR #373 (gate 163) on the RAM work branch: the Codex fill that proves the nine class corollaries of `RAMSimulation/Classes.lean` (tier 3), landed unchanged. Replay 2/2, seals and controls pass, no sweep flag, 3 copy pairs dispositioned; each corollary reaches only the tier 2 admission it should. Every citation home is bundled.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate163-ram-fill-classes-bundle.md` | the bundle to attach: 31 sections (one per file, in `BUNDLE-FILES.txt` order), 798428 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `f92cc25cb15165a58989d71836388998e7222924ce7f777efd0271b8c8dca1c8`
- **Built by** `mkbundle-mixed.py`: the Lean files from `1ababb822cd0aff5fa841239e140f0fb60a77f48`, everything else from the
  campaign commit `bcbbef2129d2105cef9d63441e747e80c8e60aef`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `31 segments, 0 problems`.
- **Export:** only the 31 listed paths, from the same two commits.
- **Findings:** the auditor delivers `gate163-ram-fill-classes-findings.md` as an attachment in chat; committed as `campaign/gates/163-ram-fill-classes/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
