# 137-ladner-common-leaves-gate

The first Codex audit for draft PR #310 (gate 137): Ladner fill 2 (the saturated power and the padding parser) with the shared repeated-squaring round.
Read pack.md (after the standards). Return the findings Markdown in chat.

| File | What |
|---|---|
| `137-ladner-common-leaves-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 1470428 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `e3c2d410e0b3408458ce6217b500d702b11d31484c75f0e4c11ba848ac6c1fd6`
- **Built by** `mkbundle-mixed.py`: the Lean files from `07272ed4d91b22357b5a81a1f65d6787c6210e93`, everything else from the
  campaign commit `9afa8d1ff70bfea584d5b8eded223907db79175d`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Findings:** the auditor delivers `gate137-ladner-common-leaves-findings.md` as an attachment in chat; committed as `campaign/gates/137-ladner-common-leaves/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
