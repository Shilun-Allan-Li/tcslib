# 158-w6-final-r2-gate

The second Codex audit for gate 158, the final chapters 3–4 audit (W6). It covers the campaign records together with draft PR #363. Round 1 returned HOLD (one major, eight minors). This round checks the resolutions. Theorem 3.2 now has the book's form for monotone `f`: `ntime_hierarchy_book` and `_of_pos`, two new public theorems. The fidelity table, D3 and the carried register are corrected and reconciled. All 69 lint flags are classified, and the six genuine items and EXPCOM's stale text are repaired. Four touched proofs now cite readers.
Read pack-r2.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate158-w6-final-r2-bundle.md` | the bundle to attach: 194 sections (one per file, in `BUNDLE-FILES.txt` order), 8644048 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `5635620c3eb05442eb22a92ea642443f186af6918cc28c7bb49504f4def84df0`
- **Built by** `mkbundle-mixed.py`: the Lean files from `e88ea45f2baa5b70f2426f6306823f1e39b2ced4`, everything else from the
  campaign commit `e88ea45f2baa5b70f2426f6306823f1e39b2ced4`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `194 segments, 0 problems`.
- **Export note:** the disk allowance did not fit a whole-tree export (4.3 GB), so `verifybundle.py`
  ran on a `git archive` export of exactly the 194 listed paths from the same two commits.
- **Findings:** the auditor delivers `gate158-w6-final-r2-findings.md` as an attachment in chat; committed as `campaign/gates/158-w6-final/findings-r2.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
