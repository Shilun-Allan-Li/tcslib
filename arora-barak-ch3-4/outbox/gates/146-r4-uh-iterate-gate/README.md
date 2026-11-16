# 146-r4-uh-iterate-gate

The first Codex audit for draft PR #335 (gate 146), stacked on PR #334 (gate 145): chapters 3–4 closeout, wave R4, item SG1-UH. It deletes Hardness's private unary-clock repetition host by proving `clA5Iter_native` through the public `BinArith.polyTimeComputable_iterate` (net −297 lines, no new API).
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate146-r4-uh-iterate-bundle.md` | the bundle to attach: 18 sections (one per file, in `BUNDLE-FILES.txt` order), 1850309 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `3b952f24645df952a01df3be3896ff6e6a6c6619ec6568e0ec85c207b9160576`
- **Built by** `mkbundle-mixed.py`: the Lean files from `2dc0fc307ce90b5ae5b56da79b7345c4367183da`, everything else from the
  campaign commit `967cde57f5cd0a44af861feb518907a279c53a82`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `18 segments, 0 problems`.
- **Findings:** the auditor delivers `gate146-r4-uh-iterate-findings.md` as an attachment in chat; committed as `campaign/gates/146/findings-iterate.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
