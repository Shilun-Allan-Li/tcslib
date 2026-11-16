# 151-c1e-1-trims-gate

The first Codex audit for draft PR #344 (gate 151): chapters 3–4 closeout, wave R3, family C1E-1 trims in `ClassNP/ExhaustiveReplay`. Two buffer-tape privates give way to `FinTM.bufferTape_of_neg`/`bufferTape_eq`, the replay's two exits share one prelude lemma, and ten bank-inequality lemmas become a file-local tactic (net −38 lines, no statement changes).
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate151-c1e-1-trims-bundle.md` | the bundle to attach: 19 sections (one per file, in `BUNDLE-FILES.txt` order), 1660288 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `6d1bbe3f738288c76a8bbfe136b43d30c593ce13d0f1cc037610d028a70f9781`
- **Built by** `mkbundle-mixed.py`: the Lean files from `974599a43484632ba38ab4dec4196790a6d0cb46`, everything else from the
  campaign commit `37adee51b80d2789dd1c930de2c95f70562fa29e`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `19 segments, 0 problems`.
- **Findings:** the auditor delivers `gate151-c1e-1-trims-findings.md` as an attachment in chat; committed as `campaign/gates/151-c1e-1-trims/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
