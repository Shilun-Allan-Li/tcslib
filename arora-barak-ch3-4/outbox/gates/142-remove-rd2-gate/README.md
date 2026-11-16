# 142-remove-rd2-gate

The first Codex audit for draft PR #328 (gate 142): chapters 3–4 closeout W2, removing the held RD-2/H6 route (`Complexity.ConfigCodec` and the `FormulaKit` modules, 41 admissions), which leaves the chapter scope admission-free.
Read pack.md (after the standards). Deliver the findings as a downloadable file and paste them in chat.

| File | What |
|---|---|
| `gate142-remove-rd2-bundle.md` | the bundle to attach: 18 sections (one per file, in `BUNDLE-FILES.txt` order), 798493 bytes |
| `BUNDLE-FILES.txt` | the section order |
| `SHA256SUMS` | SHA-256 of the bundle and of this README |
| `README.md` | this file |

- **Bundle SHA-256:** `ca96e0cfecac55798a88ee83a50bf888d0b05c0630680fb11ff221a8cadf2e2f`
- **Built by** `mkbundle-mixed.py`: the Lean files from `dcbab37806581f2bd0fd24cb55fee75fcacd2dab`, everything else from the
  campaign commit `fb500567734ab45a53ce916a2b49ad58e7554e45`.
- **Checked by** its `--verify` rebuild, and by `verifybundle.py` against a `git archive` export of
  the two: `18 segments, 0 problems`.
- **Findings:** the auditor delivers `gate142-remove-rd2-findings.md` as an attachment in chat; committed as `campaign/gates/142-remove-rd2/findings.md`.
- **Not yet dispatched.** The prompt to paste is given in chat (no PROMPT.txt).
